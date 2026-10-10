// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// FC_MA_EX -- execution pipelines: the two ALU pipelines, the mult/div/CHERI
// pipeline, the complex (AMO) unit, and the branch unit.
//
// All four bind targets contribute coverpoints to the single FC_MA_EX group
// because they are one functional block from the plan's point of view: the
// per-slot execution resources the issuer arbitrates over.
//
// Bound to rtl/alu_pipeline.sv, rtl/branch_unit.sv, rtl/mult_pipeline.sv,
// rtl/cmplx_unit.sv.
// See doc/functional_coverage_plan.md section 11.
// ===========================================================================
// ALU pipeline (instantiated twice: alu_pipeline0_i / alu_pipeline1_i)
// ===========================================================================
module kudu_fcov_alu
  import super_pkg::*;
  import kudu_fcov_pkg::*;
#(
  parameter string PlName = "alu0",
  parameter bit SingleStage = 1,
  parameter bit CHERIoTEn = 1
) (
  input logic       clk_i,
  input logic       rst_ni,

  input logic       us_valid_i,
  input logic       alupl_rdy_o,
  input logic       ds_rdy_i,
  input logic       alupl_valid_o,
  input logic       flush_i,

  input ir_dec_t    instr_i,
  input pl_out_t    alupl_output_o,

  input alu_op_e    rv32_alu_operator,
  input op_a_sel_e  rv32_alu_op_a_mux_sel,
  input op_b_sel_e  rv32_alu_op_b_mux_sel,

  input logic       cycle2,
  input logic       instr_2cycle,
  input logic       ex1_is_cheri,
  input logic       ex2_valid,
  input logic       ex2_rdy,
  input logic       wb_valid,
  input logic       wb_rdy,
  input logic       ex2_waw_match,
  input logic       wb_waw_match,
  input logic       ex2_fwd_valid_q,
  input logic       wb_fwd_valid_q,
  input logic [4:0] ex2_fwd_rd,
  input waw_act_t   waw_act_i,
  input logic       debug_mode_i
);

`ifndef KUDU_FCOV_OFF

  wire cheri_active = CHERIoTEn && alu_pipeline.cheri_pmode_i;

  // ALU stage registers retain PC/result metadata but not the instruction.
  // Keep only its category, using the RTL's existing stage enables/valids.
  kudu_instr_cat_e ex2_category, wb_category;
  if (SingleStage) begin : gen_category_bypass
    assign ex2_category = fcov_instr_cat(instr_i);
  end else begin : gen_category_ex2
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) ex2_category <= IC_ALU_RI;
      else if (!flush_i && ex2_rdy) ex2_category <= fcov_instr_cat(instr_i);
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) wb_category <= IC_ALU_RI;
    else if (!flush_i && wb_rdy) wb_category <= ex2_category;
  end

  covergroup cg_ma_alu @(posedge clk_i iff rst_ni);
    option.per_instance = 1;
    option.name         = {"FC_MA_EX.", PlName};

    // alu_op_e is a lossy projection of the ISA (several distinct instructions
    // share one operator), which is exactly why this is FC_MA and the ISA-level
    // encoding coverage lives in FC_ISA_INSTR.
    cp_alu_op:   coverpoint rv32_alu_operator iff (us_valid_i);
    cp_op_a_sel: coverpoint rv32_alu_op_a_mux_sel iff (us_valid_i) {
      bins reg_a = {OP_A_REG_A};
      bins currpc = {OP_A_CURRPC};
      bins imm = {OP_A_IMM};
    }
    cp_op_b_sel: coverpoint rv32_alu_op_b_mux_sel iff (us_valid_i);

    // rv32_alu chooses the subtraction sign for equal operand signs, but
    // chooses operand_a's sign XOR signedness when their signs differ.
    cp_compare_path: coverpoint {
        alu_pipeline.rv32_alu_i.cmp_signed,
        (alu_pipeline.rv32_alu_i.operand_a[31] ^
         alu_pipeline.rv32_alu_i.operand_b[31]),
        alu_pipeline.rv32_alu_i.is_greater_equal}
        iff (us_valid_i && alupl_rdy_o && !flush_i && !ex1_is_cheri &&
             rv32_alu_operator inside {ALU_SLT, ALU_SLTU}) {
      bins unsigned_same_lt = {3'b000};
      bins unsigned_same_ge = {3'b001};
      bins unsigned_diff_lt = {3'b010};
      bins unsigned_diff_ge = {3'b011};
      bins signed_same_lt = {3'b100};
      bins signed_same_ge = {3'b101};
      bins signed_diff_lt = {3'b110};
      bins signed_diff_ge = {3'b111};
    }
    cp_shift_amount: coverpoint alu_pipeline.rv32_alu_i.shift_amt
        iff (us_valid_i && alupl_rdy_o && !flush_i && !ex1_is_cheri &&
             rv32_alu_operator inside {ALU_SLL, ALU_SRL, ALU_SRA}) {
      bins zero = {0};
      bins one = {1};
      bins middle = {[2:30]};
      bins maximum = {31};
    }
    cp_shift_rotate_op: coverpoint rv32_alu_operator
        iff (us_valid_i && alupl_rdy_o && !flush_i && !ex1_is_cheri &&
             rv32_alu_operator inside {ALU_SLL, ALU_SRL, ALU_SRA, ALU_ROL, ALU_ROR}) {
      bins sll = {ALU_SLL};
      bins srl = {ALU_SRL};
      bins sra = {ALU_SRA};
      bins rol = {ALU_ROL};
      bins ror = {ALU_ROR};
    }
    cp_shift_rotate_amount: coverpoint alu_pipeline.rv32_alu_i.shift_amt
        iff (us_valid_i && alupl_rdy_o && !flush_i && !ex1_is_cheri &&
             rv32_alu_operator inside {ALU_SLL, ALU_SRL, ALU_SRA, ALU_ROL, ALU_ROR}) {
      bins zero = {0};
      bins one = {1};
      bins middle = {[2:30]};
      bins maximum = {31};
    }
    cp_shift_operand_form: coverpoint rv32_alu_op_b_mux_sel
        iff (us_valid_i && alupl_rdy_o && !flush_i && !ex1_is_cheri &&
             rv32_alu_operator inside {ALU_SLL, ALU_SRL, ALU_SRA, ALU_ROL, ALU_ROR}) {
      bins rs2 = {OP_B_REG_B};
      bins imm = {OP_B_IMM};
    }
    cp_sra_negative_operand: coverpoint alu_pipeline.rv32_alu_i.operand_a[31]
        iff (us_valid_i && alupl_rdy_o && !flush_i && !ex1_is_cheri &&
             rv32_alu_operator == ALU_SRA) {
      bins positive = {1'b0};
      bins negative = {1'b1};
    }

    cp_is_cheri: coverpoint ex1_is_cheri
        iff (cheri_active && us_valid_i) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins capability[] = {[0:CHERIoTEn]};
    }

    // Handshakes.  Backpressure on this pipeline is what makes the issuer
    // arbitration interesting, so accept/stall must be seen at both ends.
    cp_us: coverpoint {us_valid_i, alupl_rdy_o} {
      bins idle       = {2'b00};
      bins rdy_no_req = {2'b01};
      bins stalled    = {2'b10};
      bins accepted   = {2'b11};
    }
    cp_ds: coverpoint {alupl_valid_o, ds_rdy_i} {
      bins idle       = {2'b00};
      bins rdy_no_out = {2'b01};
      bins stalled    = {2'b10};
      bins committed  = {2'b11};
    }

    cp_wb: coverpoint {wb_valid, wb_rdy} {
      bins idle     = {2'b00};
      bins ready    = {2'b01};
      bins stalled  = {2'b10};
      bins advanced = {2'b11};
    }
    cp_flush: coverpoint flush_i { bins hit = {1'b1}; }
    // Flushing while there is live state in the pipeline is the case that can
    // leave a stale forwarding entry behind.
    cp_flush_busy: coverpoint (flush_i & wb_valid) { bins hit = {1'b1}; }

    // WAW cancellation: a younger write to the same register retires first, so
    // this result must be dropped.
    cp_waw_act:       coverpoint waw_act_i.valid {
      bins none = {2'b00};
      bins v0   = {2'b01};
      bins v1   = {2'b10};
      bins both = {2'b11};
    }
    cp_wb_waw_match:  coverpoint wb_waw_match  { bins hit = {1'b1}; }

    cp_fwd: coverpoint wb_fwd_valid_q {
      bins source[] = {[1'b0:1'b1]};
    }

    // An error is an invariant violation, not a coverage closure target.
    cp_out_err: coverpoint alupl_output_o.err iff (alupl_valid_o) {
      bins no_err = {1'b0};
      illegal_bins err = {1'b1};
    }
    cp_out_we: coverpoint alupl_output_o.we iff (alupl_valid_o) {
      ignore_bins no_write = {1'b0};
    }
    cp_out_wrsv:   coverpoint alupl_output_o.wrsv   iff (alupl_valid_o);

    cp_debug_mode: coverpoint debug_mode_i;

    x_shift_op_amount: cross cp_shift_rotate_op, cp_shift_rotate_amount;
    x_shift_op_form: cross cp_shift_rotate_op, cp_shift_operand_form {
      // Zbb has rori but no immediate rol.
      ignore_bins no_rol_imm = binsof(cp_shift_rotate_op.rol) && binsof(cp_shift_operand_form.imm);
    }
  endgroup

  cg_ma_alu u_cg_alu = new();

  AssertNoAluErr: assert property (
    @(posedge clk_i) disable iff (!rst_ni) alupl_valid_o |-> !alupl_output_o.err)
    else $error("FCOV: alu_pipeline raised .err; committer error capture (F-03) is unsafe");

`endif  // KUDU_FCOV_OFF

endmodule


// ===========================================================================
// Branch unit (one instance, kudu_top.branch_unit_i)
// ===========================================================================
// Groups are per logical issue slot (IR0/IR1); the issuer supplies the
// evaluation qualifier and issue status hierarchically.
module kudu_fcov_branch_unit
  import super_pkg::*;
  import kudu_fcov_pkg::*;
#(
  parameter bit CHERIoTEn        = 1'b1,
  parameter bit ChkBranchJALAddr = 1'b1
) (
  input logic         clk_i,
  input logic         rst_ni,

  input logic         cheri_pmode_i,
  input logic         debug_mode_i,
  input ir_dec_t      ira_dec_i,
  input ir_dec_t      irb_dec_i,
  input logic         ira_is0_i,
  input full_data2_t  ira_full_data2_i,
  input full_data2_t  irb_full_data2_i,
  input branch_info_t branch_info_o,
  input logic [31:0]  ir0_jalr_target_o,
  input logic [31:0]  ir1_jalr_target_o,
  input logic [2:0]   ir0_cjalr_err_o,
  input logic [2:0]   ir1_cjalr_err_o
);

`ifndef KUDU_FCOV_OFF

  for (genvar Slot = 0; Slot < 2; Slot++) begin : gen_slot
    ir_dec_t dec;
    full_data2_t resolved_data;
    logic eval_valid, issued, taken;
    logic [3:0] mispredict;
    logic [31:0] jalr_target;
    logic [2:0] cjalr_errors;
    wire cjalr_active = CHERIoTEn && cheri_pmode_i;

    // Inputs are physical A/B; branch-unit outputs are ordered IR0/IR1.
    assign dec = ((Slot == 0) == ira_is0_i) ? ira_dec_i : irb_dec_i;
    assign resolved_data = ((Slot == 0) == ira_is0_i) ? ira_full_data2_i : irb_full_data2_i;
    assign eval_valid = kudu_top.issuer_i.ctrl_fsm_cs[CSM_DECODE] &&
        kudu_top.issuer_i.ir_valid_i[Slot] && !kudu_top.issuer_i.ir_hazard[Slot] &&
        !kudu_top.issuer_i.cmt_err_i && !dec.any_err &&
        (dec.is_branch || dec.is_jal || dec.is_jalr);
    assign issued = Slot == 0 ? kudu_top.issuer_i.ir0_issued : kudu_top.issuer_i.ir1_issued;
    assign taken = branch_info_o.branch_taken[Slot];
    assign mispredict = {
        branch_info_o.mis_jalr[Slot],
        branch_info_o.mis_jal[Slot],
        branch_info_o.mis_not_taken[Slot],
        branch_info_o.mis_taken[Slot]};
    assign jalr_target = Slot == 0 ? ir0_jalr_target_o : ir1_jalr_target_o;
    assign cjalr_errors = Slot == 0 ? ir0_cjalr_err_o : ir1_cjalr_err_o;

    // Evaluate rather than require issue: a CJALR fault prevents issue.
    covergroup cg_ma_branch @(posedge clk_i iff (rst_ni && eval_valid));
      option.per_instance = 1;
      option.name = Slot == 0 ? "FC_MA_EX.branch.ir0" : "FC_MA_EX.branch.ir1";

      cp_kind: coverpoint {dec.is_jalr, dec.is_jal, dec.is_branch} {
        bins branch = {3'b001};
        bins jal = {3'b010};
        bins jalr = {3'b100};
      }
      cp_mapping: coverpoint ira_is0_i;
      cp_issued: coverpoint issued;

      cp_branch_outcome: coverpoint {dec.insn[14:12], taken} iff (dec.is_branch) {
        bins beq[]  = {[4'h0:4'h1]};
        bins bne[]  = {[4'h2:4'h3]};
        bins blt[]  = {[4'h8:4'h9]};
        bins bge[]  = {[4'ha:4'hb]};
        bins bltu[] = {[4'hc:4'hd]};
        bins bgeu[] = {[4'he:4'hf]};
      }
      cp_compare_operands: coverpoint {
          resolved_data.d0[31], resolved_data.d1[31],
          (resolved_data.d0[31:0] == resolved_data.d1[31:0])}
          iff (dec.is_branch) {
        bins positive_different = {3'b000};
        bins positive_equal = {3'b001};
        bins positive_negative = {3'b010};
        bins negative_positive = {3'b100};
        bins negative_different = {3'b110};
        bins negative_equal = {3'b111};
      }
      cp_branch_direction: coverpoint {
          branch_info_o.is_fwd[Slot], taken}
          iff (dec.is_branch) {
        bins backward_not_taken = {2'b00};
        bins backward_taken = {2'b01};
        bins forward_not_taken = {2'b10};
        bins forward_taken = {2'b11};
      }
      cp_branch_prediction: coverpoint {dec.ptaken, taken} iff (dec.is_branch) {
        bins correct_not_taken = {2'b00};
        bins missed_taken = {2'b01};
        bins missed_not_taken = {2'b10};
        bins correct_taken_direction = {2'b11};
      }
      cp_mispredict: coverpoint mispredict {
        // Four independent output flags, not a scalar "any miss".
        bins cause[] = {4'd0, 4'd1, 4'd2, 4'd4, 4'd8}
          with (item != 4 || ChkBranchJALAddr);
      }
      cp_jalr_prediction: coverpoint {dec.ptaken, mispredict[3]} iff (dec.is_jalr) {
        bins not_predicted = {2'b01};
        bins correct = {2'b10};
        bins wrong_target = {2'b11};
      }
      // This block produces the raw sum, before any downstream bit-0 masking.
      cp_jalr_target_low: coverpoint jalr_target[1:0] iff (dec.is_jalr) {
        bins low_bits[] = {[2'd0:2'd3]};
      }
      cp_jalr_immediate: coverpoint dec.insn[31:20] iff (dec.is_jalr) {
        bins zero = {12'h000};
        bins positive = {[12'h001:12'h7ff]};
        bins negative = {[12'h800:12'hffe]};
        bins minus_one = {12'hfff};
      }
      cp_cjalr_errors: coverpoint cjalr_errors
          iff (cjalr_active && dec.is_jalr) {
        option.weight = CHERIoTEn ? 1 : 0;
        // {execute permission, sealing rules, tag}; combinations are legal.
        bins mask[] = {[3'd0:3'd7]} with (CHERIoTEn || item == 0);
      }
    endgroup

    cg_ma_branch u_cg_branch = new();
  end

`endif  // KUDU_FCOV_OFF

endmodule


// ===========================================================================
// Mult / div / CHERI pipeline
// ===========================================================================
module kudu_fcov_mult
  import cheri_pkg::*;
  import super_pkg::*;
  import kudu_fcov_pkg::*;
#(
  parameter bit CHERIoTEn = 1
) (
  input logic       clk_i,
  input logic       rst_ni,

  input logic       us_valid_i,
  input logic       multpl_rdy_o,
  input logic       ds_rdy_i,
  input logic       multpl_valid_o,
  input logic       flush_i,
  input logic       sel_ira_i,
  input cpu_ctrl_t  cpu_ctrl_i,

  input pl_out_t    multpl_output_o,

  input md_op_e     md_operator,
  input logic [1:0] md_signed_mode,
  input logic       md_mult_en,
  input logic       md_div_en,
  input logic       md_mult_valid,
  input logic       md_div_valid,
  input logic       mult_sel,
  input logic       div_sel,
  input logic       is_mult,
  input logic       is_div,
  input logic       div_done_q,
  input logic       op_done,

  input logic       ex1_is_cjalr,
  input logic [1:0] mis_jalr_i,
  input logic       cjalr_pcc_set_o,
  input logic       cjalr_set_mie_o,
  input logic       cjalr_clr_mie_o,

  input logic       ex2_valid,
  input logic       ex2_rdy,
  input logic       wb_valid,
  input logic       wb_rdy,
  input logic       ex2_err,
  input logic [5:0] ex2_err_type,
  input logic       ex2_waw_match,
  input logic       wb_waw_match,
  input waw_act_t   waw_act_i,

  input ir_dec_t    ira_dec_i,
  input ir_dec_t    irb_dec_i
);

`ifndef KUDU_FCOV_OFF

  ir_dec_t sel_dec;
  wire cheri_active = CHERIoTEn && mult_pipeline.cheri_pmode_i;
  assign sel_dec = sel_ira_i ? ira_dec_i : irb_dec_i;

  typedef enum logic [2:0] {
    FCOV_MD_MULH, FCOV_MD_MULHSU, FCOV_MD_MULHU,
    FCOV_MD_DIV, FCOV_MD_DIVU, FCOV_MD_REM, FCOV_MD_REMU
  } fcov_md_insn_e;

  typedef enum logic [1:0] {
    FCOV_DIVISOR_ZERO, FCOV_DIVISOR_ONE, FCOV_DIVISOR_MINUS_ONE, FCOV_DIVISOR_OTHER
  } fcov_divisor_class_e;

  typedef enum logic [1:0] {
    FCOV_DIVIDEND_ZERO, FCOV_DIVIDEND_MIN, FCOV_DIVIDEND_POS, FCOV_DIVIDEND_NEG
  } fcov_dividend_class_e;

  typedef enum logic [2:0] {
    FCOV_MULOP_ZERO, FCOV_MULOP_ONE, FCOV_MULOP_POS,
    FCOV_MULOP_NEG, FCOV_MULOP_MIN, FCOV_MULOP_MINUS_ONE
  } fcov_mul_operand_class_e;

  typedef enum logic {
    FCOV_DIV_COMPLETE_EARLY, FCOV_DIV_COMPLETE_FULL
  } fcov_div_completion_e;

  typedef enum logic [2:0] {
    FCOV_SB_SETBOUNDS, FCOV_SB_SETBOUNDSEXACT, FCOV_SB_SETBOUNDSIMM,
    FCOV_SB_ROUNDDOWN, FCOV_SB_OTHER
  } fcov_setbounds_op_e;

  typedef enum logic [1:0] {
    FCOV_SB_OK, FCOV_SB_EXACT_INEXACT, FCOV_SB_OUT_OF_BOUNDS, FCOV_SB_SEALED_UNTAGGED
  } fcov_setbounds_reason_e;

  typedef enum logic [1:0] {
    FCOV_SB_EXACT_REP, FCOV_SB_TOP_ROUNDED, FCOV_SB_BASE_ROUNDED, FCOV_SB_TOP_BASE_ROUNDED
  } fcov_setbounds_round_e;

  typedef enum logic [1:0] {
    FCOV_SB_PATH_NORMAL, FCOV_SB_PATH_OVERFLOW_SECOND,
    FCOV_SB_PATH_RNDN_EXPLEN_GT_EXPB, FCOV_SB_PATH_RNDN_EXPLEN_LE_EXPB
  } fcov_setbounds_path_e;

  fcov_md_insn_e div_insn_q;
  logic          ex2_cheri_mode_q;
  logic          div_early_q;

  function automatic fcov_md_insn_e fcov_md_insn(md_op_e op, logic [1:0] sign);
    if (op == MD_OP_DIV) return sign == 2'b11 ? FCOV_MD_DIV : FCOV_MD_DIVU;
    if (op == MD_OP_REM) return sign == 2'b11 ? FCOV_MD_REM : FCOV_MD_REMU;
    if (sign == 2'b11) return FCOV_MD_MULH;
    if (sign == 2'b01) return FCOV_MD_MULHSU;
    return FCOV_MD_MULHU;
  endfunction

  function automatic fcov_divisor_class_e fcov_divisor_class(logic [31:0] v);
    if (v == 32'h0) return FCOV_DIVISOR_ZERO;
    if (v == 32'h1) return FCOV_DIVISOR_ONE;
    if (v == 32'hffff_ffff) return FCOV_DIVISOR_MINUS_ONE;
    return FCOV_DIVISOR_OTHER;
  endfunction

  function automatic fcov_dividend_class_e fcov_dividend_class(logic [31:0] v);
    if (v == 32'h0) return FCOV_DIVIDEND_ZERO;
    if (v == 32'h8000_0000) return FCOV_DIVIDEND_MIN;
    if (v[31]) return FCOV_DIVIDEND_NEG;
    return FCOV_DIVIDEND_POS;
  endfunction

  function automatic fcov_mul_operand_class_e fcov_mul_operand_class(logic [31:0] v);
    if (v == 32'h0) return FCOV_MULOP_ZERO;
    if (v == 32'h1) return FCOV_MULOP_ONE;
    if (v == 32'h8000_0000) return FCOV_MULOP_MIN;
    if (v == 32'hffff_ffff) return FCOV_MULOP_MINUS_ONE;
    if (v[31]) return FCOV_MULOP_NEG;
    return FCOV_MULOP_POS;
  endfunction

  function automatic fcov_setbounds_op_e fcov_setbounds_op();
    cheri_op_t cheri_op;
    cheri_op = mult_pipeline.ex2_reg.cheri_op;
    if (cheri_op.csetbounds) return FCOV_SB_SETBOUNDS;
    if (cheri_op.csetboundsex) return FCOV_SB_SETBOUNDSEXACT;
    if (cheri_op.csetboundsimm) return FCOV_SB_SETBOUNDSIMM;
    if (cheri_op.csetboundsrndn) return FCOV_SB_ROUNDDOWN;
    return FCOV_SB_OTHER;
  endfunction

  function automatic logic fcov_setbounds_overflow();
    logic [32:0] mask1;
    logic [BOT_W:0] base1, top1, len1;
    logic topoff1;

    mask1   = {33{1'b1}} << mult_pipeline.setbounds_req_q.exp1;
    base1   = (BOT_W+1)'(mult_pipeline.ex1_tfcap_q.addr >> mult_pipeline.setbounds_req_q.exp1);
    topoff1 = |(mult_pipeline.setbounds_req_q.top33req & ~mask1);
    top1    = (BOT_W+1)'(mult_pipeline.setbounds_req_q.top33req >>
                         mult_pipeline.setbounds_req_q.exp1) + (BOT_W+1)'(topoff1);
    len1    = top1 - base1;
    return len1[9];
  endfunction

  function automatic fcov_setbounds_round_e fcov_setbounds_rounding();
    logic [4:0] exp_sel;
    logic [32:0] mask;
    logic topoff, baseoff;

    exp_sel = fcov_setbounds_overflow() ? mult_pipeline.setbounds_req_q.exp2 :
                                          mult_pipeline.setbounds_req_q.exp1;
    if (fcov_setbounds_op() == FCOV_SB_ROUNDDOWN)
      exp_sel = (mult_pipeline.setbounds_req_q.explen > mult_pipeline.setbounds_req_q.expb) ?
                mult_pipeline.setbounds_req_q.expb[4:0] : mult_pipeline.setbounds_req_q.explen[4:0];
    mask    = {33{1'b1}} << exp_sel;
    topoff  = |(mult_pipeline.setbounds_req_q.top33req & ~mask);
    baseoff = |({1'b0, mult_pipeline.ex1_tfcap_q.addr} & ~mask);
    if (topoff && baseoff) return FCOV_SB_TOP_BASE_ROUNDED;
    if (topoff) return FCOV_SB_TOP_ROUNDED;
    if (baseoff) return FCOV_SB_BASE_ROUNDED;
    return FCOV_SB_EXACT_REP;
  endfunction

  function automatic fcov_setbounds_reason_e fcov_setbounds_reason();
    logic in_bound;

    in_bound = ~((mult_pipeline.setbounds_req_q.top33req > mult_pipeline.ex1_tfcap_q.top33) ||
                 (mult_pipeline.ex1_tfcap_q.addr < mult_pipeline.ex1_tfcap_q.base32));
    if (!mult_pipeline.ex1_tfcap_q.valid || (mult_pipeline.ex1_tfcap_q.otype != OTYPE_UNSEALED))
      return FCOV_SB_SEALED_UNTAGGED;
    if (!in_bound) return FCOV_SB_OUT_OF_BOUNDS;
    if (mult_pipeline.req_exact_q && (fcov_setbounds_rounding() != FCOV_SB_EXACT_REP))
      return FCOV_SB_EXACT_INEXACT;
    return FCOV_SB_OK;
  endfunction

  function automatic fcov_setbounds_path_e fcov_setbounds_path();
    if (fcov_setbounds_op() == FCOV_SB_ROUNDDOWN)
      return (mult_pipeline.setbounds_req_q.explen > mult_pipeline.setbounds_req_q.expb) ?
             FCOV_SB_PATH_RNDN_EXPLEN_GT_EXPB : FCOV_SB_PATH_RNDN_EXPLEN_LE_EXPB;
    return fcov_setbounds_overflow() ? FCOV_SB_PATH_OVERFLOW_SECOND : FCOV_SB_PATH_NORMAL;
  endfunction

  function automatic logic [32:0] fcov_setbounds_req_len();
    return mult_pipeline.setbounds_req_q.top33req - {1'b0, mult_pipeline.ex1_tfcap_q.addr};
  endfunction

  // Instruction class occupying the mult pipeline. CRRL/CRAM also use this
  // pipeline but are not occupancy goals (FCOV_MP_OTHER is never binned).
  typedef enum logic [2:0] {
    FCOV_MP_MULT, FCOV_MP_DIV, FCOV_MP_SETBOUNDS, FCOV_MP_CJALR, FCOV_MP_OTHER
  } fcov_mp_class_e;

  function automatic fcov_mp_class_e fcov_mp_class(logic is_cjalr, logic is_mult,
                                                   logic is_div, cheri_op_t cheri_op);
    if (is_cjalr) return FCOV_MP_CJALR;
    if (is_mult)  return FCOV_MP_MULT;
    if (is_div)   return FCOV_MP_DIV;
    if (cheri_op.csetbounds || cheri_op.csetboundsex || cheri_op.csetboundsimm ||
        cheri_op.csetboundsrndn) return FCOV_MP_SETBOUNDS;
    return FCOV_MP_OTHER;
  endfunction

  fcov_mp_class_e ex2_mp_class, us_mp_class;
  assign ex2_mp_class = fcov_mp_class(mult_pipeline.ex2_reg.flags.is_cjalr,
                                      mult_pipeline.ex2_reg.flags.is_mult,
                                      mult_pipeline.ex2_reg.flags.is_div,
                                      mult_pipeline.ex2_reg.cheri_op);
  assign us_mp_class  = fcov_mp_class(ex1_is_cjalr, mult_sel, div_sel,
                                      mult_pipeline.instr_dec.cheri_op);

  wire setbounds_sample = CHERIoTEn && ex2_cheri_mode_q && ex2_valid && op_done &&
      (fcov_setbounds_op() != FCOV_SB_OTHER);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      div_insn_q <= FCOV_MD_DIV;
      div_early_q <= 1'b0;
      ex2_cheri_mode_q <= 1'b0;
    end else begin
      if (md_div_en) begin
        div_insn_q <= fcov_md_insn(md_operator, md_signed_mode);
        div_early_q <= (mult_pipeline.md_op_b == 32'h0) && !cpu_ctrl_i.data_ind_timing;
      end
      if (flush_i) ex2_cheri_mode_q <= 1'b0;
      else if (ex2_rdy) ex2_cheri_mode_q <= cheri_active;
    end
  end

  covergroup cg_ma_mult @(posedge clk_i iff rst_ni);
    option.per_instance = 1;
    option.name         = "FC_MA_EX.mult";

    // md_op_e has only four values; signedness is carried separately in
    // md_signed_mode, so MULHSU/MULHU/MULH all appear as MD_OP_MULH here and
    // only the pair distinguishes them.
    cp_md_op:     coverpoint md_operator iff (md_mult_en | md_div_en);
    cp_md_signed: coverpoint md_signed_mode iff (md_mult_en | md_div_en) {
      bins uu = {2'b00};
      bins su = {2'b01};
      ignore_bins unused_us = {2'b10};
      bins ss = {2'b11};
    }

    cp_is_mult: coverpoint is_mult iff (ex2_valid);
    cp_is_div:  coverpoint is_div  iff (ex2_valid);
    cp_mult_sel: coverpoint mult_sel;
    cp_div_sel:  coverpoint div_sel;
    cp_md_valid: coverpoint {md_div_valid, md_mult_valid} {
      bins none = {2'b00};
      bins mult = {2'b01};
      bins div  = {2'b10};
      illegal_bins both = {2'b11};
    }
    cp_div_done: coverpoint div_done_q { bins hit = {1'b1}; }
    cp_op_done:  coverpoint op_done    { bins hit = {1'b1}; }

    // Data-independent timing forces the divider to a fixed latency; both
    // settings have to be exercised or the constant-time mode is untested.
    cp_ind_timing: coverpoint cpu_ctrl_i.data_ind_timing;

    // A divide in flight while a new instruction is offered is the multi-cycle
    // backpressure case that stalls issue.
    cp_div_busy_stall: coverpoint (md_div_en & us_valid_i & ~multpl_rdy_o) {
      bins hit = {1'b1};
    }

    cp_div_op_sem: coverpoint fcov_md_insn(md_operator, md_signed_mode)
        iff (md_div_en) {
      bins div  = {FCOV_MD_DIV};
      bins divu = {FCOV_MD_DIVU};
      bins rem  = {FCOV_MD_REM};
      bins remu = {FCOV_MD_REMU};
    }
    cp_divisor_class: coverpoint fcov_divisor_class(mult_pipeline.md_op_b)
        iff (md_div_en) {
      bins zero = {FCOV_DIVISOR_ZERO};
      bins one = {FCOV_DIVISOR_ONE};
      bins minus_one = {FCOV_DIVISOR_MINUS_ONE};
      bins other = {FCOV_DIVISOR_OTHER};
    }
    cp_dividend_class: coverpoint fcov_dividend_class(mult_pipeline.md_op_a)
        iff (md_div_en) {
      bins zero = {FCOV_DIVIDEND_ZERO};
      bins int_min = {FCOV_DIVIDEND_MIN};
      bins positive = {FCOV_DIVIDEND_POS};
      bins negative = {FCOV_DIVIDEND_NEG};
    }
    cp_signed_div_overflow: coverpoint
        (mult_pipeline.md_op_a == 32'h8000_0000 && mult_pipeline.md_op_b == 32'hffff_ffff)
        iff (md_div_en && md_signed_mode == 2'b11) {
      bins other = {1'b0};
      bins int_min_div_minus_one = {1'b1};
    }
    cp_signed_div_signs: coverpoint {mult_pipeline.md_op_a[31], mult_pipeline.md_op_b[31]}
        iff (md_div_en && md_signed_mode == 2'b11) {
      bins pos_pos = {2'b00};
      bins pos_neg = {2'b01};
      bins neg_pos = {2'b10};
      bins neg_neg = {2'b11};
    }
    cp_div_completion_path: coverpoint (div_early_q ? FCOV_DIV_COMPLETE_EARLY :
                                                      FCOV_DIV_COMPLETE_FULL)
        iff (md_div_valid) {
      bins early = {FCOV_DIV_COMPLETE_EARLY};
      bins full_iteration = {FCOV_DIV_COMPLETE_FULL};
    }
    cp_div_complete_op: coverpoint div_insn_q iff (md_div_valid) {
      bins div  = {FCOV_MD_DIV};
      bins divu = {FCOV_MD_DIVU};
      bins rem  = {FCOV_MD_REM};
      bins remu = {FCOV_MD_REMU};
    }
    cp_mulh_op_sem: coverpoint fcov_md_insn(md_operator, md_signed_mode)
        iff (md_mult_en && md_operator == MD_OP_MULH) {
      bins mulh = {FCOV_MD_MULH};
      bins mulhsu = {FCOV_MD_MULHSU};
      bins mulhu = {FCOV_MD_MULHU};
    }
    cp_mulh_operand_a_class: coverpoint fcov_mul_operand_class(mult_pipeline.md_op_a)
        iff (md_mult_en && md_operator == MD_OP_MULH) {
      bins zero = {FCOV_MULOP_ZERO};
      bins one = {FCOV_MULOP_ONE};
      bins positive = {FCOV_MULOP_POS};
      bins negative = {FCOV_MULOP_NEG};
      bins int_min = {FCOV_MULOP_MIN};
      bins minus_one = {FCOV_MULOP_MINUS_ONE};
    }
    cp_mulh_operand_b_class: coverpoint fcov_mul_operand_class(mult_pipeline.md_op_b)
        iff (md_mult_en && md_operator == MD_OP_MULH) {
      bins zero = {FCOV_MULOP_ZERO};
      bins one = {FCOV_MULOP_ONE};
      bins positive = {FCOV_MULOP_POS};
      bins negative = {FCOV_MULOP_NEG};
      bins int_min = {FCOV_MULOP_MIN};
      bins minus_one = {FCOV_MULOP_MINUS_ONE};
    }

    // CHERI operations share this pipeline with mult/div.
    cp_input_category: coverpoint fcov_instr_cat(sel_dec)
        iff (us_valid_i && multpl_rdy_o &&
             (cheri_active || fcov_instr_cat(sel_dec) inside {IC_MUL, IC_DIV})) {
      bins category[] = {IC_MUL, IC_DIV, IC_JALR, IC_CHERI_INSPECT, IC_CHERI_MODIFY}
        with (CHERIoTEn || kudu_instr_cat_e'(item) inside {IC_MUL, IC_DIV});
    }
    cp_sel_ira:  coverpoint sel_ira_i iff (us_valid_i);

    cp_cjalr: coverpoint ex1_is_cjalr
        iff (cheri_active && us_valid_i) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins hit = {1'b1};
    }
    cp_setbounds_op: coverpoint fcov_setbounds_op() iff (setbounds_sample) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins setbounds = {FCOV_SB_SETBOUNDS};
      bins setboundsexact = {FCOV_SB_SETBOUNDSEXACT};
      bins setboundsimm = {FCOV_SB_SETBOUNDSIMM};
      bins setboundsrounddown = {FCOV_SB_ROUNDDOWN};
    }
    cp_setbounds_result_tag: coverpoint mult_pipeline.ex2_bounds.fcap.valid
        iff (setbounds_sample) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins cleared = {1'b0};
      bins valid = {1'b1};
    }
    cp_setbounds_reason: coverpoint fcov_setbounds_reason()
        iff (setbounds_sample) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins none = {FCOV_SB_OK};
      bins exact_inexact = {FCOV_SB_EXACT_INEXACT};
      bins out_of_parent_bounds = {FCOV_SB_OUT_OF_BOUNDS};
      bins sealed_or_untagged_input = {FCOV_SB_SEALED_UNTAGGED};
    }
    cp_setbounds_rounding: coverpoint fcov_setbounds_rounding()
        iff (setbounds_sample) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins exact = {FCOV_SB_EXACT_REP};
      bins top = {FCOV_SB_TOP_ROUNDED};
      bins base = {FCOV_SB_BASE_ROUNDED};
      bins top_and_base = {FCOV_SB_TOP_BASE_ROUNDED};
    }
    cp_setbounds_exp_path: coverpoint fcov_setbounds_path()
        iff (setbounds_sample) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins normal = {FCOV_SB_PATH_NORMAL};
      bins overflow_second = {FCOV_SB_PATH_OVERFLOW_SECOND};
      bins rndn_explen_gt_expb = {FCOV_SB_PATH_RNDN_EXPLEN_GT_EXPB};
      bins rndn_explen_le_expb = {FCOV_SB_PATH_RNDN_EXPLEN_LE_EXPB};
    }
    cp_setbounds_exp_class: coverpoint mult_pipeline.ex2_bounds.fcap.exp
        iff (setbounds_sample) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins zero = {5'd0};
      bins small_exp = {[5'd1:5'd8]};
      bins large_exp = {[5'd9:5'd23]};
      bins maximum = {[5'd24:5'd31]};
    }
    cp_setbounds_length_class: coverpoint fcov_setbounds_req_len()
        iff (setbounds_sample) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins zero = {33'h0};
      bins small_exact = {[33'h1:33'hff]};
      bins large_needing_rounding = {[33'h100:33'h7fff_ffff]};
      bins near_2g_to_4g = {[33'h8000_0000:33'h1_0000_0000]};
    }
    // EX2 holding an instruction it cannot retire this cycle (divide still
    // iterating, or WB back-pressure). SetBounds/CJALR exist only on CHERIoT HW.
    cp_ex2_busy_op: coverpoint ex2_mp_class iff (ex2_valid && !ex2_rdy) {
      bins op[] = {FCOV_MP_MULT, FCOV_MP_DIV, FCOV_MP_SETBOUNDS, FCOV_MP_CJALR}
          with (CHERIoTEn || item inside {FCOV_MP_MULT, FCOV_MP_DIV});
    }
    // Instruction presented by the issuer to EX1.
    cp_us_op: coverpoint us_mp_class iff (us_valid_i) {
      bins op[] = {FCOV_MP_MULT, FCOV_MP_DIV, FCOV_MP_SETBOUNDS, FCOV_MP_CJALR}
          with (CHERIoTEn || item inside {FCOV_MP_MULT, FCOV_MP_DIV});
    }
    cp_cjalr_pcc_set: coverpoint cjalr_pcc_set_o
        iff (cheri_active) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins hit = {1'b1};
    }
    cp_cjalr_mie: coverpoint {cjalr_clr_mie_o, cjalr_set_mie_o}
        iff (cheri_active && us_valid_i && multpl_rdy_o && ex1_is_cjalr) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins none = {2'b00};
      bins set  = {2'b01};
      bins clr  = {2'b10};
      illegal_bins both = {2'b11};
    }
    // These branch-unit misprediction flags also describe ordinary RV32 JALR.
    cp_mis_jalr: coverpoint mis_jalr_i {
      bins none  = {2'b00};
      bins slot0 = {2'b01};
      bins slot1 = {2'b10};
      bins both  = {2'b11};
    }

    cp_us: coverpoint {us_valid_i, multpl_rdy_o} {
      bins idle       = {2'b00};
      bins rdy_no_req = {2'b01};
      bins stalled    = {2'b10};
      bins accepted   = {2'b11};
    }
    cp_ds: coverpoint {multpl_valid_o, ds_rdy_i} {
      bins idle       = {2'b00};
      bins rdy_no_out = {2'b01};
      bins stalled    = {2'b10};
      bins committed  = {2'b11};
    }
    cp_ex2: coverpoint {ex2_valid, ex2_rdy} {
      bins idle     = {2'b00};
      bins ready    = {2'b01};
      bins stalled  = {2'b10};
      bins advanced = {2'b11};
    }
    cp_wb: coverpoint {wb_valid, wb_rdy} {
      bins idle     = {2'b00};
      bins ready    = {2'b01};
      bins stalled  = {2'b10};
      bins advanced = {2'b11};
    }

    cp_flush:      coverpoint flush_i { bins hit = {1'b1}; }
    cp_flush_busy: coverpoint (flush_i & (ex2_valid | wb_valid | md_div_en)) {
      bins hit = {1'b1};
    }

    cp_waw_act:       coverpoint waw_act_i.valid {
      bins none = {2'b00};
      bins v0   = {2'b01};
      bins v1   = {2'b10};
      bins both = {2'b11};
    }
    cp_ex2_waw_match: coverpoint ex2_waw_match { bins hit = {1'b1}; }
    cp_wb_waw_match:  coverpoint wb_waw_match  { bins hit = {1'b1}; }

    // ex2_err is tied low; its error-type and mcause bins had no valid samples.
    cp_out_err: coverpoint multpl_output_o.err iff (multpl_valid_o) {
      bins no_err = {1'b0};
      illegal_bins err = {1'b1};
    }
    cp_out_we:     coverpoint multpl_output_o.we     iff (multpl_valid_o);

    // 
    // Cross coverage 
    //
    x_ind_timing_div: cross cp_ind_timing, cp_div_op_sem, cp_divisor_class;

    x_div_op_divisor: cross cp_div_op_sem, cp_divisor_class;
    x_div_op_dividend: cross cp_div_op_sem, cp_dividend_class;
    x_div_op_signs: cross cp_div_op_sem, cp_signed_div_signs {
      ignore_bins unsigned_ops = binsof(cp_div_op_sem.divu) || binsof(cp_div_op_sem.remu);
    }
    x_div_op_completion: cross cp_div_complete_op, cp_div_completion_path;
    x_mulh_operands: cross cp_mulh_op_sem, cp_mulh_operand_a_class, cp_mulh_operand_b_class;
    x_setbounds_op_reason: cross cp_setbounds_op, cp_setbounds_reason {
      option.weight = CHERIoTEn ? 1 : 0;
      // Only CSetBoundsExact sets req_exact (rtl/mult_pipeline.sv).
      ignore_bins inexact_non_exact_op = binsof(cp_setbounds_reason.exact_inexact) &&
          !binsof(cp_setbounds_op.setboundsexact);
    }
    x_setbounds_op_rounding: cross cp_setbounds_op, cp_setbounds_rounding {
      option.weight = CHERIoTEn ? 1 : 0;
    }
    x_setbounds_op_exp_path: cross cp_setbounds_op, cp_setbounds_exp_path {
      option.weight = CHERIoTEn ? 1 : 0;
      // fcov_setbounds_path() returns rndn_* paths only for CSetBoundsRoundDown.
      ignore_bins rndn_path_other_op =
          (binsof(cp_setbounds_exp_path.rndn_explen_gt_expb) ||
           binsof(cp_setbounds_exp_path.rndn_explen_le_expb)) &&
          !binsof(cp_setbounds_op.setboundsrounddown);
      ignore_bins normal_path_rndn_op =
          (binsof(cp_setbounds_exp_path.normal) ||
           binsof(cp_setbounds_exp_path.overflow_second)) &&
          binsof(cp_setbounds_op.setboundsrounddown);
    }
    x_setbounds_op_length: cross cp_setbounds_op, cp_setbounds_length_class {
      option.weight = CHERIoTEn ? 1 : 0;
      // CSetBoundsImm length is a 12-bit unsigned immediate.
      ignore_bins imm_huge_length = binsof(cp_setbounds_op.setboundsimm) &&
          binsof(cp_setbounds_length_class.near_2g_to_4g);
    }
    x_setbounds_result_reason: cross cp_setbounds_result_tag, cp_setbounds_reason {
      option.weight = CHERIoTEn ? 1 : 0;
      // set_bounds/set_bounds_rndn clear the tag for every failure reason.
      ignore_bins valid_with_failure = binsof(cp_setbounds_result_tag.valid) &&
          !binsof(cp_setbounds_reason.none);
    }
    // Upstream instruction arriving while EX2 is stalled on another one.
    x_ex2_busy_us_op: cross cp_ex2_busy_op, cp_us_op
        iff (ex2_valid && !ex2_rdy && us_valid_i);
  endgroup

  cg_ma_mult u_cg_mult = new();

  AssertNoMultErr: assert property (
    @(posedge clk_i) disable iff (!rst_ni) multpl_valid_o |-> !multpl_output_o.err)
    else $error("FCOV: mult_pipeline raised .err; committer error capture (F-03) is unsafe");

  AssertMdOneHot: assert property (
    @(posedge clk_i) disable iff (!rst_ni) !(md_mult_valid && md_div_valid))
    else $error("FCOV: mult and div both valid");

  AssertCjalrMie: assert property (
    @(posedge clk_i) disable iff (!rst_ni) !(cjalr_set_mie_o && cjalr_clr_mie_o))
    else $error("FCOV: CJALR both sets and clears MIE");

`endif  // KUDU_FCOV_OFF

endmodule


// ===========================================================================
// Complex unit (atomics)
// ===========================================================================
module kudu_fcov_cmplx
  import super_pkg::*;
  import kudu_fcov_pkg::*;
(
  input logic       clk_i,
  input logic       rst_ni,

  // cmplx_fsm_e is declared inside cmplx_unit.sv (:38) and so cannot be named
  // in a port type; the raw 2-bit encoding is used instead.
  input logic [1:0] cmplx_fsm_cs,

  input logic       cmplx_instr_start_i,
  input logic       cmplx_instr_done_o,
  input logic       cmplx_lsu_req_valid_o,
  input logic       cmplx_sbd_wr_o,
  input logic       instr_is_amo,
  input logic       lspl_rdy_i,
  input logic       lspl_valid_i,
  input logic       lspl_commit,
  input pl_out_t    lspl_output_i,
  input logic       flush_i,
  input logic       sel_ira_i
);

`ifndef KUDU_FCOV_OFF

  localparam logic [1:0] CU_IDLE        = 2'd0;
  localparam logic [1:0] CU_AMO_WAIT_RD = 2'd1;
  localparam logic [1:0] CU_AMO_WRITE   = 2'd2;
  localparam logic [1:0] CU_AMO_WAIT_WR = 2'd3;

  covergroup cg_ma_cmplx @(posedge clk_i iff rst_ni);
    option.per_instance = 1;
    option.name         = "FC_MA_EX.cmplx";

    cp_state: coverpoint cmplx_fsm_cs {
      bins idle        = {CU_IDLE};
      bins amo_wait_rd = {CU_AMO_WAIT_RD};
      bins amo_write   = {CU_AMO_WRITE};
      bins amo_wait_wr = {CU_AMO_WAIT_WR};
    }

    // Native transition bins over consecutive samples of the current state.
    // WAIT_RD -> IDLE is a read error or flush; WRITE -> IDLE is only a flush.
    cp_transition: coverpoint cmplx_fsm_cs {
      bins start_req    = (CU_IDLE        => CU_AMO_WAIT_RD);
      bins read_abort   = (CU_AMO_WAIT_RD => CU_IDLE);
      bins read_ok      = (CU_AMO_WAIT_RD => CU_AMO_WRITE);
      bins wr_issued    = (CU_AMO_WRITE   => CU_AMO_WAIT_WR);
      bins wr_flush     = (CU_AMO_WRITE   => CU_IDLE);
      bins wr_done      = (CU_AMO_WAIT_WR => CU_IDLE);
      bins idle_hold    = (CU_IDLE        => CU_IDLE);
      bins wait_rd_hold = (CU_AMO_WAIT_RD => CU_AMO_WAIT_RD);
      bins write_hold   = (CU_AMO_WRITE   => CU_AMO_WRITE);
      bins wait_wr_hold = (CU_AMO_WAIT_WR => CU_AMO_WAIT_WR);
      illegal_bins bad_transition = (CU_IDLE        => CU_AMO_WRITE, CU_AMO_WAIT_WR),
                                    (CU_AMO_WAIT_RD => CU_AMO_WAIT_WR),
                                    (CU_AMO_WRITE   => CU_AMO_WAIT_RD),
                                    (CU_AMO_WAIT_WR => CU_AMO_WAIT_RD, CU_AMO_WRITE);
    }

    cp_start:    coverpoint cmplx_instr_start_i { bins hit = {1'b1}; }
    cp_is_amo:   coverpoint instr_is_amo iff (cmplx_instr_start_i);
    cp_done:     coverpoint cmplx_instr_done_o { bins hit = {1'b1}; }
    cp_req:      coverpoint cmplx_lsu_req_valid_o { bins hit = {1'b1}; }
    cp_sbd_wr:   coverpoint cmplx_sbd_wr_o { bins hit = {1'b1}; }
    cp_sel_ira:  coverpoint sel_ira_i iff (cmplx_instr_start_i);

    // An error on the read half aborts the sequence without the write ever
    // being issued, which must leave memory unmodified.
    cp_read_err: coverpoint lspl_output_i.err
                 iff (cmplx_fsm_cs == CU_AMO_WAIT_RD && lspl_commit) {
      bins ok  = {1'b0};
      bins err = {1'b1};
    }
    cp_write_err: coverpoint lspl_output_i.err
                  iff (cmplx_fsm_cs == CU_AMO_WAIT_WR && lspl_commit) {
      bins ok  = {1'b0};
      bins err = {1'b1};
    }

    cp_flush:      coverpoint flush_i { bins hit = {1'b1}; }
  endgroup

  cg_ma_cmplx u_cg_cmplx = new();

  AssertCmplxState: assert property (
    @(posedge clk_i) disable iff (!rst_ni) cmplx_fsm_cs <= CU_AMO_WAIT_WR)
    else $error("FCOV: cmplx_unit reached an undefined state");

  // Pairs with cp_transition.bad_transition.
  AssertCmplxTransition: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (cmplx_fsm_cs == CU_IDLE        |=> cmplx_fsm_cs inside {CU_IDLE, CU_AMO_WAIT_RD}) and
    (cmplx_fsm_cs == CU_AMO_WAIT_RD |=> cmplx_fsm_cs != CU_AMO_WAIT_WR) and
    (cmplx_fsm_cs == CU_AMO_WRITE   |=> cmplx_fsm_cs != CU_AMO_WAIT_RD) and
    (cmplx_fsm_cs == CU_AMO_WAIT_WR |=> cmplx_fsm_cs inside {CU_IDLE, CU_AMO_WAIT_WR}))
    else $error("FCOV: cmplx_unit took an illegal FSM transition");

`endif  // KUDU_FCOV_OFF

endmodule
