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
  import cheri_pkg::*;
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
  wire auipcc_accepted = cheri_active && us_valid_i && alupl_rdy_o &&
                         !flush_i && instr_i.cheri_op.auipcc;
  full_cap_t auipcc_pcc_full;
  mem_cap_t auipcc_pcc;
  // Mirror the inherited PCC source in cheri_alu, before the immediate is added.
  // The low RegCapW bits are register format; reg2mcap recomputes the cursor
  // corrections and compresses the exponent/top without changing the source tag.
  assign auipcc_pcc_full = pcc2fullcap_lite(alu_pipeline.pcc_cap_i, instr_i.pc);
  assign auipcc_pcc = reg2mcap(reg_cap_t'(auipcc_pcc_full));

  // ALU stage registers retain PC/result metadata but not the instruction.
  // Keep only its category, using the RTL's existing stage enables/valids.
  kudu_instr_cat_e ex2_category, wb_category;
  // A trigger match while in debug mode leaves is_brkpt set, but the
  // instruction still executes normally (issuer masks handle_debug with
  // ~debug_mode_q), so categorise it by its opcode, as the s0 path does.
  ir_dec_t instr_nobrk;
  always_comb begin
    instr_nobrk = instr_i;
    instr_nobrk.is_brkpt = 1'b0;
  end
  if (SingleStage) begin : gen_category_bypass
    assign ex2_category = fcov_instr_cat(instr_nobrk);
  end else begin : gen_category_ex2
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) ex2_category <= IC_ALU_RI;
      else if (!flush_i && ex2_rdy) ex2_category <= fcov_instr_cat(instr_nobrk);
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

    cp_auipcc_pcc_tag: coverpoint auipcc_pcc.valid iff (auipcc_accepted) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins tag[] = {0, 1};
    }
    cp_auipcc_pcc_reserved: coverpoint auipcc_pcc.rsvd iff (auipcc_accepted) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins value[] = {0, 1};
    }
    cp_auipcc_pcc_cperms: coverpoint auipcc_pcc.cperms iff (auipcc_accepted) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins permissions[] = {[0:63]};
    }
    cp_auipcc_pcc_otype: coverpoint auipcc_pcc.otype iff (auipcc_accepted) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins unsealed = {0};
      bins sentry[] = {[1:5]};
      bins sealed[] = {[6:7]};
    }
    cp_auipcc_pcc_cexp: coverpoint auipcc_pcc.cexp iff (auipcc_accepted) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins exponent[] = {[0:31]};
    }
    cp_auipcc_pcc_base: coverpoint auipcc_pcc.base9 iff (auipcc_accepted) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins zero = {0};
      bins one = {1};
      bins low = {[2:254]};
      bins boundary[] = {255, 256};
      bins high = {[257:510]};
      bins maximum = {511};
    }
    cp_auipcc_pcc_top: coverpoint auipcc_pcc.top8 iff (auipcc_accepted) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins zero = {0};
      bins one = {1};
      bins low = {[2:126]};
      bins boundary[] = {127, 128};
      bins high = {[129:254]};
      bins maximum = {255};
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

  // The SVA twin of the error check is in kudu_sva_alu.

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

  // The SVA twins of the illegal_bins above are in kudu_sva_mult.

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

  // The SVA twins of the illegal_bins above are in kudu_sva_cmplx.

`endif  // KUDU_FCOV_OFF

endmodule

// ===========================================================================
// SVA property checks for the execution units (formal + simulation).
//
// kudu_sva_alu          -- alu_pipeline (bound to both instances): in-order,
//                          no loss/duplication handshake, held-while-stalled
//                          output, forwarding consistency, RV32/Zba/Zbb/Zbs/Zbc
//                          results against an ISA reference, and CHERI ALU
//                          capability-monotonicity rules.
// kudu_sva_branch_unit  -- branch decision against a reference compare,
//                          misprediction-cause consistency, predicted targets.
// kudu_sva_mult         -- mult_pipeline: handshake/forwarding, mul/div/rem
//                          results against the RISC-V spec (incl. div-by-zero
//                          and overflow), CJALR and CSetBounds rules.
// kudu_sva_cmplx        -- cmplx_unit AMO read-modify-write sequencing.
//
// All checks look only at module ports (plus a few documented internal state
// registers), so they are independent of the multiplier implementation.
// ===========================================================================

module kudu_sva_alu
  import cheri_pkg::*;
  import super_pkg::*;
#(
  parameter bit CHERIoTEn   = 1'b1,
  parameter bit SingleStage = 1'b1
) (
  input logic        clk_i,
  input logic        rst_ni,
  input logic        cheri_pmode_i,
  input logic        flush_i,
  input logic        us_valid_i,
  input logic        alupl_rdy_o,
  input ir_dec_t     instr_i,
  input full_data2_t full_data2_i,
  input pcc_cap_t    pcc_cap_i,
  input logic        csr_mstatus_mie_i,
  input logic [31:0] fwd_act_o,
  input pl_fwd_t     fwd_info_o,
  input logic        ds_rdy_i,
  input logic        alupl_valid_o,
  input pl_out_t     alupl_output_o
);

`ifndef KUDU_FCOV_OFF

  typedef struct packed {
    logic        chk;
    logic [31:0] res;
  } sva_ref_t;

  function automatic logic [31:0] f_clz(logic [31:0] a);
    logic [31:0] n;
    logic        found;
    n = 32'd0;
    found = 1'b0;
    for (int i = 31; i >= 0; i--) begin
      if (!found && a[i]) found = 1'b1;
      else if (!found) n = n + 1;
    end
    return n;
  endfunction

  function automatic logic [31:0] f_ctz(logic [31:0] a);
    logic [31:0] n;
    logic        found;
    n = 32'd0;
    found = 1'b0;
    for (int i = 0; i < 32; i++) begin
      if (!found && a[i]) found = 1'b1;
      else if (!found) n = n + 1;
    end
    return n;
  endfunction

  function automatic logic [31:0] f_cpop(logic [31:0] a);
    logic [31:0] n;
    n = 32'd0;
    for (int i = 0; i < 32; i++) n = n + 32'(a[i]);
    return n;
  endfunction

  function automatic logic [31:0] f_ror(logic [31:0] a, logic [4:0] s);
    return (a >> s) | (a << (6'd32 - {1'b0, s}));
  endfunction

  function automatic logic [31:0] f_clmul(logic [31:0] a, logic [31:0] b, logic [1:0] mode);
    // mode 0: clmul, 1: clmulh, 2: clmulr (RISC-V Zbc definitions)
    logic [63:0] p;
    p = 64'h0;
    for (int i = 0; i < 32; i++) if (b[i]) p = p ^ ({32'h0, a} << i);
    case (mode)
      2'd1:    return p[63:32];
      2'd2:    return p[62:31];
      default: return p[31:0];
    endcase
  endfunction

  // ISA-level reference for every integer result the ALU pipeline produces,
  // decoded from the raw instruction word (independent of alu_decoder.sv).
  function automatic sva_ref_t sva_alu_ref(logic [31:0] insn, logic [31:0] a, logic [31:0] b,
                                           logic [31:0] pc, logic is_comp, logic pmode,
                                           cheri_op_t cop);
    sva_ref_t    r;
    logic [2:0]  f3;
    logic [6:0]  f7;
    logic [31:0] immi;
    logic [4:0]  sh;
    f3   = insn[14:12];
    f7   = insn[31:25];
    immi = {{20{insn[31]}}, insn[31:20]};
    sh   = insn[24:20];
    r.chk = 1'b1;
    r.res = 32'h0;
    case (insn[6:0])
      7'h37: r.res = {insn[31:12], 12'h0};                                         // lui
      7'h17: r.res = pc + (pmode ? {insn[31], insn[31:12], 11'h0} : {insn[31:12], 12'h0});
      7'h6f: r.res = pc + (is_comp ? 32'd2 : 32'd4);                             // jal link
      7'h67: begin                                                                // jalr link
        r.chk = !pmode;
        r.res = pc + (is_comp ? 32'd2 : 32'd4);
      end
      7'h13: begin
        case (f3)
          3'b000: r.res = a + immi;
          3'b010: r.res = 32'($signed(a) < $signed(immi));
          3'b011: r.res = 32'(a < immi);
          3'b100: r.res = a ^ immi;
          3'b110: r.res = a | immi;
          3'b111: r.res = a & immi;
          3'b001: begin
            if (f7 == 7'h00)                r.res = a << sh;
            else if (insn[31:20] == 12'h600) r.res = f_clz(a);
            else if (insn[31:20] == 12'h601) r.res = f_ctz(a);
            else if (insn[31:20] == 12'h602) r.res = f_cpop(a);
            else if (insn[31:20] == 12'h604) r.res = {{24{a[7]}}, a[7:0]};
            else if (insn[31:20] == 12'h605) r.res = {{16{a[15]}}, a[15:0]};
            else if (f7 == 7'h14)           r.res = a | (32'h1 << sh);
            else if (f7 == 7'h24)           r.res = a & ~(32'h1 << sh);
            else if (f7 == 7'h34)           r.res = a ^ (32'h1 << sh);
            else                            r.chk = 1'b0;
          end
          default: begin  // 3'b101
            if (f7 == 7'h00)                r.res = a >> sh;
            else if (f7 == 7'h20)           r.res = 32'($signed(a) >>> sh);
            else if (f7 == 7'h30)           r.res = f_ror(a, sh);
            else if (insn[31:20] == 12'h287)
              r.res = {{8{|a[31:24]}}, {8{|a[23:16]}}, {8{|a[15:8]}}, {8{|a[7:0]}}};
            else if (insn[31:20] == 12'h698) r.res = {a[7:0], a[15:8], a[23:16], a[31:24]};
            else if (f7 == 7'h24)           r.res = 32'((a >> sh) & 32'h1);
            else                            r.chk = 1'b0;
          end
        endcase
      end
      7'h33: begin
        case ({f7, f3})
          {7'h00, 3'b000}: r.res = a + b;
          {7'h20, 3'b000}: r.res = a - b;
          {7'h00, 3'b001}: r.res = a << b[4:0];
          {7'h00, 3'b010}: r.res = 32'($signed(a) < $signed(b));
          {7'h00, 3'b011}: r.res = 32'(a < b);
          {7'h00, 3'b100}: r.res = a ^ b;
          {7'h00, 3'b101}: r.res = a >> b[4:0];
          {7'h20, 3'b101}: r.res = 32'($signed(a) >>> b[4:0]);
          {7'h00, 3'b110}: r.res = a | b;
          {7'h00, 3'b111}: r.res = a & b;
          {7'h10, 3'b010}: r.res = (a << 1) + b;                                  // sh1add
          {7'h10, 3'b100}: r.res = (a << 2) + b;                                  // sh2add
          {7'h10, 3'b110}: r.res = (a << 3) + b;                                  // sh3add
          {7'h05, 3'b100}: r.res = ($signed(a) < $signed(b)) ? a : b;             // min
          {7'h05, 3'b110}: r.res = ($signed(a) < $signed(b)) ? b : a;             // max
          {7'h05, 3'b101}: r.res = (a < b) ? a : b;                               // minu
          {7'h05, 3'b111}: r.res = (a < b) ? b : a;                               // maxu
          {7'h20, 3'b100}: r.res = ~(a ^ b);                                      // xnor
          {7'h20, 3'b110}: r.res = a | ~b;                                        // orn
          {7'h20, 3'b111}: r.res = a & ~b;                                        // andn
          {7'h30, 3'b001}: r.res = f_ror(a, 5'(6'd32 - {1'b0, b[4:0]}));          // rol
          {7'h30, 3'b101}: r.res = f_ror(a, b[4:0]);                              // ror
          {7'h05, 3'b001}: r.res = f_clmul(a, b, 2'd0);
          {7'h05, 3'b011}: r.res = f_clmul(a, b, 2'd1);
          {7'h05, 3'b010}: r.res = f_clmul(a, b, 2'd2);
          {7'h14, 3'b001}: r.res = a | (32'h1 << b[4:0]);                         // bset
          {7'h24, 3'b001}: r.res = a & ~(32'h1 << b[4:0]);                        // bclr
          {7'h34, 3'b001}: r.res = a ^ (32'h1 << b[4:0]);                         // binv
          {7'h24, 3'b101}: r.res = 32'((a >> b[4:0]) & 32'h1);                    // bext
          {7'h04, 3'b100}: begin                                                  // zext.h
            r.chk = (insn[24:20] == 5'h0);
            r.res = {16'h0, a[15:0]};
          end
          default: r.chk = 1'b0;
        endcase
      end
      7'h5b: begin  // CHERIoT integer/address results
        r.chk = pmode;
        if (cop.cincaddr)         r.res = a + b;
        else if (cop.cincaddrimm) r.res = a + immi;
        else if (cop.csub)        r.res = a - b;
        else if (cop.csetaddr)    r.res = b;
        else if (cop.cgetaddr)    r.res = a;
        else                      r.chk = 1'b0;
      end
      7'h7b: begin  // auicgp
        r.chk = pmode;
        r.res = a + {insn[31], insn[31:12], 11'h0};
      end
      default: r.chk = 1'b0;
    endcase
    return r;
  endfunction

  // ---- Shadow scoreboard of accepted instructions (in-order, 2 entries) ----
  typedef struct packed {
    logic [31:0] insn;
    logic [31:0] pc;
    logic        is_comp;
    logic        is_jal;
    logic        any_err;
    logic        rf_we;
    logic [4:0]  rd;
    logic        pmode;
    logic        mie;
    cheri_op_t   cop;
    full_data2_t data;
    pcc_cap_t    pcc;
  } alu_snap_t;

  localparam int unsigned Capacity = SingleStage ? 1 : 2;

  alu_snap_t   sb_q [2];
  alu_snap_t   snap_d, head;
  logic [1:0]  sb_cnt_q;
  logic        sb_wp_q, sb_rp_q;
  logic        sb_push, sb_pop, out_chk;
  sva_ref_t    ref_res;

  assign snap_d = '{insn: instr_i.insn, pc: instr_i.pc, is_comp: instr_i.is_comp,
                    is_jal: instr_i.is_jal, any_err: instr_i.any_err, rf_we: instr_i.rf_we,
                    rd: instr_i.rd, pmode: CHERIoTEn & cheri_pmode_i, mie: csr_mstatus_mie_i,
                    cop: instr_i.cheri_op, data: full_data2_i, pcc: pcc_cap_i};
  assign sb_push = us_valid_i & alupl_rdy_o & ~flush_i;
  assign sb_pop  = alupl_valid_o & ds_rdy_i & ~flush_i & (sb_cnt_q != 2'd0);
  assign head    = sb_q[sb_rp_q];
  assign out_chk = alupl_valid_o & (sb_cnt_q != 2'd0);
  assign ref_res = sva_alu_ref(head.insn, head.data.d0[31:0], head.data.d1[31:0], head.pc,
                               head.is_comp, head.pmode, head.cop);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sb_cnt_q <= 2'd0;
      sb_wp_q  <= 1'b0;
      sb_rp_q  <= 1'b0;
    end else if (flush_i) begin
      sb_cnt_q <= 2'd0;
      sb_wp_q  <= 1'b0;
      sb_rp_q  <= 1'b0;
    end else begin
      if (sb_push) sb_wp_q <= ~sb_wp_q;
      if (sb_pop)  sb_rp_q <= ~sb_rp_q;
      sb_cnt_q <= sb_cnt_q + 2'(sb_push) - 2'(sb_pop);
    end
  end

  always_ff @(posedge clk_i) begin
    if (sb_push) sb_q[sb_wp_q] <= snap_d;
  end

  // rtl/alu_pipeline.sv:250-260 -- an output is only presented for an accepted, unflushed instruction (no duplicates/ghosts).
  AssertSvaAluNoSpurious: assert property (@(posedge clk_i) disable iff (!rst_ni)
    alupl_valid_o |-> sb_cnt_q != 2'd0);

  // rtl/alu_pipeline.sv:108,213 -- alupl_rdy_o never lets more instructions in than the pipeline holds.
  AssertSvaAluNoOverflow: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sb_push && !sb_pop |-> sb_cnt_q < 2'(Capacity));

  // rtl/alu_pipeline.sv:250-260 -- a full pipeline always presents its oldest instruction (no lost instruction).
  AssertSvaAluNoLoss: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sb_cnt_q >= 2'(Capacity) |-> alupl_valid_o);

  // rtl/alu_pipeline.sv:270-275 -- the output carries pc/rd/we of the oldest accepted instruction (in order).
  AssertSvaAluOutOrder: assert property (@(posedge clk_i) disable iff (!rst_ni)
    out_chk |-> alupl_output_o.pc[31:0] == head.pc && alupl_output_o.waddr == head.rd &&
                alupl_output_o.we == head.rf_we);

  // rtl/alu_pipeline.sv:247-255,174 -- a stalled output (valid & !ds_rdy) is held unchanged until taken.
  AssertSvaAluStallHold: assert property (@(posedge clk_i) disable iff (!rst_ni)
    alupl_valid_o && !ds_rdy_i && !flush_i |=> alupl_valid_o &&
      $stable({alupl_output_o.we, alupl_output_o.waddr, alupl_output_o.wdata, alupl_output_o.pc}));

  // rtl/alu_pipeline.sv:112-122,261-265 + rv32_alu.sv -- integer result equals the RV32I/Zba/Zbb/Zbs/Zbc (and CHERIoT address) reference.
  AssertSvaAluResult: assert property (@(posedge clk_i) disable iff (!rst_ni)
    out_chk && ref_res.chk && !head.any_err |->
      kudu_fcov_pkg::sva_xok(alupl_output_o.wdata[31:0] == ref_res.res));

  // rtl/alu_pipeline.sv:84-90 -- fwd_act_o is exactly the one-hot decode of the valid forwarding slots (x0 never).
  AssertSvaAluFwdAct: assert property (@(posedge clk_i) disable iff (!rst_ni)
    fwd_act_o == (((32'(fwd_info_o.valid[0]) << fwd_info_o.addr0) |
                   (32'(fwd_info_o.valid[1]) << fwd_info_o.addr1)) & ~32'h1));

  // rtl/alu_pipeline.sv:221-235,272 -- WB forwarding is only offered for a valid output that writes a non-x0 rd.
  AssertSvaAluFwdValid: assert property (@(posedge clk_i) disable iff (!rst_ni)
    fwd_info_o.valid[1] |-> alupl_valid_o && alupl_output_o.we && alupl_output_o.waddr != 5'h0 &&
                            fwd_info_o.addr1 == alupl_output_o.waddr &&
                            kudu_fcov_pkg::sva_xok(fwd_info_o.data1[31:0] == alupl_output_o.wdata[31:0]));

  if (CHERIoTEn) begin : g_cheri
    full_cap_t          cs1, cs2;
    reg_cap_t           res;
    logic [RegW-1:0]    res_w;
    logic [PERMS_W-1:0] cs1_p, cs2_p, res_p, pcc_p;
    logic [3:0]         cs1_otype4;
    logic               pm, from_cs1, from_pcc, int_res, addr_op;

    assign cs1        = head.data.d0;
    assign cs2        = head.data.d1;
    assign res        = alupl_output_o.wdata;
    assign res_w      = alupl_output_o.wdata;
    assign cs1_p      = expand_perms(cs1.cperms);
    assign cs2_p      = expand_perms(cs2.cperms);
    assign res_p      = expand_perms(res.cperms);
    assign pcc_p      = expand_perms(head.pcc.cperms);
    assign cs1_otype4 = decode_otype(cs1.otype, cs1_p[PERM_EX]);
    assign pm         = head.pmode;
    assign addr_op    = head.cop.cincaddr | head.cop.csetaddr | head.cop.cincaddrimm | head.cop.auicgp;
    assign from_cs1   = pm & (addr_op | head.cop.cseal | head.cop.cunseal | head.cop.candperm |
                              head.cop.cmove | head.cop.ccleartag);
    assign from_pcc   = pm & (head.cop.auipcc | head.is_jal);
    assign int_res    = ~(from_cs1 | from_pcc | (pm & head.cop.csethigh));

    // rtl/alu_pipeline.sv:261-265, cheri_alu.sv:57-82 -- integer results (all ops when pmode=0) carry no tag or metadata.
    AssertSvaAluIntUntagged: assert property (@(posedge clk_i) disable iff (!rst_ni)
      out_chk && int_res |-> alupl_output_o.wdata[RegW-1:32] == '0);

    // rtl/cheri_alu.sv:84-160 -- a tagged result is only derived from a tagged cs1 (or the tagged PCC for auipcc/jal).
    AssertSvaAluTagSource: assert property (@(posedge clk_i) disable iff (!rst_ni)
      out_chk && res.valid |-> (from_cs1 && cs1.valid && !head.cop.ccleartag) ||
                               (from_pcc && head.pcc.valid));

    // rtl/cheri_alu.sv:100-125 -- permissions are monotonic: a derived capability never gains a permission.
    AssertSvaAluPermMono: assert property (@(posedge clk_i) disable iff (!rst_ni)
      out_chk && res.valid |-> (!from_cs1 || ((res_p & ~cs1_p) == '0)) &&
                               (!from_pcc || ((res_p & ~pcc_p) == '0)));

    // rtl/cheri_alu.sv:84-140 -- no CHERI ALU op changes the bounds encoding of its source capability.
    AssertSvaAluBoundsKept: assert property (@(posedge clk_i) disable iff (!rst_ni)
      out_chk && res.valid |->
        (!from_cs1 || {res.exp, res.top9, res.base9} == {cs1.exp, cs1.top9, cs1.base9}) &&
        (!from_pcc || {res.exp, res.top9, res.base9} ==
                      {head.pcc.exp, 9'(head.pcc.top33 >> head.pcc.exp),
                       9'(head.pcc.base32 >> head.pcc.exp)}));

    // rtl/cheri_alu.sv:84-98 -- CSeal tags only with a tagged unsealed SE-permitted cs2 whose in-bounds address is the new otype.
    AssertSvaAluSealOk: assert property (@(posedge clk_i) disable iff (!rst_ni)
      out_chk && pm && head.cop.cseal && res.valid |->
        cs2.valid && cs2_p[PERM_SE] && cs1.otype == '0 && cs2.otype == '0 &&
        res.otype == cs2.addr[2:0] && res.otype != '0 &&
        cs2.base32 <= cs2.addr && {1'b0, cs2.addr} < cs2.top33);

    // rtl/cheri_alu.sv:100-112 -- CUnseal tags only with sealed cs1, tagged unsealed US-permitted cs2 covering cs1's otype; result unsealed.
    AssertSvaAluUnsealOk: assert property (@(posedge clk_i) disable iff (!rst_ni)
      out_chk && pm && head.cop.cunseal && res.valid |->
        cs2.valid && cs2_p[PERM_US] && cs1.otype != '0 && cs2.otype == '0 && res.otype == '0 &&
        res_p[PERM_GL] == (cs1_p[PERM_GL] & cs2_p[PERM_GL]) &&
        cs2.base32 <= 32'(cs1_otype4) && 33'(cs1_otype4) < cs2.top33);

    // rtl/cheri_alu.sv:125-141 -- address-modifying ops on a sealed cs1 always clear the tag.
    AssertSvaAluSealedAddr: assert property (@(posedge clk_i) disable iff (!rst_ni)
      out_chk && pm && addr_op && cs1.otype != '0 |-> !res.valid);

    // rtl/cheri_alu.sv:58-75,143-170 -- exact results of cmove/ccleartag/cgettag/cgetperm/cgettype.
    AssertSvaAluCapExact: assert property (@(posedge clk_i) disable iff (!rst_ni)
      out_chk && pm |->
        (!head.cop.cmove     || res_w == cs1[RegW-1:0]) &&
        (!head.cop.ccleartag || res_w == {1'b0, cs1[RegW-2:0]}) &&
        (!head.cop.cgettag   || res_w == RegW'(cs1.valid)) &&
        (!head.cop.cgetperm  || res_w == RegW'(cs1_p)) &&
        (!head.cop.cgettype  || res_w == RegW'(cs1_otype4)));

    // rtl/cheri_alu.sv:172-180 -- CJAL link is a PCC-derived cap; rd==ra seals it as a backward sentry carrying MIE.
    AssertSvaAluJalLink: assert property (@(posedge clk_i) disable iff (!rst_ni)
      out_chk && pm && head.is_jal |->
        res.otype == ((head.rd == 5'h1) ? (head.mie ? OTYPE_SENTRY_IE_BKWD : OTYPE_SENTRY_ID_BKWD)
                                        : head.pcc.otype));
  end

  // ==========================================================================
  // SVA twin of the error check in kudu_fcov_alu.
  // ==========================================================================
  AssertNoAluErr: assert property (
    @(posedge clk_i) disable iff (!rst_ni) alupl_valid_o |-> !alupl_output_o.err)
    else $error("FCOV: alu_pipeline raised .err; committer error capture (F-03) is unsafe");

`endif  // KUDU_FCOV_OFF

endmodule

module kudu_sva_branch_unit
  import cheri_pkg::*;
  import super_pkg::*;
  import kudu_fcov_pkg::*;
#(
  parameter bit CHERIoTEn = 1'b1
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

  for (genvar Slot = 0; Slot < 2; Slot++) begin : g_slot
    ir_dec_t     dec;
    full_data2_t dat;
    logic [31:0] a, b, imm_i, imm_b, imm_j, jalr_target;
    logic [3:0]  mis;
    logic [2:0]  cjalr_err;
    logic        taken, ref_cmp, f3_ok, eval_valid, issued;

    // Inputs are physical A/B; branch-unit outputs are ordered IR0/IR1.
    assign dec   = ((Slot == 0) == ira_is0_i) ? ira_dec_i : irb_dec_i;
    assign dat   = ((Slot == 0) == ira_is0_i) ? ira_full_data2_i : irb_full_data2_i;
    assign a     = dat.d0[31:0];
    assign b     = dat.d1[31:0];
    assign imm_i = {{20{dec.insn[31]}}, dec.insn[31:20]};
    assign imm_b = {{20{dec.insn[31]}}, dec.insn[7], dec.insn[30:25], dec.insn[11:8], 1'b0};
    assign imm_j = {{12{dec.insn[31]}}, dec.insn[19:12], dec.insn[20], dec.insn[30:21], 1'b0};
    assign taken = branch_info_o.branch_taken[Slot];
    assign mis   = {branch_info_o.mis_jalr[Slot], branch_info_o.mis_jal[Slot],
                    branch_info_o.mis_not_taken[Slot], branch_info_o.mis_taken[Slot]};
    assign jalr_target = (Slot == 0) ? ir0_jalr_target_o : ir1_jalr_target_o;
    assign cjalr_err   = (Slot == 0) ? ir0_cjalr_err_o : ir1_cjalr_err_o;

    always_comb begin
      f3_ok   = 1'b1;
      ref_cmp = 1'b0;
      case (dec.insn[14:12])
        3'b000:  ref_cmp = (a == b);
        3'b001:  ref_cmp = (a != b);
        3'b100:  ref_cmp = ($signed(a) <  $signed(b));
        3'b101:  ref_cmp = ($signed(a) >= $signed(b));
        3'b110:  ref_cmp = (a <  b);
        3'b111:  ref_cmp = (a >= b);
        default: f3_ok   = 1'b0;
      endcase
    end

    // Same qualifier as kudu_fcov_branch_unit: the slot is being evaluated in DECODE.
    assign eval_valid = kudu_top.issuer_i.ctrl_fsm_cs[CSM_DECODE] &&
        kudu_top.issuer_i.ir_valid_i[Slot] && !kudu_top.issuer_i.ir_hazard[Slot] &&
        !kudu_top.issuer_i.cmt_err_i && !dec.any_err &&
        (dec.is_branch || dec.is_jal || dec.is_jalr);
    assign issued = (Slot == 0) ? kudu_top.issuer_i.ir0_issued : kudu_top.issuer_i.ir1_issued;

    // rtl/branch_unit.sv:35-64,139-145 -- taken equals the RV32 reference compare for the slot's own operands (jal always taken).
    AssertSvaBrTaken: assert property (@(posedge clk_i) disable iff (!rst_ni)
      !(dec.is_branch && !f3_ok) |-> taken == (dec.is_jal || (dec.is_branch && ref_cmp)));

    // rtl/branch_unit.sv:79-98 -- at most one mispredict cause, and only for the matching instruction type.
    AssertSvaBrMisType: assert property (@(posedge clk_i) disable iff (!rst_ni)
      !$isunknown({mis, dec.is_branch, dec.is_jal, dec.is_jalr}) |->
        $onehot0(mis) && (!(mis[0] || mis[1]) || dec.is_branch) && (!mis[2] || dec.is_jal) &&
        (!mis[3] || dec.is_jalr));

    // rtl/branch_unit.sv:79-89 -- without a direction mispredict, the predicted direction is the actual one.
    AssertSvaBrDirOk: assert property (@(posedge clk_i) disable iff (!rst_ni)
      (dec.is_branch && !mis[0] && !mis[1] |-> dec.ptaken == taken) and
      (dec.is_jal && !mis[2] |-> dec.ptaken));

    // rtl/branch_unit.sv:66-75,170-174 -- JALR target is rs1+imm with bit 0 cleared.
    AssertSvaBrJalrTarget: assert property (@(posedge clk_i) disable iff (!rst_ni)
      !$isunknown({a, imm_i}) |-> kudu_fcov_pkg::sva_xok(jalr_target == ((a + imm_i) & ~32'h1)));

    // rtl/branch_unit.sv:94-96, branch_predict.sv:147-160, ir_stage.sv:198-208 -- an accepted JALR prediction targets the real rs1+imm.
    AssertSvaBrJalrPredTarget: assert property (@(posedge clk_i) disable iff (!rst_ni)
      eval_valid && issued && dec.is_jalr && !mis[3] |-> dec.ptarget[31:0] == jalr_target);

    // rtl/branch_unit.sv:82-92, issuer.sv:879 -- a taken branch/jal accepted as predicted had the right predicted target.
    AssertSvaBrPredTarget: assert property (@(posedge clk_i) disable iff (!rst_ni)
      eval_valid && issued && taken && (dec.is_branch || dec.is_jal) && !mis[0] && !mis[2] |->
        dec.ptarget[31:0] == dec.btarget);

    // rtl/ir_decoder.sv:126 -- the branch/jal target used for redirect is pc + B/J immediate.
    AssertSvaBrTargetRef: assert property (@(posedge clk_i) disable iff (!rst_ni)
      eval_valid && (dec.is_branch || dec.is_jal) |->
        dec.btarget == dec.pc + (dec.is_jal ? imm_j : imm_b));

    if (CHERIoTEn) begin : g_cheri
      full_cap_t          cs1;
      logic [PERMS_W-1:0] cs1_p;
      assign cs1   = dat.d0;
      assign cs1_p = expand_perms(cs1.cperms);

      // rtl/branch_unit.sv:101-131 -- an error-free CJALR has a tagged executable cs1 that is unsealed or a sentry with imm 0.
      AssertSvaBrCjalrOk: assert property (@(posedge clk_i) disable iff (!rst_ni)
        cheri_pmode_i && !debug_mode_i && dec.is_jalr && cjalr_err == 3'h0 |->
          cs1.valid && cs1_p[PERM_EX] && (cs1.otype == '0 || dec.insn[31:20] == 12'h0));
    end
  end

`endif  // KUDU_FCOV_OFF

endmodule

// Port-level only: independent of the multiplier implementation (UseDWMult).
module kudu_sva_mult
  import cheri_pkg::*;
  import super_pkg::*;
#(
  parameter bit CHERIoTEn = 1'b1
) (
  input logic        clk_i,
  input logic        rst_ni,
  input logic        cheri_pmode_i,
  input logic        flush_i,
  input logic        us_valid_i,
  input logic        multpl_rdy_o,
  input logic        sel_ira_i,
  input ir_dec_t     ira_dec_i,
  input ir_dec_t     irb_dec_i,
  input full_data2_t ira_full_data2_i,
  input full_data2_t irb_full_data2_i,
  input logic [31:0] fwd_act_o,
  input pl_fwd_t     fwd_info_o,
  input logic        ds_rdy_i,
  input logic        multpl_valid_o,
  input pl_out_t     multpl_output_o,
  input pcc_cap_t    pcc_cap_i,
  input logic        csr_mstatus_mie_i,
  input pcc_cap_t    cjalr_pcap_o,
  input logic        cjalr_pcc_set_o,
  input logic        cjalr_set_mie_o,
  input logic        cjalr_clr_mie_o,
  input logic        md_mult_valid,
  input logic        md_div_valid
);

`ifndef KUDU_FCOV_OFF

  typedef struct packed {
    logic [31:0] insn;
    logic [31:0] pc;
    logic        is_comp;
    logic        is_jalr;
    logic        any_err;
    logic        rf_we;
    logic [4:0]  rd;
    logic        pmode;
    logic        mie;
    cheri_op_t   cop;
    full_data2_t data;
    pcc_cap_t    pcc;
  } mult_snap_t;

  ir_dec_t     dec;
  full_data2_t dat;
  mult_snap_t  sb_q [2];
  mult_snap_t  snap_d, head;
  logic [1:0]  sb_cnt_q;
  logic        sb_wp_q, sb_rp_q;
  logic        sb_push, sb_pop, out_chk, is_md;
  logic [31:0] a, b, res;
  logic signed [65:0] prod_ss, prod_su, prod_uu;
  logic [2:0]  f3;

  assign dec    = sel_ira_i ? ira_dec_i : irb_dec_i;
  assign dat    = sel_ira_i ? ira_full_data2_i : irb_full_data2_i;
  assign snap_d = '{insn: dec.insn, pc: dec.pc, is_comp: dec.is_comp, is_jalr: dec.is_jalr,
                    any_err: dec.any_err, rf_we: dec.rf_we, rd: dec.rd,
                    pmode: CHERIoTEn & cheri_pmode_i, mie: csr_mstatus_mie_i,
                    cop: dec.cheri_op, data: dat, pcc: pcc_cap_i};
  assign sb_push = us_valid_i & multpl_rdy_o & ~flush_i;
  assign sb_pop  = multpl_valid_o & ds_rdy_i & ~flush_i & (sb_cnt_q != 2'd0);
  assign head    = sb_q[sb_rp_q];
  assign out_chk = multpl_valid_o & (sb_cnt_q != 2'd0);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sb_cnt_q <= 2'd0;
      sb_wp_q  <= 1'b0;
      sb_rp_q  <= 1'b0;
    end else if (flush_i) begin
      sb_cnt_q <= 2'd0;
      sb_wp_q  <= 1'b0;
      sb_rp_q  <= 1'b0;
    end else begin
      if (sb_push) sb_wp_q <= ~sb_wp_q;
      if (sb_pop)  sb_rp_q <= ~sb_rp_q;
      sb_cnt_q <= sb_cnt_q + 2'(sb_push) - 2'(sb_pop);
    end
  end

  always_ff @(posedge clk_i) begin
    if (sb_push) sb_q[sb_wp_q] <= snap_d;
  end

  // RV32M reference (RISC-V unprivileged spec, chapter M).
  assign a       = head.data.d0[31:0];
  assign b       = head.data.d1[31:0];
  assign res     = multpl_output_o.wdata[31:0];
  assign f3      = head.insn[14:12];
  assign is_md   = !head.any_err && head.insn[6:0] == 7'h33 && head.insn[31:25] == 7'h01;
  // 33x33 signed products of the sign/zero-extended operands (mulh: ss, mulhsu: su, mulhu: uu).
  assign prod_ss = $signed({a[31], a}) * $signed({b[31], b});
  assign prod_su = $signed({a[31], a}) * $signed({1'b0, b});
  assign prod_uu = $signed({1'b0, a}) * $signed({1'b0, b});

  // rtl/mult_pipeline.sv:316-325 -- the two-stage pipeline never accepts more than it holds.
  AssertSvaMultNoOverflow: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sb_push && !sb_pop |-> sb_cnt_q < 2'd2);

  // rtl/mult_pipeline.sv:422-431 -- an output is only presented for an accepted, unflushed instruction.
  AssertSvaMultNoSpurious: assert property (@(posedge clk_i) disable iff (!rst_ni)
    multpl_valid_o |-> sb_cnt_q != 2'd0);

  // rtl/mult_pipeline.sv:316-325,422-431 -- with both stages occupied the oldest is presented (no loss).
  AssertSvaMultNoLoss: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sb_cnt_q == 2'd2 |-> multpl_valid_o);

  // rtl/mult_pipeline.sv:436-443 -- the output carries pc/rd/we of the oldest accepted instruction (in order).
  AssertSvaMultOutOrder: assert property (@(posedge clk_i) disable iff (!rst_ni)
    out_chk |-> multpl_output_o.pc[31:0] == head.pc && multpl_output_o.waddr == head.rd &&
                multpl_output_o.we == head.rf_we);

  // rtl/mult_pipeline.sv:420-431 -- a stalled output is held unchanged until taken.
  AssertSvaMultStallHold: assert property (@(posedge clk_i) disable iff (!rst_ni)
    multpl_valid_o && !ds_rdy_i && !flush_i |=> multpl_valid_o &&
      $stable({multpl_output_o.we, multpl_output_o.waddr, multpl_output_o.wdata, multpl_output_o.pc}));

  // rtl/mult_pipeline.sv:108-123 -- fwd_act_o is the registered decode of the WB forwarding slot (x0 never).
  AssertSvaMultFwdAct: assert property (@(posedge clk_i) disable iff (!rst_ni)
    fwd_act_o == ((32'(fwd_info_o.valid[1]) << fwd_info_o.addr1) & ~32'h1) && !fwd_info_o.valid[0]);

  // rtl/mult_pipeline.sv:401-412 -- WB forwarding only for a valid output writing a non-x0 rd.
  AssertSvaMultFwdValid: assert property (@(posedge clk_i) disable iff (!rst_ni)
    fwd_info_o.valid[1] |-> multpl_valid_o && multpl_output_o.we && multpl_output_o.waddr != 5'h0 &&
                            fwd_info_o.addr1 == multpl_output_o.waddr &&
                            fwd_info_o.data1[31:0] == multpl_output_o.wdata[31:0]);

  // rtl/mult_pipeline.sv:160-180,366-367 + multdiv32.sv -- MUL returns the low 32 bits of the product.
  AssertSvaMultMulLo: assert property (@(posedge clk_i) disable iff (!rst_ni)
    out_chk && is_md && f3 == 3'b000 |-> res == 32'(a * b));

  // rtl/mult_pipeline.sv:180-195 + multdiv32.sv -- MULH/MULHSU/MULHU return the high word of the ss/su/uu product.
  AssertSvaMultMulHi: assert property (@(posedge clk_i) disable iff (!rst_ni)
    out_chk && is_md && f3[2] == 1'b0 && f3[1:0] != 2'b00 |->
      res == ((f3[1:0] == 2'b01) ? prod_ss[63:32] :
              (f3[1:0] == 2'b10) ? prod_su[63:32] : prod_uu[63:32]));

  // rtl/mult_pipeline.sv:181-200 + multdiv32.sv:636-770 -- DIV/DIVU/REM/REMU quotient/remainder (b != 0, no overflow).
  AssertSvaMultDiv: assert property (@(posedge clk_i) disable iff (!rst_ni)
    out_chk && is_md && f3[2] && b != 32'h0 && !(!f3[0] && a == 32'h8000_0000 && b == 32'hffff_ffff) |->
      res == ((f3 == 3'b100) ? 32'($signed(a) / $signed(b)) :
              (f3 == 3'b101) ? a / b :
              (f3 == 3'b110) ? 32'($signed(a) % $signed(b)) : a % b));

  // multdiv32.sv:636-770 -- division by zero: quotient all ones, remainder = dividend (RISC-V M table 7.1).
  AssertSvaMultDivZero: assert property (@(posedge clk_i) disable iff (!rst_ni)
    out_chk && is_md && f3[2] && b == 32'h0 |-> res == (f3[1] ? a : 32'hffff_ffff));

  // multdiv32.sv:636-770 -- signed overflow -2^31 / -1: quotient -2^31, remainder 0.
  AssertSvaMultDivOvf: assert property (@(posedge clk_i) disable iff (!rst_ni)
    out_chk && is_md && f3[2] && !f3[0] && a == 32'h8000_0000 && b == 32'hffff_ffff |->
      res == (f3[1] ? 32'h0 : 32'h8000_0000));

  if (CHERIoTEn) begin : g_cheri
    full_cap_t          cs1, cs2, rfcap, ex1_cs1;
    reg_cap_t           rcap;
    logic               pm, is_cjalr, is_sb, is_rndn, cap_res;
    logic [32:0]        req_top;
    logic [31:0]        req_len;

    assign pm       = head.pmode;
    assign cs1      = head.data.d0;
    assign cs2      = head.data.d1;
    assign ex1_cs1  = dat.d0;
    assign rcap     = multpl_output_o.wdata;
    assign rfcap    = op2fullcap(reg2opcap(rcap));
    assign is_cjalr = pm & head.is_jalr;
    assign is_rndn  = pm & head.cop.csetboundsrndn;
    assign is_sb    = pm & (head.cop.csetbounds | head.cop.csetboundsex | head.cop.csetboundsimm);
    assign cap_res  = is_cjalr | is_sb | is_rndn;
    assign req_len  = head.cop.csetboundsimm ? 32'(head.insn[31:20]) : cs2.addr;
    assign req_top  = {1'b0, cs1.addr} + {1'b0, req_len};

    // rtl/mult_pipeline.sv:376-381 -- integer results (M ops, crrl, cram) carry no tag/metadata.
    AssertSvaMultIntUntagged: assert property (@(posedge clk_i) disable iff (!rst_ni)
      out_chk && !cap_res |-> multpl_output_o.wdata[RegW-1:32] == '0);

    // rtl/mult_pipeline.sv:229-236,348-351 -- CJALR link = PCC with address pc+2/4; rd==ra seals it as a backward sentry with MIE.
    AssertSvaMultCjalrLink: assert property (@(posedge clk_i) disable iff (!rst_ni)
      out_chk && is_cjalr |->
        rcap.addr == head.pc + (head.is_comp ? 32'd2 : 32'd4) &&
        rcap.otype == ((head.rd == 5'h1) ? (head.mie ? OTYPE_SENTRY_IE_BKWD : OTYPE_SENTRY_ID_BKWD)
                                         : head.pcc.otype) &&
        rcap.cperms == head.pcc.cperms && (!rcap.valid || head.pcc.valid));

    // rtl/mult_pipeline.sv:237-244 -- the new PCC is cs1 unsealed (all else unchanged); MIE update only with it and per sentry type.
    AssertSvaMultCjalrPcap: assert property (@(posedge clk_i) disable iff (!rst_ni)
      (cjalr_set_mie_o || cjalr_clr_mie_o |-> cjalr_pcc_set_o) and
      (cjalr_pcc_set_o |->
        cjalr_pcap_o.otype == '0 && cjalr_pcap_o.valid == ex1_cs1.valid &&
        cjalr_pcap_o.top33 == ex1_cs1.top33 && cjalr_pcap_o.base32 == ex1_cs1.base32 &&
        cjalr_pcap_o.perms == ex1_cs1.perms && cjalr_pcap_o.exp == ex1_cs1.exp &&
        cjalr_set_mie_o == (ex1_cs1.otype == OTYPE_SENTRY_IE_FWD || ex1_cs1.otype == OTYPE_SENTRY_IE_BKWD) &&
        cjalr_clr_mie_o == (ex1_cs1.otype == OTYPE_SENTRY_ID_FWD || ex1_cs1.otype == OTYPE_SENTRY_ID_BKWD)));

    // rtl/mult_pipeline.sv:244 -- PCC is never updated by a CJALR that is being flushed in the same cycle.
    AssertSvaMultCjalrNoFlush: assert property (@(posedge clk_i) disable iff (!rst_ni)
      cjalr_pcc_set_o |-> !flush_i && multpl_rdy_o && us_valid_i);

    // rtl/mult_pipeline.sv:262-300,366-376, cheri_pkg.sv:468-583 -- CSetBounds* only tags from a tagged unsealed cs1 and
    // keeps address, permissions and otype.
    AssertSvaMultSbMeta: assert property (@(posedge clk_i) disable iff (!rst_ni)
      out_chk && (is_sb || is_rndn) && rcap.valid |->
        cs1.valid && cs1.otype == '0 && rcap.otype == '0 && rcap.addr == cs1.addr &&
        rcap.cperms == cs1.cperms);

    // cheri_pkg.sv:468-536 -- a tagged CSetBounds/Ex/Imm result lies within cs1's bounds and covers [addr, addr+len).
    AssertSvaMultSbBounds: assert property (@(posedge clk_i) disable iff (!rst_ni)
      out_chk && is_sb && rcap.valid |->
        rfcap.base32 >= cs1.base32 && rfcap.top33 <= cs1.top33 &&
        rfcap.base32 <= cs1.addr && rfcap.top33 >= req_top);

    // cheri_pkg.sv:468-536 -- CSetBoundsExact yields exactly [addr, addr+len) when tagged.
    AssertSvaMultSbExact: assert property (@(posedge clk_i) disable iff (!rst_ni)
      out_chk && pm && head.cop.csetboundsex && rcap.valid |->
        rfcap.base32 == cs1.addr && rfcap.top33 == req_top);

    // cheri_pkg.sv:538-583 -- CSetBoundsRoundDown: base == addr, top <= addr+len, within cs1's bounds.
    AssertSvaMultSbRndn: assert property (@(posedge clk_i) disable iff (!rst_ni)
      out_chk && is_rndn && rcap.valid |->
        rfcap.base32 == cs1.addr && rfcap.top33 <= req_top && rfcap.top33 >= {1'b0, cs1.addr} &&
        rfcap.top33 <= cs1.top33);
  end

  // ==========================================================================
  // SVA twins of the illegal_bins in kudu_fcov_mult.
  // ==========================================================================
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

module kudu_sva_cmplx
  import cheri_pkg::*;
  import super_pkg::*;
#(
  parameter bit CHERIoTEn = 1'b1
) (
  input logic          clk_i,
  input logic          rst_ni,
  input logic          flush_i,
  input logic          sel_ira_i,
  input ir_dec_t       ira_dec_i,
  input ir_dec_t       irb_dec_i,
  input full_data2_t   ira_full_data2_i,
  input full_data2_t   irb_full_data2_i,
  input logic          cmplx_instr_start_i,
  input logic          cmplx_instr_done_o,
  input logic          lspl_valid_i,
  input pl_out_t       lspl_output_i,
  input logic          lspl_rdy_i,
  input logic          cmplx_lsu_req_valid_o,
  input lsu_req_info_t cmplx_lsu_req_info_o,
  input ir_dec_t       ir_dec_q,
  input full_data2_t   ir_full_data2_q,
  input logic [1:0]    cmplx_fsm_cs
);

`ifndef KUDU_FCOV_OFF

  // RISC-V A: AMO<op>.W memory update value from the loaded word and rs2.
  function automatic logic [31:0] amo_ref(logic [4:0] op, logic [31:0] m, logic [31:0] r);
    case (op)
      5'h00:   return m + r;
      5'h01:   return r;
      5'h04:   return m ^ r;
      5'h08:   return m | r;
      5'h0c:   return m & r;
      5'h10:   return ($signed(m) < $signed(r)) ? m : r;
      5'h14:   return ($signed(m) < $signed(r)) ? r : m;
      5'h18:   return (m < r) ? m : r;
      5'h1c:   return (m < r) ? r : m;
      default: return r;
    endcase
  endfunction

  ir_dec_t     cur_dec;
  full_data2_t cur_dat;
  logic        rd_req, wr_req, commit;
  logic        busy_q, rd_ok_q;
  logic [31:0] t_addr_q, t_rs2_q, t_rdata_q;
  logic [4:0]  t_op_q, t_rd_q;

  assign cur_dec = sel_ira_i ? ira_dec_i : irb_dec_i;
  assign cur_dat = sel_ira_i ? ira_full_data2_i : irb_full_data2_i;
  assign rd_req  = cmplx_lsu_req_valid_o & cmplx_lsu_req_info_o.is_load;
  assign wr_req  = cmplx_lsu_req_valid_o & ~cmplx_lsu_req_info_o.is_load;
  assign commit  = lspl_valid_i & lspl_rdy_i;

  // Port-level transaction tracker: one AMO = read request, read response, write request, write response.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      busy_q  <= 1'b0;
      rd_ok_q <= 1'b0;
    end else if (flush_i || cmplx_instr_done_o) begin
      busy_q  <= 1'b0;
      rd_ok_q <= 1'b0;
    end else begin
      if (rd_req && !busy_q) busy_q <= 1'b1;
      if (busy_q && !rd_ok_q && commit && !lspl_output_i.err) rd_ok_q <= 1'b1;
    end
  end

  always_ff @(posedge clk_i) begin
    if (rd_req && !busy_q) begin
      t_addr_q <= cur_dat.d0[31:0];
      t_rs2_q  <= cur_dat.d1[31:0];
      t_op_q   <= cur_dec.insn[31:27];
      t_rd_q   <= cur_dec.rd;
    end
    if (busy_q && !rd_ok_q && commit) t_rdata_q <= lspl_output_i.wdata[31:0];
  end

  // rtl/cmplx_unit.sv:72-74,88-91 -- the FSM leaves IDLE on start without waiting, so the read request must be accepted at once.
  AssertSvaCmplxRdAccept: assert property (@(posedge clk_i) disable iff (!rst_ni)
    rd_req |-> lspl_rdy_i);

  // rtl/cmplx_unit.sv:88-91, issuer.sv:766 -- start is only given for an AMO in IDLE, never while one is in flight.
  AssertSvaCmplxStart: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cmplx_instr_start_i |-> cmplx_fsm_cs == 2'd0 && !busy_q && ir_dec_q.insn[6:0] == 7'h2f);

  // rtl/cmplx_unit.sv:193-197 -- operands are captured the cycle before start; they must still be the live operands at start.
  AssertSvaCmplxCapture: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cmplx_instr_start_i && cmplx_fsm_cs == 2'd0 |->
      ir_dec_q.insn == cur_dec.insn && ir_dec_q.pc == cur_dec.pc && ir_dec_q.rd == cur_dec.rd &&
      ir_full_data2_q.d0[31:0] == cur_dat.d0[31:0] && ir_full_data2_q.d1[31:0] == cur_dat.d1[31:0]);

  // rtl/cmplx_unit.sv:72-74,99-107 -- the AMO write is only requested after a successful read of the same AMO.
  AssertSvaCmplxWrAfterRd: assert property (@(posedge clk_i) disable iff (!rst_ni)
    wr_req |-> busy_q && rd_ok_q);

  // rtl/cmplx_unit.sv:122-182 -- AMO write targets rs1 with the RISC-V A reference value of (loaded word, rs2), and rd.
  AssertSvaCmplxWrData: assert property (@(posedge clk_i) disable iff (!rst_ni)
    wr_req && busy_q && rd_ok_q |->
      cmplx_lsu_req_info_o.addr == t_addr_q && cmplx_lsu_req_info_o.rd == t_rd_q &&
      cmplx_lsu_req_info_o.rf_we &&
      cmplx_lsu_req_info_o.wdata[31:0] == amo_ref(t_op_q, t_rdata_q, t_rs2_q));

  // rtl/cmplx_unit.sv:72-74,104-107 -- a write request stays asserted and unchanged until the LSU accepts it.
  AssertSvaCmplxWrHold: assert property (@(posedge clk_i) disable iff (!rst_ni)
    wr_req && !lspl_rdy_i && !flush_i |=> wr_req &&
      $stable({cmplx_lsu_req_info_o.addr, cmplx_lsu_req_info_o.wdata, cmplx_lsu_req_info_o.rd}));

  // rtl/cmplx_unit.sv:66-67 -- done only completes an AMO that was started (and not flushed).
  AssertSvaCmplxDone: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cmplx_instr_done_o |-> busy_q);

  // ==========================================================================
  // SVA twins of the illegal_bins in kudu_fcov_cmplx.  The state encoding
  // duplicates kudu_fcov_cmplx (cmplx_unit.sv:38); keep the two in sync.
  // ==========================================================================
  localparam logic [1:0] CU_IDLE        = 2'd0;
  localparam logic [1:0] CU_AMO_WAIT_RD = 2'd1;
  localparam logic [1:0] CU_AMO_WRITE   = 2'd2;
  localparam logic [1:0] CU_AMO_WAIT_WR = 2'd3;

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

// ============================================================================
// FV helper lemmas: formal only, compiled only with +define+KUDU_FV_HELPERS.
//
// Auxiliary invariants that JasperGold proves and then assumes (run_fcov_clean
// in fv/fv_kudu_fcov.tcl) so that the harder assertions above become
// inductive. No covergroups; simulation never defines KUDU_FV_HELPERS. They
// are bound only in the KUDU_FV_HELPERS block at the end of kudu_fcov_bind.sv,
// which sits inside its KUDU_FCOV_OFF and CHERIoT guards. They read the fcov
// instances bound there and were proven only with CHERIoTEn=1, so the
// definitions carry the same guards: an unbound copy would become an extra
// top-level module with unresolvable kudu_top.* references.
// ============================================================================
`ifdef KUDU_FV_HELPERS
`ifdef CHERIoT
`ifndef KUDU_FCOV_OFF

// kudu_fvh_ex_lsu (was fv/fv_help_ex_lsu.sv, bound into kudu_top as
// u_fvh_ex_lsu).
//
// FV helper invariants (lemmas) for the ex_lsu hard fcov targets:
//   branch_unit  AssertSvaBrPredTarget
//   mult         AssertSvaMultSbBounds/SbExact/SbRndn
//   lsu          AssertNoFaultingReqOnBus/AssertCapAccess8Aligned/AssertCapStoreTag
module kudu_fvh_ex_lsu import super_pkg::*; import cheri_pkg::*; (
  input logic clk_i,
  input logic rst_ni
);

  // ===========================================================================
  // Branch prediction target (PredictUseBtb=0: ptarget = decoded pc + offset)
  // ===========================================================================
  // copies of fetch_fifo64 dec_branch/dec_jal and branch_predict dec_target
  function automatic logic h_dec_branch(logic [15:0] insn16);
    return ((insn16[1:0] == 2'b01) && (insn16[15:14] == 2'b11)) || (insn16[6:0] == OPCODE_BRANCH);
  endfunction

  function automatic logic h_dec_jal(logic [15:0] insn16);
    return ((insn16[1:0] == 2'b01) && (insn16[14:13] == 2'b01)) || (insn16[6:0] == OPCODE_JAL);
  endfunction

  function automatic logic [31:0] h_dec_target(ir_reg_t instr_i);
    logic [31:0] offset, insn32, imm_j_type, imm_b_type;
    logic [15:0] insn16;
    insn16 = instr_i.insn[15:0];
    if (instr_i.is_branch && (instr_i.insn[1:0] == 2'b01) && (instr_i.insn[15:14] == 2'b11))
      insn32 = {{4 {insn16[12]}}, insn16[6:5], insn16[2], 5'b0, 2'b01,
                insn16[9:7], 2'b00, insn16[13], insn16[11:10], insn16[4:3],
                insn16[12], {OPCODE_BRANCH}};
    else if (instr_i.is_jal && (instr_i.insn[1:0] == 2'b01) && (instr_i.insn[14:13] == 2'b01))
      insn32 = {insn16[12], insn16[8], insn16[10:9], insn16[6],
                insn16[7], insn16[2], insn16[11], insn16[5:3],
                {9 {insn16[12]}}, 4'b0, ~insn16[15], {OPCODE_JAL}};
    else
      insn32 = instr_i.insn;
    imm_j_type = { {12{insn32[31]}}, insn32[19:12], insn32[20], insn32[30:21], 1'b0 };
    imm_b_type = { {19{insn32[31]}}, insn32[31], insn32[7], insn32[30:25], insn32[11:8], 1'b0 };
    offset = instr_i.is_branch ? imm_b_type : imm_j_type;
    return instr_i.pc + offset;
  endfunction

  // IF/s0 entry: predecode flags match the instruction bits
  function automatic logic h_reg_flags_ok(ir_reg_t r);
    return (r.is_branch == h_dec_branch(r.insn[15:0])) && (r.is_jal == h_dec_jal(r.insn[15:0]));
  endfunction

  // IF/s0 entry: a predicted-taken branch/jal carries the decoded target
  function automatic logic h_reg_tgt_ok(ir_reg_t r);
    return !(r.ptaken && (r.is_branch || r.is_jal) && !r.errs.fetch_err) ||
           (r.ptarget == h_dec_target(r));
  endfunction

  // decoded/s1 entry: a predicted-taken error-free branch/jal has ptarget == btarget
  function automatic logic h_dec_tgt_ok(ir_dec_t d);
    return !((d.is_branch || d.is_jal) && d.ptaken && !d.any_err) || (d.ptarget[31:0] == d.btarget);
  endfunction

  ir_reg_t h_if0, h_if1;
  ir_reg_t h_s0m[4];
  ir_dec_t h_dec0, h_dec1, h_s1m[2];

  assign h_if0  = kudu_top.if_instr0;
  assign h_if1  = kudu_top.if_instr1;
  assign h_dec0 = kudu_top.ir_stage_i.dec_out0;
  assign h_dec1 = kudu_top.ir_stage_i.dec_out1;
  for (genvar i = 0; i < 4; i++) begin : g_s0m
    assign h_s0m[i] = ir_reg_t'(kudu_top.ir_stage_i.gen_stage0_buffer.s0_fifo.fifo_mem[i]);
  end
  for (genvar i = 0; i < 2; i++) begin : g_s1m
    assign h_s1m[i] = ir_dec_t'(kudu_top.ir_stage_i.gen_stage1.s1_fifo.fifo_mem[i]);
  end

  AssertHelpBrIfFlags0: assert property (@(posedge clk_i) disable iff (!rst_ni) h_reg_flags_ok(h_if0));
  AssertHelpBrIfFlags1: assert property (@(posedge clk_i) disable iff (!rst_ni) h_reg_flags_ok(h_if1));
  AssertHelpBrIfTgt0:   assert property (@(posedge clk_i) disable iff (!rst_ni) h_reg_tgt_ok(h_if0));
  AssertHelpBrIfTgt1:   assert property (@(posedge clk_i) disable iff (!rst_ni) h_reg_tgt_ok(h_if1));
  for (genvar i = 0; i < 4; i++) begin : g_br_s0
    AssertHelpBrS0Flags: assert property (@(posedge clk_i) disable iff (!rst_ni) h_reg_flags_ok(h_s0m[i]));
    AssertHelpBrS0Tgt:   assert property (@(posedge clk_i) disable iff (!rst_ni) h_reg_tgt_ok(h_s0m[i]));
  end
  AssertHelpBrDecTgt0: assert property (@(posedge clk_i) disable iff (!rst_ni) h_dec_tgt_ok(h_dec0));
  AssertHelpBrDecTgt1: assert property (@(posedge clk_i) disable iff (!rst_ni) h_dec_tgt_ok(h_dec1));
  for (genvar i = 0; i < 2; i++) begin : g_br_s1
    AssertHelpBrS1Tgt: assert property (@(posedge clk_i) disable iff (!rst_ni) h_dec_tgt_ok(h_s1m[i]));
  end

  // ===========================================================================
  // LSU: lsu_if / load_store_unit request consistency
  // ===========================================================================
  logic          l_pmode, l_dbg, l_busy, l_dly_valid, l_in_valid;
  logic [2:0]    l_lsif;
  lsu_req_info_t l_hold, l_dly, l_in;
  lschk_err_t    l_hold_chk;

  assign l_pmode     = kudu_top.ls_pipeline_i.lsu_if_i.cheri_pmode;
  assign l_dbg       = kudu_top.ls_pipeline_i.lsu_if_i.debug_mode_i;
  assign l_busy      = (kudu_top.ls_pipeline_i.load_store_unit_i.ls_fsm_cs != IDLE);
  assign l_lsif      = 3'(kudu_top.ls_pipeline_i.lsu_if_i.lsif_fsm_q);
  assign l_hold      = kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q;
  assign l_dly       = kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q;
  assign l_dly_valid = kudu_top.ls_pipeline_i.lsu_if_i.req_dly_valid;
  assign l_in        = kudu_top.ls_pipeline_i.lsu_if_i.lsu_req_dec_i;
  assign l_in_valid  = kudu_top.ls_pipeline_i.lsu_if_i.us_valid_i;

  assign l_hold_chk = check_ls_err(l_pmode, l_dbg, l_hold.cs1_fcap, l_hold.cs2_valid, l_hold.cs2_perms,
                                   l_hold.addr, l_hold.is_load, l_hold.is_cap, l_hold.data_type,
                                   l_hold.amo_flag);

  // LSU is only busy (WAIT_GNT*/WAIT_RVALID_MIS) while lsu_if holds the request (DLY0_WGNT/DLY1_WGNT)
  AssertHelpLsuBusyHeld: assert property (@(posedge clk_i) disable iff (!rst_ni)
    l_busy |-> (l_lsif == 3'h1) || (l_lsif == 3'h3));

  // DLY0_WGNT only holds early (unchecked) loads/CSR requests
  AssertHelpLsifDly0Early: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (l_lsif == 3'h1) |-> l_hold.early_load);

  // (removed AssertHelpLsifDly1NotEarly: false, CEX 8 cycles -- an early load accepted while
  //  lsif is in DLY1 goes through req_dly and is checked, so DLY1_WGNT may hold early_load=1)

  // debug_mode seen when the checked request entered the hold register (DLY1 -> DLY1_WGNT)
  logic l_dbg_hold_q;
  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) l_dbg_hold_q <= 1'b0;
    else if (kudu_top.ls_pipeline_i.lsu_if_i.xfr2hold1) l_dbg_hold_q <= l_dbg;

  // a request held in DLY1_WGNT is not yet committed, so debug_mode cannot change under it
  AssertHelpLsifHeldUncmt: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (l_lsif == 3'h3) |-> kudu_top.sbdfifo_rd_valid[0]);
  AssertHelpLsifDbgStable: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (l_lsif == 3'h3) |-> l_dbg == l_dbg_hold_q);

  // DLY1_WGNT: the held CHERI check equals the check of the held request now
  AssertHelpLsifHoldChk: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (l_lsif == 3'h3) |-> l_hold.lschk_err == l_hold_chk);

  // ---- HeldUncmt decomposition: count LS-pipeline instructions accepted by lsu_if and not yet
  //      popped by the committer (c_ls); relate it to the sbd fifo and to the LS pipeline state
  logic [3:0] c_ls, s_ls, s_cnt, s_off, w_cnt;
  logic [2:0] s_idx, w_d;
  logic       c_acc, c_pop;
  assign c_acc = kudu_top.ls_pipeline_i.lsu_if_req_valid & kudu_top.ls_pipeline_i.lspl_rdy_o;
  assign c_pop = kudu_top.cmt_lspl_rdy;
  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni)              c_ls <= 4'h0;
    else if (kudu_top.cmt_flush) c_ls <= 4'h0;
    else                      c_ls <= c_ls + 4'(c_acc) - 4'(c_pop);

  assign s_cnt = kudu_top.sbd_fifo_i.wr_ptr_q - kudu_top.sbd_fifo_i.rd_ptr_q;
  sbd_fifo_t s_mem[8];
  for (genvar i = 0; i < 8; i++) begin : g_s_mem
    assign s_mem[i] = sbd_fifo_t'(kudu_top.sbd_fifo_i.fifo_mem[i]);
  end
  always_comb begin
    s_ls = 4'h0;
    for (int i = 0; i < 8; i++) begin
      s_idx = 3'(i) - kudu_top.sbd_fifo_i.rd_ptr_q[2:0];
      s_off = 4'(s_idx);
      if ((s_off < s_cnt) && s_mem[i].pl[3]) s_ls = s_ls + 4'h1;
    end
  end
  assign w_d   = kudu_top.ls_pipeline_i.wb_fifo_i.wr_ptr_q - kudu_top.ls_pipeline_i.wb_fifo_i.rd_ptr_q;
  assign w_cnt = 4'(w_d);

  // sbd side: LS entries in the sbd fifo == accepted-not-committed LS count; fill status matches
  AssertHelpLsSbdCnt: assert property (@(posedge clk_i) disable iff (!rst_ni) s_ls == c_ls);
  AssertHelpLsSbdFill: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.sbd_fifo_i.fill_status_q[0] == (s_cnt != 4'h0)) && (s_cnt <= 4'h8));
  AssertHelpLsSbdFill1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.sbd_fifo_i.fill_status_q[1] == (s_cnt > 4'h1));
  // LSU side: every request in lsu_if / LSU / wb_fifo is still counted
  AssertHelpLsPipeCnt: assert property (@(posedge clk_i) disable iff (!rst_ni)
    c_ls >= w_cnt + 4'(kudu_top.ls_pipeline_i.load_store_unit_i.outstanding_resp_q && !l_busy) +
            4'((l_lsif == 3'h1) || (l_lsif == 3'h3)) +
            4'(l_dly_valid && ((l_lsif == 3'h2) || (l_lsif == 3'h3))));

  // LSU busy on a held checked request => it did not fault
  AssertHelpLsifHoldNoFault: assert property (@(posedge clk_i) disable iff (!rst_ni)
    l_busy && (l_lsif == 3'h3) |-> !l_hold.lschk_err.any_fault);

  // capability store data carries the cs2 tag (input, dly and hold stages)
  AssertHelpLsInTag: assert property (@(posedge clk_i) disable iff (!rst_ni)
    l_in_valid && l_pmode && l_in.is_cap && !l_in.is_load |-> l_in.wdata[MEM_TAG] == l_in.cs2_valid);
  AssertHelpLsDlyTag: assert property (@(posedge clk_i) disable iff (!rst_ni)
    l_dly_valid && l_pmode && l_dly.is_cap && !l_dly.is_load |-> l_dly.wdata[MEM_TAG] == l_dly.cs2_valid);
  AssertHelpLsHoldTag: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (l_lsif == 3'h3) && l_pmode && l_hold.is_cap && !l_hold.is_load |->
      l_hold.wdata[MEM_TAG] == (l_hold.cs2_valid && !l_hold.lschk_err.slc));

  // ===========================================================================
  // Mult pipeline: CSetBounds* path vs the fcov snapshot FIFO
  // ===========================================================================
  logic           m_ex2v, m_wbv, m_wp, m_rp;
  logic [1:0]     m_cnt;
  cheri_op_t      n_cop, h_cop;
  logic [31:0]    n_insn, h_insn;
  full_cap_t      n_d0, n_d1, h_d0, h_d1, iss_d0;
  logic           n_pm, h_pm, n_sb, h_sb, h_rndn, iss_v;
  logic [31:0]    n_len, h_len;
  setbounds_out_t h_ref;

  assign m_ex2v = kudu_top.mult_pipeline_i.ex2_valid;
  assign m_wbv  = kudu_top.mult_pipeline_i.wb_valid;
  assign m_wp   = kudu_top.mult_pipeline_i.u_fcov_sva_mult.sb_wp_q;
  assign m_rp   = kudu_top.mult_pipeline_i.u_fcov_sva_mult.sb_rp_q;
  assign m_cnt  = kudu_top.mult_pipeline_i.u_fcov_sva_mult.sb_cnt_q;

  // newest entry = sb_q[~wp]
  assign n_cop  = m_wp ? kudu_top.mult_pipeline_i.u_fcov_sva_mult.sb_q[0].cop
                       : kudu_top.mult_pipeline_i.u_fcov_sva_mult.sb_q[1].cop;
  assign n_insn = m_wp ? kudu_top.mult_pipeline_i.u_fcov_sva_mult.sb_q[0].insn
                       : kudu_top.mult_pipeline_i.u_fcov_sva_mult.sb_q[1].insn;
  assign n_d0   = m_wp ? kudu_top.mult_pipeline_i.u_fcov_sva_mult.sb_q[0].data.d0
                       : kudu_top.mult_pipeline_i.u_fcov_sva_mult.sb_q[1].data.d0;
  assign n_d1   = m_wp ? kudu_top.mult_pipeline_i.u_fcov_sva_mult.sb_q[0].data.d1
                       : kudu_top.mult_pipeline_i.u_fcov_sva_mult.sb_q[1].data.d1;
  assign n_pm   = m_wp ? kudu_top.mult_pipeline_i.u_fcov_sva_mult.sb_q[0].pmode
                       : kudu_top.mult_pipeline_i.u_fcov_sva_mult.sb_q[1].pmode;
  // oldest entry = head
  assign h_cop  = kudu_top.mult_pipeline_i.u_fcov_sva_mult.head.cop;
  assign h_insn = kudu_top.mult_pipeline_i.u_fcov_sva_mult.head.insn;
  assign h_d0   = kudu_top.mult_pipeline_i.u_fcov_sva_mult.head.data.d0;
  assign h_d1   = kudu_top.mult_pipeline_i.u_fcov_sva_mult.head.data.d1;
  assign h_pm   = kudu_top.mult_pipeline_i.u_fcov_sva_mult.head.pmode;

  assign n_sb   = n_pm & (n_cop.csetbounds | n_cop.csetboundsex | n_cop.csetboundsimm | n_cop.csetboundsrndn);
  assign h_sb   = h_pm & (h_cop.csetbounds | h_cop.csetboundsex | h_cop.csetboundsimm);
  assign h_rndn = h_pm & h_cop.csetboundsrndn;
  assign n_len  = n_cop.csetboundsimm ? 32'(n_insn[31:20]) : n_d1.addr;
  assign h_len  = h_cop.csetboundsimm ? 32'(h_insn[31:20]) : h_d1.addr;
  assign h_ref  = h_rndn ? set_bounds_rndn(h_d0, prep_bound_req(h_d0, h_len))
                         : set_bounds(h_d0, prep_bound_req(h_d0, h_len), h_cop.csetboundsex);

  // occupancy: the fcov snapshot count tracks the two pipeline stages
  AssertHelpMultCnt: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_cnt == 2'(m_ex2v) + 2'(m_wbv));
  AssertHelpMultPtr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (m_cnt == 2'd1) == (m_wp != m_rp));

  // EX2 holds the newest snapshot
  AssertHelpMultEx2Op: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_ex2v |-> kudu_top.mult_pipeline_i.ex2_reg.cheri_op == n_cop &&
               kudu_top.mult_pipeline_i.ex2_reg.insn == n_insn);
  AssertHelpMultEx2Cap: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_ex2v && n_sb |-> kudu_top.mult_pipeline_i.ex1_tfcap_q == n_d0);
  AssertHelpMultEx2Req: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_ex2v && n_sb |-> kudu_top.mult_pipeline_i.setbounds_req_q == prep_bound_req(n_d0, n_len) &&
                       kudu_top.mult_pipeline_i.req_exact_q == n_cop.csetboundsex);

  // EX2 result path: a set-bounds op is not also a cjalr/mult/div op, and the
  // set-bounds opcode bits are one-hot (so the RTL mux picks the reference function)
  logic n_rndn;
  setbounds_out_t n_ref;
  assign n_rndn = n_pm & n_cop.csetboundsrndn;
  assign n_ref  = n_rndn ? set_bounds_rndn(n_d0, prep_bound_req(n_d0, n_len))
                         : set_bounds(n_d0, prep_bound_req(n_d0, n_len), n_cop.csetboundsex);
  AssertHelpMultEx2Flags: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_ex2v && n_sb |-> !kudu_top.mult_pipeline_i.ex2_reg.flags.is_cjalr &&
                       !kudu_top.mult_pipeline_i.ex2_reg.flags.is_mult &&
                       !kudu_top.mult_pipeline_i.ex2_reg.flags.is_div &&
                       $onehot({n_cop.csetbounds, n_cop.csetboundsex, n_cop.csetboundsimm,
                                n_cop.csetboundsrndn, n_cop.crrl, n_cop.cram}));
  AssertHelpMultEx2Res: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_ex2v && n_sb |-> kudu_top.mult_pipeline_i.ex2_result == n_ref.fcap[OpW-1:0]);

  // WB holds the oldest snapshot's reference CSetBounds result
  AssertHelpMultWbRes: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_wbv && (h_sb || h_rndn) |-> kudu_top.mult_pipeline_i.wb_reg.wdata == h_ref.fcap[OpW-1:0]);

  // operand well-formedness of the issued cs1 and of the head snapshot
  assign iss_v  = kudu_top.mult_pipeline_i.us_valid_i;
  assign iss_d0 = full_cap_t'(kudu_top.mult_pipeline_i.full_data2.d0);
  AssertHelpMultIssFull: assert property (@(posedge clk_i) disable iff (!rst_ni)
    iss_v |-> iss_d0 == op2fullcap(iss_d0[OpW-1:0]));
  AssertHelpMultIssOp: assert property (@(posedge clk_i) disable iff (!rst_ni)
    iss_v |-> iss_d0[OpW-1:0] == reg2opcap(iss_d0[RegW-1:0]));
  AssertHelpMultHeadFull: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_cnt != 2'd0 |-> h_d0 == op2fullcap(h_d0[OpW-1:0]));
  AssertHelpMultHeadOp: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_cnt != 2'd0 |-> h_d0[OpW-1:0] == reg2opcap(h_d0[RegW-1:0]));

  // ===========================================================================
  // Operand well-formedness (WF: the op_cap correction bits match the reg cap)
  //   issued op data = RF read (reg2opcap, WF by construction) or a forwarded result
  // ===========================================================================
  function automatic logic h_wf(logic [OpW-1:0] x);
    return x == reg2opcap(x[RegW-1:0]);
  endfunction

  pl_fwd_t w_fwd[4];
  assign w_fwd[0] = kudu_top.alupl0_fwd_info;
  assign w_fwd[1] = kudu_top.alupl1_fwd_info;
  assign w_fwd[2] = kudu_top.lspl_fwd_info;
  assign w_fwd[3] = kudu_top.multpl_fwd_info;

  logic [7:0]       w_fv;
  logic [7:0][4:0]  w_fa;
  logic [7:0][OpW-1:0] w_fd;
  always_comb
    for (int i = 0; i < 4; i++) begin
      w_fv[2*i] = w_fwd[i].valid[0]; w_fa[2*i] = w_fwd[i].addr0; w_fd[2*i] = w_fwd[i].data0;
      w_fv[2*i+1] = w_fwd[i].valid[1]; w_fa[2*i+1] = w_fwd[i].addr1; w_fd[2*i+1] = w_fwd[i].data1;
    end

  // at most one forwarding slot per (non-zero) register: the fwd_lookup OR-merge is a mux
  logic w_uniq;
  always_comb begin
    w_uniq = 1'b1;
    for (int i = 0; i < 8; i++)
      for (int j = i+1; j < 8; j++)
        if (w_fv[i] && w_fv[j] && (w_fa[i] == w_fa[j]) && (w_fa[i] != 5'h0)) w_uniq = 1'b0;
  end
  AssertHelpWfFwdUniq: assert property (@(posedge clk_i) disable iff (!rst_ni) w_uniq);

  // strengthened (inductive) form of Uniq: AllowWaW=1, so uniqueness is kept by waw_act
  // cancelling older trackers. Track every live result tracker that can (later) forward:
  // alu0/1 WB, mult EX2 (fwd_ok) and WB, dcache fwd slot, dcache waw_fifo entries (bit5 = live)
  logic [8:0]      u_v;
  logic [8:0][4:0] u_a;
  logic [2:0]      u_cnt, u_off;
  logic [1:0]      u_idx;
  logic            u_uniq;
  assign u_cnt = kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.wr_ptr_q -
                 kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.rd_ptr_q;
  always_comb begin
    u_v[0] = kudu_top.alu_pipeline0_i.wb_fwd_valid_q;     u_a[0] = kudu_top.alu_pipeline0_i.wb_reg.rd;
    u_v[1] = kudu_top.alu_pipeline1_i.wb_fwd_valid_q;     u_a[1] = kudu_top.alu_pipeline1_i.wb_reg.rd;
    u_v[2] = kudu_top.mult_pipeline_i.ex2_valid & kudu_top.mult_pipeline_i.ex2_fwd_ok &
             kudu_top.mult_pipeline_i.ex2_reg.rf_we;     u_a[2] = kudu_top.mult_pipeline_i.ex2_reg.rd;
    u_v[3] = kudu_top.mult_pipeline_i.wb_fwd_valid_q;     u_a[3] = kudu_top.mult_pipeline_i.wb_reg.rd;
    u_v[4] = kudu_top.ls_pipeline_i.genblk1.dcache_i.fwd_info_o.valid[1];
    u_a[4] = kudu_top.ls_pipeline_i.genblk1.dcache_i.fwd_info_o.addr1;
    for (int i = 0; i < 4; i++) begin
      u_idx = 2'(i) - kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.rd_ptr_q[1:0];
      u_off = 3'(u_idx);
      u_v[5+i] = (u_off < u_cnt) && kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.fifo_mem[i][5];
      u_a[5+i] = kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.fifo_mem[i][4:0];
    end
    u_uniq = 1'b1;
    for (int i = 0; i < 9; i++)
      for (int j = i+1; j < 9; j++)
        if (u_v[i] && u_v[j] && (u_a[i] == u_a[j]) && (u_a[i] != 5'h0)) u_uniq = 1'b0;
  end
  AssertHelpUniqAll: assert property (@(posedge clk_i) disable iff (!rst_ni) u_uniq);
  // per-tracker split of UniqAll (tracker k collides with no other tracker)
  for (genvar k = 0; k < 9; k++) begin : g_uniq
    logic u_ok;
    always_comb begin
      u_ok = 1'b1;
      for (int j = 0; j < 9; j++)
        if ((j != k) && u_v[k] && u_v[j] && (u_a[k] == u_a[j]) && (u_a[k] != 5'h0)) u_ok = 1'b0;
    end
    AssertHelpUniqItem: assert property (@(posedge clk_i) disable iff (!rst_ni) u_ok);
  end
  // dcache waw_fifo occupancy is bounded by its depth
  AssertHelpUniqDcCnt: assert property (@(posedge clk_i) disable iff (!rst_ni) u_cnt <= 3'd4);

  // every valid forwarding slot carries a WF op cap
  logic w_fwd_wf;
  always_comb begin
    w_fwd_wf = 1'b1;
    for (int i = 0; i < 8; i++) if (w_fv[i] && !h_wf(w_fd[i])) w_fwd_wf = 1'b0;
  end

  // pipeline-internal WF state (WB results, fwd-valid => WB valid, mult snapshots)
  logic w_alu0, w_alu1, w_mult;
  assign w_alu0 = (!kudu_top.alu_pipeline0_i.wb_valid || h_wf(kudu_top.alu_pipeline0_i.wb_result)) &&
                  (!kudu_top.alu_pipeline0_i.wb_fwd_valid_q || kudu_top.alu_pipeline0_i.wb_valid);
  assign w_alu1 = (!kudu_top.alu_pipeline1_i.wb_valid || h_wf(kudu_top.alu_pipeline1_i.wb_result)) &&
                  (!kudu_top.alu_pipeline1_i.wb_fwd_valid_q || kudu_top.alu_pipeline1_i.wb_valid);
  assign w_mult = (!m_wbv || h_wf(kudu_top.mult_pipeline_i.wb_reg.wdata)) &&
                  (!kudu_top.mult_pipeline_i.wb_fwd_valid_q || m_wbv) &&
                  (!m_ex2v || (h_wf(n_d0[OpW-1:0]) && n_d0 == op2fullcap(n_d0[OpW-1:0]))) &&
                  (m_cnt == 2'd0 || h_wf(h_d0[OpW-1:0]));

  AssertHelpWfFwd:  assert property (@(posedge clk_i) disable iff (!rst_ni) w_fwd_wf);
  AssertHelpWfAlu0: assert property (@(posedge clk_i) disable iff (!rst_ni) w_alu0);
  AssertHelpWfAlu1: assert property (@(posedge clk_i) disable iff (!rst_ni) w_alu1);
  AssertHelpWfMult: assert property (@(posedge clk_i) disable iff (!rst_ni) w_mult);
  // joint (mutually inductive) form of the four above
  AssertHelpWfJoint: assert property (@(posedge clk_i) disable iff (!rst_ni)
    w_fwd_wf && w_alu0 && w_alu1 && w_mult);
  // the forwarded issue operands are WF (combinational consequence of Uniq + Fwd)
  AssertHelpWfIssA: assert property (@(posedge clk_i) disable iff (!rst_ni)
    h_wf(kudu_top.issuer_i.ira_op_data2_fwd.d0) && h_wf(kudu_top.issuer_i.ira_op_data2_fwd.d1));
  AssertHelpWfIssB: assert property (@(posedge clk_i) disable iff (!rst_ni)
    h_wf(kudu_top.issuer_i.irb_op_data2_fwd.d0) && h_wf(kudu_top.issuer_i.irb_op_data2_fwd.d1));

endmodule

`endif  // KUDU_FCOV_OFF
`endif  // CHERIoT
`endif  // KUDU_FV_HELPERS
