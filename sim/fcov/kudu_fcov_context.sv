// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Simultaneous pre-edge stage contents, not issue or retirement events.
module kudu_fcov_context
  import super_pkg::*;
  import kudu_fcov_pkg::*;
#(
  parameter kudu_cfg_pkg::kudu_cfg_t CFG = kudu_cfg_pkg::KuduCfg1,
  parameter bit CHERIoTEn = 1
) (
  input logic clk_i, rst_ni
);
`ifndef KUDU_FCOV_OFF
  typedef enum logic [4:0] {
    C_ALU_RI = IC_ALU_RI, C_ALU_RR = IC_ALU_RR, C_ALU_SHIFT = IC_ALU_SHIFT,
    C_BITMANIP = IC_BITMANIP, C_MUL = IC_MUL, C_DIV = IC_DIV,
    C_BRANCH = IC_BRANCH, C_JAL = IC_JAL, C_JALR = IC_JALR,
    C_LS_INT = IC_LS_INT, C_LS_CAP = IC_LS_CAP, C_AMO = IC_AMO,
    C_CSR = IC_CSR, C_SCR = IC_SCR, C_CHERI_INSPECT = IC_CHERI_INSPECT,
    C_CHERI_MODIFY = IC_CHERI_MODIFY, C_CHERI_SEAL = IC_CHERI_SEAL,
    C_SYS = IC_SYS, C_ILLEGAL = IC_ILLEGAL, EMPTY = 31
  } context_category_e;
  localparam int Alu0Wb = 0, Alu1Wb = 1, LsifDly = 2, LsuReq = 3,
                 MultEx2 = 4, MultWb = 5;

  // Low three bits retain the decoder's PL field. Only legal category/PL
  // pairs are named; faults and breakpoints can accompany any decoded PL.
  typedef enum int unsigned {
    IR_ALU_RI_ALU       = (int'(IC_ALU_RI) << 3) | int'(PL_ALU),
    IR_ALU_RR_ALU       = (int'(IC_ALU_RR) << 3) | int'(PL_ALU),
    IR_ALU_SHIFT_ALU    = (int'(IC_ALU_SHIFT) << 3) | int'(PL_ALU),
    IR_BITMANIP_ALU     = (int'(IC_BITMANIP) << 3) | int'(PL_ALU),
    IR_MUL_MULT        = (int'(IC_MUL) << 3) | int'(PL_MULT),
    IR_DIV_MULT        = (int'(IC_DIV) << 3) | int'(PL_MULT),
    IR_BRANCH_LOCAL    = (int'(IC_BRANCH) << 3) | int'(PL_LOCAL),
    IR_JAL_JAL         = (int'(IC_JAL) << 3) | int'(PL_JAL),
    IR_JALR_JALR       = (int'(IC_JALR) << 3) | int'(PL_JALR),
    IR_LS_INT_LS       = (int'(IC_LS_INT) << 3) | int'(PL_LS),
    IR_LS_CAP_LS       = (int'(IC_LS_CAP) << 3) | int'(PL_LS),
    IR_LRSC_LS         = (int'(IC_AMO) << 3) | int'(PL_LS),
    IR_CSR_LS          = (int'(IC_CSR) << 3) | int'(PL_LS),
    IR_SCR_LS          = (int'(IC_SCR) << 3) | int'(PL_LS),
    IR_CHERI_INSPECT_ALU  = (int'(IC_CHERI_INSPECT) << 3) | int'(PL_ALU),
    IR_CHERI_INSPECT_MULT = (int'(IC_CHERI_INSPECT) << 3) | int'(PL_MULT),
    IR_CHERI_MODIFY_ALU   = (int'(IC_CHERI_MODIFY) << 3) | int'(PL_ALU),
    IR_CHERI_MODIFY_MULT  = (int'(IC_CHERI_MODIFY) << 3) | int'(PL_MULT),
    IR_CHERI_SEAL_ALU   = (int'(IC_CHERI_SEAL) << 3) | int'(PL_ALU),
    IR_FENCE_LOCAL     = (int'(IC_SYS) << 3) | int'(PL_LOCAL),
    IR_EMPTY           = 152,
    IR_FAULT_LOCAL     = 160, IR_FAULT_ALU, IR_FAULT_LS,
    IR_FAULT_MULT, IR_FAULT_JAL, IR_FAULT_JALR,
    IR_DEBUG_LOCAL     = 168, IR_DEBUG_ALU, IR_DEBUG_LS,
    IR_DEBUG_MULT, IR_DEBUG_JAL, IR_DEBUG_JALR,
    IR_SYSCTL_LOCAL    = 176,
    IR_SYSCTL_LS       = 178,
    IR_CMPLX_LOCAL     = 184
  } ir_context_e;

  logic [4:0] s0_category[2], ex_category[6];
  ir_context_e ir_context[2];
  logic [3:0] special_event;
  ir_dec_t ir0_dec, ir1_dec;

  function automatic bit category_enabled(int c);
    if (c == int'(EMPTY)) return 1;
    if (c < int'(IC_ALU_RI) || c > int'(IC_ILLEGAL)) return 0;
    if (!CHERIoTEn && fcov_is_cheri_category(kudu_instr_cat_e'(c))) return 0;
    if (!CFG.RV32M && c inside {int'(IC_MUL), int'(IC_DIV)}) return 0;
    // The current decoder gates immediate bitmanip by RV32M, register forms
    // by RV32B. Either enables at least one instruction in this category.
    if (!CFG.RV32B && !CFG.RV32M && c == int'(IC_BITMANIP)) return 0;
    if (!CFG.RV32A && c == int'(IC_AMO)) return 0;
    return 1;
  endfunction

  function automatic bit ir_enabled(int value);
    case (ir_context_e'(value))
      IR_EMPTY, IR_FAULT_LOCAL, IR_FAULT_ALU, IR_FAULT_LS,
      IR_FAULT_MULT, IR_FAULT_JAL, IR_FAULT_JALR,
      IR_SYSCTL_LOCAL, IR_SYSCTL_LS: return 1;
      IR_DEBUG_LOCAL, IR_DEBUG_ALU, IR_DEBUG_LS,
      IR_DEBUG_JAL, IR_DEBUG_JALR: return CFG.DbgTriggerEn;
      IR_DEBUG_MULT: return CFG.DbgTriggerEn && (CFG.RV32M || CHERIoTEn);
      IR_CMPLX_LOCAL: return CFG.RV32A;
      IR_ALU_RI_ALU, IR_ALU_RR_ALU, IR_ALU_SHIFT_ALU, IR_BITMANIP_ALU,
      IR_MUL_MULT, IR_DIV_MULT, IR_BRANCH_LOCAL, IR_JAL_JAL, IR_JALR_JALR,
      IR_LS_INT_LS, IR_LS_CAP_LS, IR_LRSC_LS, IR_CSR_LS, IR_SCR_LS,
      IR_CHERI_INSPECT_ALU, IR_CHERI_INSPECT_MULT,
      IR_CHERI_MODIFY_ALU, IR_CHERI_MODIFY_MULT, IR_CHERI_SEAL_ALU,
      IR_FENCE_LOCAL: return category_enabled(value >> 3);
      default: return 0;
    endcase
  endfunction

  function automatic bit ir_fault(int value);
    return value inside {[int'(IR_FAULT_LOCAL):int'(IR_FAULT_JALR)]};
  endfunction

  function automatic ir_context_e classify_ir(ir_dec_t d, bit valid, bit fault);
    if (!valid) return IR_EMPTY;
    if (fault) return ir_context_e'(int'(IR_FAULT_LOCAL) | int'(d.pl_type));
    if (d.is_brkpt) return ir_context_e'(int'(IR_DEBUG_LOCAL) | int'(d.pl_type));
    if (d.sysctl.valid) return ir_context_e'(int'(IR_SYSCTL_LOCAL) | int'(d.pl_type));
    if (d.is_cmplx) return ir_context_e'(int'(IR_CMPLX_LOCAL) | int'(d.pl_type));
    return ir_context_e'((int'(fcov_instr_cat(d)) << 3) | int'(d.pl_type));
  endfunction

  function automatic bit ex_enabled(int c, int stage);
    if (!category_enabled(c)) return 0;
    if (c == int'(EMPTY)) return 1;
    case (stage)
      Alu0Wb, Alu1Wb:
        return kudu_instr_cat_e'(c) inside {
          IC_ALU_RI, IC_ALU_RR, IC_ALU_SHIFT, IC_BITMANIP, IC_JAL, IC_JALR,
          IC_CHERI_INSPECT, IC_CHERI_MODIFY, IC_CHERI_SEAL};
      LsifDly, LsuReq:
        return kudu_instr_cat_e'(c) inside {IC_LS_INT, IC_LS_CAP, IC_AMO, IC_CSR, IC_SCR};
      MultEx2, MultWb:
        return kudu_instr_cat_e'(c) inside {IC_MUL, IC_DIV, IC_CHERI_INSPECT,
                                           IC_CHERI_MODIFY} ||
               (CHERIoTEn && c == int'(IC_JALR));
      default: return 0;
    endcase
  endfunction

  function automatic kudu_instr_cat_e classify_request(lsu_req_info_t req);
    // Complex AMO requests do not save the opcode; amo_flag identifies both
    // halves as well as LR/SC. CSR/SCR requests retain the original opcode.
    if (|req.amo_flag) return IC_AMO;
    if (req.is_csr)
      return req.insn[6:0] == OPCODE_CHERI ? IC_SCR : IC_CSR;
    return req.is_cap ? IC_LS_CAP : IC_LS_INT;
  endfunction

  function automatic kudu_instr_cat_e classify_mult(
      logic [31:0] insn, cheri_op_t cheri_op, bit is_cjalr);
    ir_dec_t d;
    d = '0;
    d.insn = insn;
    d.cheri_op = cheri_op;
    d.is_jalr = is_cjalr;
    return fcov_instr_cat(d);
  endfunction

  assign ir0_dec = kudu_top.issuer_i.ir0_dec;
  assign ir1_dec = kudu_top.issuer_i.ir1_dec;
  assign ir_context[0] = classify_ir(ir0_dec, kudu_top.ir_valid[0],
                                    kudu_top.issuer_i.ir_any_err[0]);
  assign ir_context[1] = classify_ir(ir1_dec, kudu_top.ir_valid[1],
                                    kudu_top.issuer_i.ir_any_err[1]);
  assign special_event = {kudu_top.issuer_i.cmt_err_i, kudu_top.issuer_i.handle_debug,
                         kudu_top.issuer_i.handle_err, kudu_top.issuer_i.handle_irq};

  if (!CFG.IrStageBypass[1]) begin : gen_s0
    // With stage 1 present, these decoders consume s0_rdata0/1, including
    // decompression. Strip PC-breakpoint metadata from instruction categories.
    ir_dec_t dec[2];
    always_comb begin
      dec[0] = kudu_top.ir_stage_i.dec_out0;
      dec[1] = kudu_top.ir_stage_i.dec_out1;
      foreach (dec[i]) begin
        dec[i].is_brkpt = 0;
        s0_category[i] = kudu_top.ir_stage_i.s0_rd_valid[i] ?
                         fcov_instr_cat(dec[i]) : EMPTY;
      end
    end

    covergroup cg_frontend @(posedge clk_i iff rst_ni);
      option.per_instance = 1;
      option.name = "FC_MA_CONTEXT.frontend";
      cp_s0_rdata0: coverpoint context_category_e'(s0_category[0]) {
        bins category[] = {[C_ALU_RI:C_ILLEGAL], EMPTY}
          with (category_enabled(int'(item)));
      }
      cp_s0_rdata1: coverpoint context_category_e'(s0_category[1]) {
        bins category[] = {[C_ALU_RI:C_ILLEGAL], EMPTY}
          with (category_enabled(int'(item)));
      }
      cp_ir0: coverpoint ir_context[0] {
        bins category_pl[] = {[IR_ALU_RI_ALU:IR_CMPLX_LOCAL]} with (ir_enabled(int'(item)));
      }
      cp_ir1: coverpoint ir_context[1] {
        bins category_pl[] = {[IR_ALU_RI_ALU:IR_CMPLX_LOCAL]} with (ir_enabled(int'(item)));
      }
      cp_special_event: coverpoint special_event { bins mask[] = {[0:15]}; }
      x_s0_ir_special: cross cp_s0_rdata0, cp_s0_rdata1, cp_ir0, cp_ir1, cp_special_event {
        ignore_bins s0_order = binsof(cp_s0_rdata0) intersect {EMPTY} &&
                              !binsof(cp_s0_rdata1) intersect {EMPTY};
        ignore_bins ir_order = binsof(cp_ir0) intersect {IR_EMPTY} &&
                              !binsof(cp_ir1) intersect {IR_EMPTY};
        // handle_err is exactly ir_valid[0] && ir_any_err[0].
        ignore_bins error_mismatch = x_s0_ir_special with
          (((cp_special_event & 2) != 0) != ir_fault(int'(cp_ir0)));
      }
    endgroup
    cg_frontend u_cg_frontend = new();

    AssertS0Order: assert property (@(posedge clk_i) disable iff (!rst_ni)
      kudu_top.ir_stage_i.s0_rd_valid[1] |-> kudu_top.ir_stage_i.s0_rd_valid[0])
      else $error("FCOV context: s0_rdata1 valid without s0_rdata0");
  end else begin : gen_no_s0
    assign s0_category = '{default: EMPTY};
  end

  always_comb begin
    ex_category[Alu0Wb] = kudu_top.alu_pipeline0_i.wb_valid ?
      kudu_top.alu_pipeline0_i.u_fcov_alu.wb_category : EMPTY;
    ex_category[Alu1Wb] = kudu_top.alu_pipeline1_i.wb_valid ?
      kudu_top.alu_pipeline1_i.u_fcov_alu.wb_category : EMPTY;
    // req_dly_valid also retains copies of bypassed early requests in IDLE
    // and DLY0_WGNT. Only DLY1 / DLY1_WGNT own delayed queued work.
    ex_category[LsifDly] =
      kudu_top.ls_pipeline_i.lsu_if_i.req_dly_valid &&
      kudu_top.ls_pipeline_i.lsu_if_i.lsif_fsm_q inside {3'd2, 3'd3} ?
      classify_request(kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q) : EMPTY;
    ex_category[LsuReq] = kudu_top.ls_pipeline_i.load_store_unit_i.outstanding_resp_q ?
      classify_request(kudu_top.ls_pipeline_i.load_store_unit_i.lsu_req_info_q) : EMPTY;
    ex_category[MultEx2] = kudu_top.mult_pipeline_i.ex2_valid ?
      classify_mult(kudu_top.mult_pipeline_i.ex2_reg.insn,
                    kudu_top.mult_pipeline_i.ex2_reg.cheri_op,
                    kudu_top.mult_pipeline_i.ex2_reg.flags.is_cjalr) : EMPTY;
    ex_category[MultWb] = kudu_top.mult_pipeline_i.wb_valid ?
      classify_mult(kudu_top.mult_pipeline_i.wb_reg.insn,
                    kudu_top.mult_pipeline_i.wb_reg.cheri_op,
                    kudu_top.mult_pipeline_i.wb_reg.flags.is_cjalr) : EMPTY;
  end

  for (genvar i = 0; i < 6; i++) begin : gen_ex
    localparam string StageName = i == Alu0Wb ? "alu0_wb" : i == Alu1Wb ? "alu1_wb" :
      i == LsifDly ? "lsif_req_dly" : i == LsuReq ? "lsu_req" :
      i == MultEx2 ? "mult_ex2" : "mult_wb";
    covergroup cg_execution @(posedge clk_i iff rst_ni);
      option.per_instance = 1;
      option.name = {"FC_MA_CONTEXT.", StageName};
      cp_ir0: coverpoint ir_context[0] {
        bins category_pl[] = {[IR_ALU_RI_ALU:IR_CMPLX_LOCAL]} with (ir_enabled(int'(item)));
      }
      cp_ir1: coverpoint ir_context[1] {
        bins category_pl[] = {[IR_ALU_RI_ALU:IR_CMPLX_LOCAL]} with (ir_enabled(int'(item)));
      }
      cp_special_event: coverpoint special_event { bins mask[] = {[0:15]}; }
      cp_ex_resident: coverpoint context_category_e'(ex_category[i]) {
        bins category[] = {[C_ALU_RI:C_ILLEGAL], EMPTY}
          with (ex_enabled(int'(item), i));
      }
      x_ir_special_ex: cross cp_ir0, cp_ir1, cp_special_event, cp_ex_resident {
        ignore_bins ir_order = binsof(cp_ir0) intersect {IR_EMPTY} &&
                              !binsof(cp_ir1) intersect {IR_EMPTY};
        ignore_bins error_mismatch = x_ir_special_ex with
          (((cp_special_event & 2) != 0) != ir_fault(int'(cp_ir0)));
      }
    endgroup
    cg_execution u_cg_execution = new();

    AssertExCategory: assert property (@(posedge clk_i) disable iff (!rst_ni)
      ex_enabled(int'(ex_category[i]), i))
      else $error("FCOV context: unexpected category in %s", StageName);
  end

  AssertIr0Category: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ir_enabled(int'(ir_context[0])))
    else $error("FCOV context: unexpected IR0 category/PL");
  AssertIr1Category: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ir_enabled(int'(ir_context[1])))
    else $error("FCOV context: unexpected IR1 category/PL");
  AssertIrOrder: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.ir_valid[1] |-> kudu_top.ir_valid[0])
    else $error("FCOV context: IR1 valid without IR0");
`endif
endmodule
