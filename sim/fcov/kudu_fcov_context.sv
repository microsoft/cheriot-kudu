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
  // EX-resident axis: every RV32 ALU form (RI/RR/shift/bitmanip/LUI) is
  // C_ALU, the AUIPC opcode (AUIPCC in PMODE=1) is separate, CSeal/CUnseal
  // join C_CHERI_MODIFY, and loads and stores are split.
  typedef enum logic [4:0] {
    C_ALU, C_AUIPCC, C_MUL, C_DIV, C_BRANCH, C_JAL, C_JALR,
    C_LOAD_INT, C_STORE_INT, C_LOAD_CAP, C_STORE_CAP, C_AMO,
    C_CSR, C_SCR, C_CHERI_INSPECT, C_CHERI_MODIFY, C_SYS, C_ILLEGAL,
    EMPTY = 31
  } context_category_e;
  // Coarser S0 axis: execution class only. All RV32 ALU forms, AUIPC(C) and
  // CHERI inspect/modify/seal operations are S_ALU; CSPECIALRW is S_CSR.
  typedef enum logic [3:0] {
    S_ALU, S_MULDIV, S_BRANCH, S_JAL, S_JALR, S_LS, S_AMO, S_CSR, S_SYS,
    S_ILLEGAL, S_EMPTY = 15
  } s0_category_e;
  localparam int Alu0Wb = 0, Alu1Wb = 1, LsifDly = 2, LsuReq = 3,
                 MultEx2 = 4, MultWb = 5;

  typedef enum logic [3:0] {
    IR_LOCAL = 4'(PL_LOCAL), IR_ALU = 4'(PL_ALU), IR_LS = 4'(PL_LS),
    IR_MULT = 4'(PL_MULT), IR_JAL = 4'(PL_JAL), IR_JALR = 4'(PL_JALR),
    IR_EMPTY = 8, IR_DIV = 9
  } ir_context_e;

  logic [3:0] s0_category[2];
  logic [4:0] ex_category[6];
  logic [5:0] ex_cmplx_amo;
  ir_context_e ir_context[2];
  logic [4:0] special_event;
  ir_dec_t ir0_dec, ir1_dec;
  logic [1:0] ir_cmplx_amo, ir_err;

  function automatic bit category_enabled(int c);
    if (c == int'(EMPTY)) return 1;
    if (c < int'(C_ALU) || c > int'(C_ILLEGAL)) return 0;
    if (!CHERIoTEn && c inside {int'(C_LOAD_CAP), int'(C_STORE_CAP), int'(C_SCR),
                                int'(C_CHERI_INSPECT), int'(C_CHERI_MODIFY)})
      return 0;
    if (!CFG.RV32M && c inside {int'(C_MUL), int'(C_DIV)}) return 0;
    if (!CFG.RV32A && c == int'(C_AMO)) return 0;
    return 1;
  endfunction

  function automatic bit s0_enabled(int c);
    if (c == int'(S_EMPTY)) return 1;
    if (c < int'(S_ALU) || c > int'(S_ILLEGAL)) return 0;
    if (!CFG.RV32M && c == int'(S_MULDIV)) return 0;
    if (!CFG.RV32A && c == int'(S_AMO)) return 0;
    return 1;
  endfunction

  function automatic s0_category_e s0_cat(kudu_instr_cat_e c);
    case (c)
      IC_ALU_RI, IC_ALU_RR, IC_ALU_SHIFT, IC_BITMANIP,
      IC_CHERI_INSPECT, IC_CHERI_MODIFY, IC_CHERI_SEAL: return S_ALU;
      IC_MUL, IC_DIV:      return S_MULDIV;
      IC_BRANCH:           return S_BRANCH;
      IC_JAL:              return S_JAL;
      IC_JALR:             return S_JALR;
      IC_LS_INT, IC_LS_CAP: return S_LS;
      IC_AMO:              return S_AMO;
      IC_CSR, IC_SCR:      return S_CSR;
      IC_SYS:              return S_SYS;
      default:             return S_ILLEGAL;
    endcase
  endfunction

  // Maps a non-memory pipeline's detailed category onto the EX context axis
  // (LSU-resident work is classified from its saved request). auipc is the
  // AUIPC opcode, decoded as cheri_op.auipcc (CHERI_MODIFY) when PMODE=1.
  function automatic context_category_e context_cat(kudu_instr_cat_e c, bit auipc);
    if (auipc && c != IC_ILLEGAL) return C_AUIPCC;
    case (c)
      IC_ALU_RI, IC_ALU_RR, IC_ALU_SHIFT, IC_BITMANIP: return C_ALU;
      IC_MUL:           return C_MUL;
      IC_DIV:           return C_DIV;
      IC_BRANCH:        return C_BRANCH;
      IC_JAL:           return C_JAL;
      IC_JALR:          return C_JALR;
      IC_AMO:           return C_AMO;
      IC_CSR:           return C_CSR;
      IC_SCR:           return C_SCR;
      IC_CHERI_INSPECT: return C_CHERI_INSPECT;
      IC_CHERI_MODIFY,
      IC_CHERI_SEAL:    return C_CHERI_MODIFY;
      IC_SYS:           return C_SYS;
      default:          return C_ILLEGAL;
    endcase
  endfunction

  function automatic bit ir_enabled(int value);
    return value inside {int'(IR_LOCAL), int'(IR_ALU), int'(IR_LS), int'(IR_MULT),
                         int'(IR_JAL), int'(IR_JALR), int'(IR_DIV), int'(IR_EMPTY)};
  endfunction

  function automatic ir_context_e classify_ir(ir_dec_t d, bit valid);
    if (!valid) return IR_EMPTY;
    // PL_MULT also carries CHERI operations; bit 14 alone is not a DIV decode.
    if (d.pl_type == PL_MULT && d.insn[6:0] == OPCODE_OP &&
        d.insn[31:25] == 7'b0000001 && d.insn[14])
      return IR_DIV;
    return ir_context_e'(d.pl_type);
  endfunction

  function automatic bit ex_enabled(int c, int stage);
    if (!category_enabled(c)) return 0;
    if (c == int'(EMPTY)) return 1;
    case (stage)
      Alu0Wb, Alu1Wb:
        return context_category_e'(c) inside {
          C_ALU, C_AUIPCC, C_JAL, C_JALR, C_CHERI_INSPECT, C_CHERI_MODIFY};
      LsifDly, LsuReq:
        return context_category_e'(c) inside {C_LOAD_INT, C_STORE_INT, C_LOAD_CAP,
                                              C_STORE_CAP, C_AMO, C_CSR, C_SCR};
      MultEx2, MultWb:
        return context_category_e'(c) inside {C_MUL, C_DIV, C_CHERI_INSPECT,
                                              C_CHERI_MODIFY} ||
               (CHERIoTEn && c == int'(C_JALR));
      default: return 0;
    endcase
  endfunction

  function automatic context_category_e classify_request(lsu_req_info_t req);
    // Complex AMO requests do not save the opcode; amo_flag identifies both
    // halves as well as LR/SC. CSR/SCR requests retain the original opcode.
    if (|req.amo_flag) return C_AMO;
    if (req.is_csr)
      return req.insn[6:0] == OPCODE_CHERI ? C_SCR : C_CSR;
    if (req.is_cap) return req.is_load ? C_LOAD_CAP : C_STORE_CAP;
    return req.is_load ? C_LOAD_INT : C_STORE_INT;
  endfunction

  function automatic context_category_e classify_mult(
      logic [31:0] insn, cheri_op_t cheri_op, bit is_cjalr);
    ir_dec_t d;
    d = '0;
    d.insn = insn;
    d.cheri_op = cheri_op;
    d.is_jalr = is_cjalr;
    return context_cat(fcov_instr_cat(d), 0);
  endfunction

  assign ir0_dec = kudu_top.issuer_i.ir0_dec;
  assign ir1_dec = kudu_top.issuer_i.ir1_dec;
  assign ir_context[0] = classify_ir(ir0_dec, kudu_top.ir_valid[0]);
  assign ir_context[1] = classify_ir(ir1_dec, kudu_top.ir_valid[1]);
  assign ir_cmplx_amo = kudu_top.ir_valid & {ir1_dec.is_cmplx, ir0_dec.is_cmplx};
  assign ir_err = kudu_top.ir_valid & kudu_top.issuer_i.ir_any_err;
  assign special_event = {kudu_top.issuer_i.cmt_err_i, kudu_top.issuer_i.handle_debug,
                         ir_err[1], ir_err[0], kudu_top.issuer_i.handle_irq};

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
                         s0_cat(fcov_instr_cat(dec[i])) : S_EMPTY;
      end
    end

    covergroup cg_frontend @(posedge clk_i iff rst_ni);
      option.per_instance = 1;
      option.name = "FC_MA_CONTEXT.frontend";
      cp_s0_rdata0: coverpoint s0_category_e'(s0_category[0]) {
        bins category[] = {[S_ALU:S_ILLEGAL], S_EMPTY}
          with (s0_enabled(int'(item)));
      }
      cp_s0_rdata1: coverpoint s0_category_e'(s0_category[1]) {
        bins category[] = {[S_ALU:S_ILLEGAL], S_EMPTY}
          with (s0_enabled(int'(item)));
      }
      cp_ir0: coverpoint ir_context[0] {
        bins pipeline[] = {[IR_LOCAL:IR_JALR], IR_DIV, IR_EMPTY};
      }
      cp_ir1: coverpoint ir_context[1] {
        bins pipeline[] = {[IR_LOCAL:IR_JALR], IR_DIV, IR_EMPTY};
      }
      cp_special_event: coverpoint special_event {
        bins none = {5'b00000};
        wildcard bins irq = {5'b????1};
        wildcard bins ir0_err = {5'b???1?};
        wildcard bins ir1_err = {5'b??1??};
        wildcard bins debug = {5'b?1???};
        wildcard bins commit_error = {5'b1????};
      }
      cp_special_event_value: coverpoint special_event { bins mask[] = {[0:31]}; }
      x_s0_s1: cross cp_s0_rdata0, cp_s0_rdata1, cp_ir0, cp_ir1 {
        ignore_bins s0_order = binsof(cp_s0_rdata0) intersect {S_EMPTY} &&
                              !binsof(cp_s0_rdata1) intersect {S_EMPTY};
        ignore_bins ir_order = binsof(cp_ir0) intersect {IR_EMPTY} &&
                              !binsof(cp_ir1) intersect {IR_EMPTY};
      }
    endgroup
    cg_frontend u_cg_frontend = new();

    AssertS0Order: assert property (@(posedge clk_i) disable iff (!rst_ni)
      kudu_top.ir_stage_i.s0_rd_valid[1] |-> kudu_top.ir_stage_i.s0_rd_valid[0])
      else $error("FCOV context: s0_rdata1 valid without s0_rdata0");
  end else begin : gen_no_s0
    assign s0_category = '{default: S_EMPTY};
  end

  always_comb begin
    ex_cmplx_amo = '0;
    ex_category[Alu0Wb] = kudu_top.alu_pipeline0_i.wb_valid ?
      context_cat(kudu_top.alu_pipeline0_i.u_fcov_alu.wb_category,
                  kudu_top.alu_pipeline0_i.u_fcov_alu.wb_auipc) : EMPTY;
    ex_category[Alu1Wb] = kudu_top.alu_pipeline1_i.wb_valid ?
      context_cat(kudu_top.alu_pipeline1_i.u_fcov_alu.wb_category,
                  kudu_top.alu_pipeline1_i.u_fcov_alu.wb_auipc) : EMPTY;
    // req_dly_valid also retains copies of bypassed early requests in IDLE
    // and DLY0_WGNT. Only DLY1 / DLY1_WGNT own delayed queued work.
    ex_category[LsifDly] =
      kudu_top.ls_pipeline_i.lsu_if_i.req_dly_valid &&
      kudu_top.ls_pipeline_i.lsu_if_i.lsif_fsm_q inside {3'd2, 3'd3} ?
      classify_request(kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q) : EMPTY;
    ex_category[LsuReq] = kudu_top.ls_pipeline_i.load_store_unit_i.outstanding_resp_q ?
      classify_request(kudu_top.ls_pipeline_i.load_store_unit_i.lsu_req_info_q) : EMPTY;
    // C_AMO also contains LR/SC. Only the upper flags identify complex AMO phases.
    ex_cmplx_amo[LsifDly] = ex_category[LsifDly] == C_AMO &&
      (|kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q.amo_flag[3:2]);
    ex_cmplx_amo[LsuReq] = ex_category[LsuReq] == C_AMO &&
      (|kudu_top.ls_pipeline_i.load_store_unit_i.lsu_req_info_q.amo_flag[3:2]);
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
        bins pipeline[] = {[IR_LOCAL:IR_JALR], IR_DIV, IR_EMPTY};
      }
      cp_ir1: coverpoint ir_context[1] {
        bins pipeline[] = {[IR_LOCAL:IR_JALR], IR_DIV, IR_EMPTY};
      }
      cp_special_event: coverpoint special_event {
        bins none = {5'b00000};
        wildcard bins irq = {5'b????1};
        wildcard bins ir0_err = {5'b???1?};
        wildcard bins ir1_err = {5'b??1??};
        wildcard bins debug = {5'b?1???};
        wildcard bins commit_error = {5'b1????};
      }
      cp_special_event_value: coverpoint special_event { bins mask[] = {[0:31]}; }
      cp_ex_resident: coverpoint context_category_e'(ex_category[i]) {
        bins category[] = {[C_ALU:C_ILLEGAL], EMPTY}
          with (ex_enabled(int'(item), i));
      }
      x_ir_special_ex: cross cp_ir0, cp_ir1, cp_special_event, cp_ex_resident
          iff (!(|ir_cmplx_amo) && !ex_cmplx_amo[i]) {
        ignore_bins ir_order = binsof(cp_ir0) intersect {IR_EMPTY} &&
                              !binsof(cp_ir1) intersect {IR_EMPTY};
        ignore_bins error_without_ir0 = binsof(cp_special_event.ir0_err) &&
                                        binsof(cp_ir0) intersect {IR_EMPTY};
        ignore_bins error_without_ir1 = binsof(cp_special_event.ir1_err) &&
                                        binsof(cp_ir1) intersect {IR_EMPTY};
        // Commit errors only come from LSU responses. The faulting response
        // clears outstanding_resp_q and blocks ds_rdy_i until cmt_flush. Paired
        // with AssertLsuReqNoCmtErr.
        illegal_bins lsu_commit_error = (binsof(cp_special_event.commit_error) &&
                                         binsof(cp_ex_resident)) with
                                        (i == LsuReq && cp_ex_resident != EMPTY);
      }
    endgroup
    cg_execution u_cg_execution = new();

    AssertExCategory: assert property (@(posedge clk_i) disable iff (!rst_ni)
      ex_enabled(int'(ex_category[i]), i))
      else $error("FCOV context: unexpected category in %s", StageName);
  end

  AssertIr0Category: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ir_enabled(int'(ir_context[0])))
    else $error("FCOV context: unexpected IR0 pipeline");
  AssertIr1Category: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ir_enabled(int'(ir_context[1])))
    else $error("FCOV context: unexpected IR1 pipeline");
  AssertIrOrder: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.ir_valid[1] |-> kudu_top.ir_valid[0])
    else $error("FCOV context: IR1 valid without IR0");
  AssertLsuReqNoCmtErr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.cmt_err_i |->
      !kudu_top.ls_pipeline_i.load_store_unit_i.outstanding_resp_q)
    else $error("FCOV context: LSU request outstanding during commit error");
`endif
endmodule
