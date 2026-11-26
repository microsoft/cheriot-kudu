// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Stage-2 invariants (README section 5). Included last inside kudu_e2e_top.
// They are asserted (and proven) like any other property, then assumed by
// the induction steps of the end-to-end checks.
//
// Groups:
//   Inv_A*  Kudu-internal reachable states under the harness restrictions
//   Inv_B*  harness spec_past_* legality; Harness_PastValidSoon bounds the
//           !past_valid window so induction may assume past_valid
//   Inv_C*  scoreboard follower vs sbd_fifo
//   Inv_D*  LS follower vs lsu_if/LSU, LSU vs bus
//   Inv_E*  CSR state vs spec_past_*
//   Inv_F*  Kudu trap decisions vs spec traps

`define KLSIF dut.ls_pipeline_i.lsu_if_i
`define KLSP dut.ls_pipeline_i
`define KCPX  dut.comlx_unit_i

////////////////////// Group B: !past_valid window //////////////////////

// past_valid is set by the first non-shadow step, which comes within a few
// cycles of reset. Induction may then assume past_valid, provided BMC from
// reset covers PastValidK + the induction depth.
localparam int PastValidK = 16;

logic [4:0] inv_cyc_q;
always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni)                 inv_cyc_q <= '0;
  else if (inv_cyc_q != 5'h1f) inv_cyc_q <= inv_cyc_q + 5'd1;
end

Harness_PastValidSoon: assert property (inv_cyc_q >= 5'(PastValidK) |-> past_valid);

Inv_B_PastPriv: assert property (past_priv inside {Machine, User});
// mstatus.MPP is WARL {M, U}; an MRET with MPP = S would leave past_priv = S.
Inv_B_PastMpp:  assert property (past_mstatus.mpp inside {2'b11, 2'b00});
// mie holds only the interrupt bits Kudu implements (irqsToMInterrupts).
Inv_B_PastMie:  assert property ((past_mie & ~32'h7fff_0888) == 32'h0);
// A tagged capability is one software can hold: it survives the memory
// encoding unchanged (E in {0..14, 24}, T[8] derived from B, representable
// permissions) and is well formed (0 <= base <= top <= 2^32). Sail's
// capability ops preserve this and loads get it from Mem_RdataCapWF. Without
// it a CJALR to such a register decodes to different bounds in Kudu's PCC and
// the spec's.
function automatic logic inv_cap_ok(t_Capability c);
  return !c.tag || (cap_eq(encodeDecodePermsOf(c), c) && cap_well_formed(c));
endfunction
// Tagged or not, a register value survives Sail's wC encode/decode round trip:
// E != 31 (encodes as denormal E = 0) and, unless E = 0, T[8] is the implicit
// top bit B[8] ^ (T[7:0] < B[7:0]) ^ 1. Kudu's mem2regcap derives the same bit
// and its capability ops keep it, but its ALU does not renormalise.
function automatic logic inv_cap_canon(t_Capability c);
  return (c.E != 5'd31) &&
         ((c.E == 5'd0) || (c.T[8] == (c.B[8] ^ (c.T[7:0] < c.B[7:0]) ^ 1'b1)));
endfunction
for (genvar i = 1; i < 32; i++) begin : g_inv_regwf
  Inv_B_RegWF: assert property (inv_cap_ok(past_regs[i]) && inv_cap_canon(past_regs[i]));
end
// The spec's main_inner clears nextPCC.B[8] when E = 24 (inv_pcc_norm), so T[8]
// is not tied to B[8] there.
Inv_B_PccWF:    assert property (inv_cap_ok(past_pcc) && (inv_cap_canon(past_pcc) || (past_pcc.E == 5'd24)));
// SCRs are read back into registers (CSpecialR), so they are canonical too,
// except MEPCC with E = 24: a trap copies PCC, which is not canonical after
// a trap to an MTCC with B[8] = 1 (Inv_B_PccWF). Sail's wC renormalises it
// on a CSpecialR read.
Inv_B_CsrWF:    assert property (inv_cap_ok(past_mtvec) && inv_cap_ok(past_mepc) &&
                                 inv_cap_ok(past_mscratchc) && inv_cap_ok(past_mtdc) &&
                                 inv_cap_canon(past_mtvec) &&
                                 (inv_cap_canon(past_mepc) || (past_mepc.E == 5'd24)) &&
                                 inv_cap_canon(past_mscratchc) && inv_cap_canon(past_mtdc));
// A tagged PCC is unsealed and executable (Sail's fetch check raises
// internal_error otherwise): CJALR checks it, and MTCC / MEPCC writes clear
// the tag of a sealed or non-executable value.
function automatic logic inv_xcap_ok(t_Capability c);
  return !c.tag || ((c.otype == '0) && c.permit_execute);
endfunction
Inv_B_PccX: assert property (inv_xcap_ok(past_pcc) && inv_xcap_ok(past_mtvec) && inv_xcap_ok(past_mepc));
// MTCC writes force address[1:0] = 0 (direct mode); prepare_trap_vector
// raises internal_error otherwise.
Inv_B_MtvecAlign: assert property (past_mtvec.address[1:0] == 2'b00);

////////////////////// Group A: Kudu-internal states //////////////////////

localparam logic [15:0] CtrlLegal = (16'h1 << super_pkg::CSM_RESET)         |
                                    (16'h1 << super_pkg::CSM_BOOT_SET)      |
                                    (16'h1 << super_pkg::CSM_DECODE)        |
                                    (16'h1 << super_pkg::CSM_CMT_FLUSH)     |
                                    (16'h1 << super_pkg::CSM_WAIT_TRVK)     |
                                    (16'h1 << super_pkg::CSM_WAIT_CMT0)     |
                                    (16'h1 << super_pkg::CSM_ISSUE_SPECIAL) |
                                    (16'h1 << super_pkg::CSM_WAIT_FINAL)    |
                                    (16'h1 << super_pkg::CSM_WAIT_CMPLX)    |
                                    (16'h1 << super_pkg::CSM_SLEEP);

Inv_A_CtrlOneHot: assert property ($onehot(`KISS.ctrl_fsm_cs) && ((`KISS.ctrl_fsm_cs & ~CtrlLegal) == '0));
// Boot (which re-initialises mtvec) completes before the first spec step.
Inv_A_BootDone: assert property (past_valid |->
  !`KISS.ctrl_fsm_cs[super_pkg::CSM_RESET] && !`KISS.ctrl_fsm_cs[super_pkg::CSM_BOOT_SET]);
Inv_A_NoCmplxSt:  assert property (!`KISS.ctrl_fsm_cs[super_pkg::CSM_WAIT_CMPLX]);
Inv_A_SpCase:     assert property (`KISS.special_case_q inside {super_pkg::NULL, super_pkg::EXEC,
                                                                super_pkg::SYSCTL, super_pkg::IRQ});
Inv_A_NoDbgMode:  assert property (!`KISS.debug_mode_q && !`KISS.step_req_q);
Inv_A_Dcsr:       assert property (!`KCSR.dcsr_q.step && !`KCSR.dcsr_q.ebreakm && !`KCSR.dcsr_q.ebreaku);
// A trap taken at ISSUE_SPECIAL (exec error, irq, ecall/ebreak) pushes no
// scoreboard entry: ecall/ebreak decode to PL_LOCAL, and a SYSCTL special
// still has its instruction at ir0 (it is popped only at ISSUE_SPECIAL).
Inv_A_EcallLocalA: assert property ((`KDUT.ira_dec.sysctl.ecall || `KDUT.ira_dec.sysctl.ebrk)
                                    |-> `KDUT.ira_dec.sysctl.valid && (`KDUT.ira_dec.pl_type == super_pkg::PL_LOCAL));
Inv_A_EcallLocalB: assert property ((`KDUT.irb_dec.sysctl.ecall || `KDUT.irb_dec.sysctl.ebrk)
                                    |-> `KDUT.irb_dec.sysctl.valid && (`KDUT.irb_dec.pl_type == super_pkg::PL_LOCAL));
// special_case_q is latched on leaving WAIT_CMT0, when ir0 is still held.
Inv_A_SpSysctl:   assert property (st_special && (`KISS.special_case_q == super_pkg::SYSCTL)
                                   |-> `KDUT.ir_valid[0] && (`KISS.ir0_dec.sysctl == `KISS.sysctl_q));
Inv_A_SpTrapLocal: assert property (st_special && `KDUT.csr_save_cause |-> !(|`KISS.ir0_pl_sel[4:1]));
Inv_A_Priv:       assert property (`KCSR.priv_lvl_q inside {2'b11, 2'b00});
Inv_A_Mpp:        assert property (`KCSR.mstatus_q.mpp inside {2'b11, 2'b00});
// The CSR request held in the LSU came through Env_InsnScope at issue.
// is_csr comes from ir_decoder: Zicsr (SYSTEM, funct3 != 0) or CSpecialRW.
function automatic logic inv_csr_ok(logic [31:0] insn);
  return (((insn[6:0] == 7'h73) && (insn[14:12] != 3'd0)) ||
          ((insn[6:0] == 7'h5b) && (insn[14:12] == 3'd0) && (insn[31:25] == 7'h01))) &&
         insn_in_scope(insn, 1'b0, 16'h0);
endfunction
// ir_decoder sysctl.csrw: a Zicsr write (csrrw*, or csrrs*/csrrc* with a
// non-zero rs1/uimm) to mstatus or mie.
function automatic logic inv_wmie(logic [31:0] insn);
  return (insn[6:0] == 7'h73) && (insn[14:12] != 3'd0) && !(insn[13] && (insn[19:15] == 5'd0)) &&
         ((insn[31:20] == 12'h300) || (insn[31:20] == 12'h304));
endfunction
for (genvar k = 0; k < 2; k++) begin : g_inv_ir
  Inv_A_IrCsr: assert property (`KDUT.ir_valid[k] && g_ir_scope[k].ir_dec.is_csr |->
                                inv_csr_ok(g_ir_scope[k].ir_dec.insn));

  // The s1_fifo slots hold ir_decoder outputs. Re-decode the stored
  // instruction word and compare every field that depends on it alone (the
  // CHERI fetch checks also depend on PCC, ptaken/ptarget on prediction).
  super_pkg::ir_dec_t d, r;
  super_pkg::ir_reg_t rin;
  assign d = g_ir_scope[k].ir_dec;
  always_comb begin
    rin                     = super_pkg::NULL_IR_REG;
    rin.insn                = d.insn;
    rin.pc                  = d.pc;
    rin.is_comp             = d.is_comp;
    rin.ferr2w              = d.ferr2w;
    rin.c_insn              = d.c_insn;
    rin.errs.illegal_c_insn = d.errs.illegal_c_insn;
    rin.errs.fetch_err      = d.errs.fetch_err;
  end
  ir_decoder #(
    .CHERIoTEn (1'b1),
    .RV32M     (KuduE2eCfg.RV32M),
    .RV32B     (KuduE2eCfg.RV32B),
    .RV32A     (KuduE2eCfg.RV32A)
  ) u_redec (
    .clk_i         (clk_i),
    .rst_ni        (rst_ni),
    .cheri_pmode_i (1'b1),
    .debug_mode_i  (1'b0),
    .pcc_cap_i     ('0),
    .ir_reg_i      (rin),
    .brkpt_match_i (1'b0),
    .ir_dec_o      (r)
  );
  Inv_A_IrDec: assert property (`KDUT.ir_valid[k] |->
    (d.is_branch == r.is_branch) && (d.is_jal == r.is_jal) && (d.is_jalr == r.is_jalr) &&
    (d.is_csr == r.is_csr) && (d.pl_type == r.pl_type) && (d.rs1 == r.rs1) &&
    (d.rs2 == r.rs2) && (d.rd == r.rd) && (d.rf_ren == r.rf_ren) && (d.rf_we == r.rf_we) &&
    (d.sysctl == r.sysctl) && (d.rs_cheri == r.rs_cheri) && (d.cheri_op == r.cheri_op) &&
    (d.is_cmplx == r.is_cmplx) && (d.errs.illegal_insn == r.errs.illegal_insn) &&
    (d.btarget == r.btarget) && (d.pc_nxt == r.pc_nxt));
  Inv_A_IrAnyErr: assert property (`KDUT.ir_valid[k] |-> d.any_err == (|d.errs));
  // asr_vio is PCC-dependent but set only for mret (u_redec has PCC = 0, so
  // its asr_vio is exactly "is mret").
  Inv_A_IrAsr:    assert property (`KDUT.ir_valid[k] && d.errs.asr_vio |-> r.errs.asr_vio);

  // The stored words came through compressed_decoder: is_comp follows the
  // 16-bit parcel (fetch_fifo64 comp_flag), insn is its expansion and c_insn
  // its low half. The spec executes c_insn when is_comp.
  super_pkg::ir_reg_t cin, cout;
  always_comb begin
    cin         = super_pkg::NULL_IR_REG;
    cin.insn    = d.is_comp ? {16'h0, d.c_insn} : d.insn;
    cin.is_comp = d.is_comp;
  end
  compressed_decoder #(.CHERIoTEn (1'b1)) u_recdec (
    .clk_i         (clk_i),
    .rst_ni        (rst_ni),
    .cheri_pmode_i (1'b1),
    .instr_i       (cin),
    .instr_o       (cout)
  );
  Inv_A_IrComp: assert property (`KDUT.ir_valid[k] |->
    (d.is_comp == (d.c_insn[1:0] != 2'b11)) && (d.c_insn == cout.c_insn) &&
    (d.errs.illegal_c_insn == cout.errs.illegal_c_insn) &&
    // Where no expansion case fires, the decoder forwards the fetched word,
    // whose upper half is unknown here; elsewhere (even if illegal) it expands.
    ((cout.insn == cin.insn) ? (d.insn[15:0] == d.c_insn) : (d.insn == cout.insn)));
end
// The CHERI fetch checks latched in ir0/ir1 were made by ir_decoder against
// the IR-stage PCC (ir_pcc_cap_q under PredictRA). They are those of the PCC
// each instruction issues under: for ir0 the EX1 PCC (a CJALR sets it in its
// issue cycle); for ir1 behind a predicted CJALR (ptaken, ptarget = the full
// return cap, as ir_stage predicts) that cap unsealed, else the EX1 PCC. An
// unpredicted CJALR always mispredicts, so ir1 behind it never issues.
// ir_pcc_cap_q is the PCC the next decoded instruction issues under. Only the
// fields the decoder reads are linked (all are moot when untagged).
function automatic cheri_pkg::pcc_cap_t g_ppcc(logic [super_pkg::RegW-1:0] t);
  return cheri_pkg::full2pcap(cheri_pkg::op2fullcap(cheri_pkg::reg2opcap(
           cheri_pkg::unseal_rcap(cheri_pkg::reg_cap_t'(t)))));
endfunction
function automatic logic g_dpcc_eq(cheri_pkg::pcc_cap_t a, cheri_pkg::pcc_cap_t b);
  return (a.valid == b.valid) &&
         (!a.valid || ((a.perms[cheri_pkg::PERM_EX] == b.perms[cheri_pkg::PERM_EX]) &&
                       (a.perms[cheri_pkg::PERM_SR] == b.perms[cheri_pkg::PERM_SR]) &&
                       (a.otype == b.otype) && (a.base32 == b.base32) && (a.top33 == b.top33)));
endfunction
super_pkg::ir_dec_t g_fd0, g_fd1;
assign g_fd0 = g_ir_scope[0].ir_dec;
assign g_fd1 = g_ir_scope[1].ir_dec;
for (genvar k = 0; k < 2; k++) begin : g_inv_irf
  cheri_pkg::pcc_cap_t ep;
  super_pkg::ir_dec_t  d, f;
  logic                live;
  assign d    = g_ir_scope[k].ir_dec;
  assign ep   = ((k == 1) && g_fd0.is_jalr) ? g_ppcc(g_fd0.ptarget) : `KCSR.ex1_pcc_cap_q;
  assign live = `KDUT.ir_valid[k] && !((k == 1) && g_fd0.is_jalr && !g_fd0.ptaken);
  ir_decoder #(
    .CHERIoTEn (1'b1),
    .RV32M     (KuduE2eCfg.RV32M),
    .RV32B     (KuduE2eCfg.RV32B),
    .RV32A     (KuduE2eCfg.RV32A)
  ) u_fdec (
    .clk_i         (clk_i),
    .rst_ni        (rst_ni),
    .cheri_pmode_i (1'b1),
    .debug_mode_i  (1'b0),
    .pcc_cap_i     (ep),
    .ir_reg_i      (g_inv_ir[k].rin),
    .brkpt_match_i (1'b0),
    .ir_dec_o      (f)
  );
  // Kudu's fetch-fault priority: perm_vio, bound_vio, ..., asr_vio.
  Inv_G_IrFErr: assert property (live |->
    (d.errs.perm_vio == f.errs.perm_vio) &&
    (d.errs.perm_vio || ((d.errs.bound_vio == f.errs.bound_vio) &&
                         (d.errs.bound_vio || (d.errs.asr_vio == f.errs.asr_vio)))));
end
Inv_G_IrPccQ: assert property (
  (`KDUT.ir_valid[1] && g_fd1.is_jalr) ? (!g_fd1.ptaken || g_dpcc_eq(`KCSR.ir_pcc_cap_q, g_ppcc(g_fd1.ptarget))) :
  (`KDUT.ir_valid[0] && g_fd0.is_jalr) ? (!g_fd0.ptaken || g_dpcc_eq(`KCSR.ir_pcc_cap_q, g_ppcc(g_fd0.ptarget))) :
                                         g_dpcc_eq(`KCSR.ir_pcc_cap_q, `KCSR.ex1_pcc_cap_q));
// Fetch only sets errs.fetch_err (and the compressed decoders illegal_c_insn);
// the CHERI and illegal_insn bits of the stored s0_fifo words are always 0
// (ir_decoder ORs the input errs into any_err).
for (genvar i = 0; i < int'(KuduE2eCfg.IrS0Depth); i++) begin : g_inv_s0
  super_pkg::ir_reg_t s0e;
  assign s0e = super_pkg::ir_reg_t'(`KDUT.ir_stage_i.gen_stage0_buffer.s0_fifo.fifo_mem[i]);
  Inv_A_S0Errs: assert property (!s0e.errs.asr_vio && !s0e.errs.perm_vio &&
                                 !s0e.errs.bound_vio && !s0e.errs.illegal_insn);
  // An occupied word's is_comp follows its 16-bit parcel (fetch_fifo64).
  localparam int S0PW = $clog2(int'(KuduE2eCfg.IrS0Depth)) + 1;
  logic [S0PW-1:0] s0wp, s0rp;
  logic            s0occ;
  assign s0wp  = `KDUT.ir_stage_i.gen_stage0_buffer.s0_fifo.wr_ptr_q;
  assign s0rp  = `KDUT.ir_stage_i.gen_stage0_buffer.s0_fifo.rd_ptr_q;
  assign s0occ = S0PW'((S0PW-1)'((S0PW-1)'(i) - s0rp[S0PW-2:0])) < S0PW'(s0wp - s0rp);
  Inv_A_S0Comp: assert property (s0occ |-> s0e.is_comp == (s0e.insn[1:0] != 2'b11));
end
// Forwarded operands are well formed: their bound corrections are those
// reg2opcap derives from the value itself, as on a register-file read
// (otherwise Kudu's expanded bounds differ from the spec's decoding).
for (genvar i = 0; i < 4; i++) begin : g_inv_fwd
  for (genvar j = 0; j < 2; j++) begin : g_slot
    logic [super_pkg::OpW-1:0] fd;
    assign fd = (j == 0) ? `KISS.fwd_info[i].data0 : `KISS.fwd_info[i].data1;
    Inv_A_FwdCap: assert property (`KISS.fwd_info[i].valid[j] |->
      fd == cheri_pkg::reg2opcap(cheri_pkg::op2regcap(cheri_pkg::op_cap_t'(fd))));
  end
end
// The CHERI ALU's registered result feeds the ALU write-back forwarding slot.
// fwd_lookup ORs every matching slot, so at most one may match a register.
for (genvar a = 0; a < 8; a++) begin : g_inv_fwdu
  for (genvar b = a + 1; b < 8; b++) begin : g_b
    Inv_A_FwdUniq: assert property (!(
      `KISS.fwd_info[a/2].valid[a%2] && `KISS.fwd_info[b/2].valid[b%2] &&
      (((a%2) ? `KISS.fwd_info[a/2].addr1 : `KISS.fwd_info[a/2].addr0) ==
       ((b%2) ? `KISS.fwd_info[b/2].addr1 : `KISS.fwd_info[b/2].addr0))));
  end
end
// A mult EX2 result that will still forward (ex2_fwd_ok, not yet cancelled
// by a younger WaW) is unique against every live WB forwarding slot.
logic inv_mex2_live;
assign inv_mex2_live = `KDUT.mult_pipeline_i.ex2_valid && `KDUT.mult_pipeline_i.ex2_reg.rf_we &&
                       (`KDUT.mult_pipeline_i.ex2_reg.rd != 5'd0) && `KDUT.mult_pipeline_i.ex2_fwd_ok;
for (genvar p = 0; p < 4; p++) begin : g_inv_mex2u
  if (p != 2) begin : g_p
    Inv_A_MultEx2Uniq: assert property (!(inv_mex2_live && `KISS.fwd_info[p].valid[1] &&
                                          (`KISS.fwd_info[p].addr1 == `KDUT.mult_pipeline_i.ex2_reg.rd)));
  end
end
// The 2-stage IR preloads register values (ir_stage gen_stage1): each s1
// slot's rf_rdata2_q is the register file at its latched raddr2_q (kept in
// step with every RF write and revocation tag clear), and a valid slot's
// raddr2_q is its instruction's rs1/rs2.
`define KIRS `KDUT.ir_stage_i
`define KRF  `KDUT.regfile_i
Inv_A_IraRd0: assert property (`KIRS.ira_rf_rdata2_q.d0 == `KRF.rf_reg[`KIRS.ira_raddr2_q.a0]);
Inv_A_IraRd1: assert property (`KIRS.ira_rf_rdata2_q.d1 == `KRF.rf_reg[`KIRS.ira_raddr2_q.a1]);
Inv_A_IrbRd0: assert property (`KIRS.irb_rf_rdata2_q.d0 == `KRF.rf_reg[`KIRS.irb_raddr2_q.a0]);
Inv_A_IrbRd1: assert property (`KIRS.irb_rf_rdata2_q.d1 == `KRF.rf_reg[`KIRS.irb_raddr2_q.a1]);
// The spec reads its operands from Kudu, so Kudu's capability storage holds
// only capabilities software can hold (inv_cap_ok), as Inv_B_*WF for the spec.
function automatic logic inv_rcap_ok(cheri_pkg::reg_cap_t r);
  return inv_cap_ok(regcap2sail(r, r.addr)) && inv_cap_canon(regcap2sail(r, r.addr));
endfunction
for (genvar i = 1; i < 32; i++) begin : g_inv_rfwf
  Inv_A_RfWF: assert property (inv_rcap_ok(cheri_pkg::reg_cap_t'(`KRF.rf_reg[i])));
end
for (genvar i = 0; i < 4; i++) begin : g_inv_fwdwf
  for (genvar j = 0; j < 2; j++) begin : g_slot
    logic [super_pkg::OpW-1:0] fd;
    assign fd = (j == 0) ? `KISS.fwd_info[i].data0 : `KISS.fwd_info[i].data1;
    Inv_A_FwdWF: assert property (`KISS.fwd_info[i].valid[j] |->
      inv_rcap_ok(cheri_pkg::op2regcap(cheri_pkg::op_cap_t'(fd))));
  end
end
// Write-back results reach the register file even after a WAW cancel has
// cleared their forwarding valid, so Inv_A_FwdWF alone does not cover them.
// Writes to x0 are discarded by the register file (no x0 flops), so a
// JAL/AUIPCC with rd = 0 may carry any value.
Inv_A_AluWbWF0: assert property (`KDUT.alu_pipeline0_i.wb_valid && `KDUT.alupl0_output.we &&
                                 (`KDUT.alupl0_output.waddr != 5'd0) |->
                                 inv_rcap_ok(cheri_pkg::reg_cap_t'(`KDUT.alupl0_output.wdata)));
Inv_A_AluWbWF1: assert property (`KDUT.alu_pipeline1_i.wb_valid && `KDUT.alupl1_output.we &&
                                 (`KDUT.alupl1_output.waddr != 5'd0) |->
                                 inv_rcap_ok(cheri_pkg::reg_cap_t'(`KDUT.alupl1_output.wdata)));
Inv_A_MulWbWF:  assert property (`KDUT.mult_pipeline_i.wb_valid && `KDUT.multpl_output.we &&
                                 (`KDUT.multpl_output.waddr != 5'd0) |->
                                 inv_rcap_ok(cheri_pkg::reg_cap_t'(`KDUT.multpl_output.wdata)));
// The multiplier's EX2 result (CJALR link/target, CSetBounds*) is computed from
// ex1_tfcap_q/setbounds_req_q captured at EX1, which nothing else constrains.
Inv_A_MulEx2WF: assert property (`KDUT.mult_pipeline_i.ex2wb_valid && `KDUT.mult_pipeline_i.ex2_reg.rf_we &&
                                 (`KDUT.mult_pipeline_i.ex2_reg.rd != 5'd0) |->
                                 inv_rcap_ok(cheri_pkg::reg_cap_t'(
                                   `KDUT.mult_pipeline_i.ex2wb_reg.wdata[super_pkg::RegW-1:0])));
// Kudu's EX1 PCC, in Kudu's decoded form: when tagged it has E <= 24 (as
// cap_well_formed), perms decoded from cperms, an encoding inv_cap_ok accepts
// (canonical cperms; the CJALR/JAL link inherits it), exponent-aligned bounds
// with base <= top <= 2^32, and a length a 9-bit mantissa can encode. F_Pcc/F_PccBnd tie ex1_pcc_cap_q to
// the spec only outside the trap shadow; inside it the pre-trap PCC still
// feeds AUIPCC/JAL (ALUs) and the CJALR link (mult EX1). ir_pcc_cap_q is
// excluded: it is a CJALR-return prediction used only by IR-stage fetch
// checks, and a mispredict replaces it with the EX1 PCC.
function automatic logic inv_kpcc_ok(cheri_pkg::pcc_cap_t p);
  logic [33:0] m, len;
  m   = (34'h1 << p.exp) - 34'h1;
  len = {1'b0, p.top33} - {2'b0, p.base32};
  return !p.valid || ((p.exp <= 5'd24) && (p.perms == cheri_pkg::expand_perms(p.cperms)) &&
                      inv_cap_ok(pcc2sail(p, p.base32)) &&
                      (p.top33 <= 33'h1_0000_0000) && ({1'b0, p.base32} <= p.top33) &&
                      ((p.base32 & m[31:0]) == 32'h0) && (({1'b0, p.top33} & m) == 34'h0) &&
                      (len <= (34'h1 << (6'(p.exp) + 6'd9))));
endfunction
Inv_A_KPccWF:   assert property (inv_kpcc_ok(`KCSR.ex1_pcc_cap_q));
// SCR writes take cs1_fcap from the LSU's current request (stale or live).
Inv_A_LsuCs1WF: assert property (`KLSU.lsu_req_info_q.is_csr |->
                                 inv_cap_ok(op2sail(`KLSU.lsu_req_info_q.cs1_fcap)) &&
                                 inv_cap_canon(op2sail(`KLSU.lsu_req_info_q.cs1_fcap)));
// Every LS write-back FIFO slot, live or stale: slots are written only from
// lsu_resp_info and reset to zero. Faulting entries (err) carry raw bus data
// but never reach the register file (committer instr_err blocks rf_we2).
// An x0 destination is discarded (e.g. CSpecialRW x0 of a divergence-G MEPCC).
for (genvar i = 0; i < 4; i++) begin : g_inv_lsfifowf
  super_pkg::pl_out_t ent;
  assign ent = super_pkg::pl_out_t'(`KDUT.ls_pipeline_i.wb_fifo_i.fifo_mem[i]);
  Inv_A_LsFifoWF: assert property (ent.we && !ent.err && (ent.waddr != 5'd0) |-> inv_rcap_ok(cheri_pkg::reg_cap_t'(ent.wdata)));
end
Inv_A_CsrWF: assert property (inv_cap_ok(dut_mtvec) && inv_cap_ok(dut_mepc) &&
                              inv_cap_ok(dut_mscratchc) && inv_cap_ok(dut_mtdc) &&
                              inv_cap_canon(dut_mtvec) &&
                              inv_cap_canon(dut_mscratchc) && inv_cap_canon(dut_mtdc));
Inv_A_MtvecAlign: assert property (dut_mtvec.address[1:0] == 2'b00);
Inv_A_PccX: assert property (inv_xcap_ok(pcc2sail(`KCSR.ex1_pcc_cap_q, `KCSR.ex1_pcc_cap_q.base32)) &&
                             inv_xcap_ok(dut_mtvec) && inv_xcap_ok(dut_mepc));
Inv_A_IraAddr: assert property ((`KDUT.ira_is0 ? `KDUT.ir_valid[0] : `KDUT.ir_valid[1]) |->
                                (`KIRS.ira_raddr2_q.a0 == `KIRS.ira_dec_o.rs1) &&
                                (`KIRS.ira_raddr2_q.a1 == `KIRS.ira_dec_o.rs2));
Inv_A_IrbAddr: assert property ((`KDUT.ira_is0 ? `KDUT.ir_valid[1] : `KDUT.ir_valid[0]) |->
                                (`KIRS.irb_raddr2_q.a0 == `KIRS.irb_dec_o.rs1) &&
                                (`KIRS.irb_raddr2_q.a1 == `KIRS.irb_dec_o.rs2));
Inv_A_AluCap0: assert property (`KDUT.alu_pipeline0_i.cheri_alu_result ==
  cheri_pkg::reg2opcap(cheri_pkg::op2regcap(`KDUT.alu_pipeline0_i.cheri_alu_result)));
Inv_A_AluCap1: assert property (`KDUT.alu_pipeline1_i.cheri_alu_result ==
  cheri_pkg::reg2opcap(cheri_pkg::op2regcap(`KDUT.alu_pipeline1_i.cheri_alu_result)));
// Likewise the mult pipeline's EX2 result and its write-back register.
Inv_A_MultEx2Cap: assert property (`KDUT.mult_pipeline_i.ex2_result ==
  cheri_pkg::reg2opcap(cheri_pkg::op2regcap(`KDUT.mult_pipeline_i.ex2_result)));
Inv_A_MultWbCap: assert property (`KDUT.mult_pipeline_i.wb_reg.wdata ==
  cheri_pkg::reg2opcap(cheri_pkg::op2regcap(`KDUT.mult_pipeline_i.wb_reg.wdata)));
// ex2_err is tied to 0, so the mult write-back register never holds an error
// (only the LS pipeline reports commit errors).
Inv_A_MultNoErr: assert property (!`KDUT.mult_pipeline_i.wb_reg.err);
Inv_A_LsuCsrScope: assert property (`KLSU.lsu_req_info_q.is_csr |-> inv_csr_ok(`KLSU.lsu_req_info_q.insn));
Inv_A_CmplxIdle:  assert property (`KCPX.cmplx_fsm_cs == 2'h0);

// sbd_fifo occupancy and status flags.
logic [3:0] inv_sbd_depth;
assign inv_sbd_depth = `KSBD.wr_ptr_q - `KSBD.rd_ptr_q;

Inv_A_SbdDepth:  assert property (inv_sbd_depth <= 4'(SbdDepth));
Inv_A_SbdFill:   assert property (`KSBD.fill_status_q == {inv_sbd_depth > 4'd1, inv_sbd_depth > 4'd0});
Inv_A_SbdRoom:   assert property (`KSBD.room_status_q == {inv_sbd_depth < 4'(SbdDepth-1),
                                                          inv_sbd_depth < 4'(SbdDepth)});

// LSU (ls_fsm_e: 0 IDLE, 1 WAIT_GNT_MIS, 2 WAIT_RVALID_MIS, 3 WAIT_GNT) and
// lsu_if (0 IDLE, 1 DLY0_WGNT, 2 DLY1, 3 DLY1_WGNT).
logic inv_ls_idle;
assign inv_ls_idle = (`KLSU.ls_fsm_cs == super_pkg::IDLE);

Inv_A_LsuFsm:     assert property (`KLSU.ls_fsm_cs inside {3'd0, 3'd1, 3'd2, 3'd3});
Inv_A_LsifFsm:    assert property (`KLSIF.lsif_fsm_q inside {3'd0, 3'd1, 3'd2, 3'd3});
Inv_A_LsifIdleLs: assert property ((`KLSIF.lsif_fsm_q inside {3'd0, 3'd2}) |-> inv_ls_idle);
Inv_A_LsifDly1:   assert property ((`KLSIF.lsif_fsm_q == 3'd2) |-> `KLSIF.req_dly_valid);
// CSR requests buffered in lsu_if came through Env_InsnScope (feeds LsuCsrScope).
Inv_A_LsifDlyScope:  assert property (`KLSIF.req_dly_valid && `KLSIF.req_dly_q.is_csr |->
                                      inv_csr_ok(`KLSIF.req_dly_q.insn));
Inv_A_LsifHoldScope: assert property ((`KLSIF.lsif_fsm_q inside {3'd1, 3'd3}) && `KLSIF.req_hold_q.is_csr |->
                                      inv_csr_ok(`KLSIF.req_hold_q.insn));
Inv_A_LsuMis:     assert property (inv_ls_idle |-> !`KLSU.handle_misaligned_q);
Inv_A_LsuNoErrQ:  assert property (!`KLSU.pmp_err_q && !`KLSU.bus_err_q);
// req_err_q / csr_go_q are set only by ls_go / csr_go, together with
// outstanding_resp_q, and the FSM stays IDLE.
Inv_A_LsuReqErrQ: assert property (`KLSU.req_err_q |-> `KLSU.outstanding_resp_q && inv_ls_idle &&
                                   `KLSU.lsu_req_info_q.lschk_err.any_fault && !`KLSU.csr_go_q);
Inv_A_LsuCsrGoQ:  assert property (`KLSU.csr_go_q |-> `KLSU.outstanding_resp_q && inv_ls_idle &&
                                   `KLSU.lsu_req_info_q.is_csr);
// A CSR access answers in the cycle after csr_go (csr_go_q), so an outstanding
// CSR request always has csr_go_q set.
Inv_A_LsuCsrOut:  assert property (`KLSU.outstanding_resp_q && `KLSU.lsu_req_info_q.is_csr |->
                                   `KLSU.csr_go_q);
// outstanding_resp_q is set with every ls_go and cleared only by the response
// (taken in IDLE), so a busy LSU always has it set (feeds RspDue).
Inv_A_LsuBusyOut: assert property (!inv_ls_idle |-> `KLSU.outstanding_resp_q);

////////////////////// Group C: scoreboard follower //////////////////////

logic [SbdDepth-1:0] inv_sbd_ls;   // occupied scoreboard entries of the LS pipeline
logic [SbdDepth-1:0] inv_sbd_src;  // occupied non-shadow trapping entries
for (genvar e = 0; e < SbdDepth; e++) begin : g_inv_sbd
  logic                 occ;
  super_pkg::sbd_fifo_t ent;
  assign occ = (3'(e - `KSBD.rd_ptr_q[2:0]) < inv_sbd_depth);
  assign ent = super_pkg::sbd_fifo_t'(`KSBD.fifo_mem[e]);

  assign inv_sbd_ls[e] = occ && ent.pl[3];

  Inv_C_FolValid: assert property (fol_valid[e] == occ);
  Inv_C_FolPc:    assert property (fol_valid[e] |-> fol_pc[e] == ent.pc);
  Inv_C_FolPl:    assert property (fol_valid[e] |-> fol_pl[e] == ent.pl);
  // pl comes from issuer select_pl (cheri_pmode=1: JALR -> 0x11).
  Inv_C_PlLegal:  assert property (occ |-> ent.pl inside {5'h01, 5'h02, 5'h03, 5'h04, 5'h05,
                                                          5'h08, 5'h10, 5'h11});

  // Shadow ordering: entries are in program order from rd_ptr, so every
  // entry younger than a trapping or shadow entry is shadow, and any such
  // entry implies shadow_q (both are cleared only by cmt_flush).
  logic nxt_occ;
  assign nxt_occ = (3'(e + 1 - `KSBD.rd_ptr_q[2:0]) < inv_sbd_depth) && (3'(e + 1 - `KSBD.rd_ptr_q[2:0]) != 3'd0);
  assign inv_sbd_src[e] = occ && fol_err[e] && !fol_shadow[e];
  Inv_C_ShQ:   assert property (occ && (fol_shadow[e] || fol_err[e]) |-> shadow_q);
  Inv_C_ShOrd: assert property (occ && nxt_occ && (fol_shadow[e] || fol_err[e]) |->
                                fol_shadow[(e + 1) % SbdDepth]);
  // cmt_err_q: the trapping entry has committed and dequeue has stopped, so
  // every remaining entry is younger than it.
  Inv_C_ErrAllSh: assert property (`KCMT.cmt_err_q && occ |-> fol_shadow[e]);
  // Only the LS pipeline reports errors (ALU/mult output err is tied 0), so a
  // non-shadow spec trap that issued is an LS (or CSR) entry.
  Inv_C_ErrLs:    assert property (inv_sbd_src[e] |-> ent.pl == 5'h08);
end

// A pending trap (shadow_q) comes from a non-shadow trapping instruction
// still in the scoreboard, or one already committed with cmt_err.
Inv_C_ShSrc:      assert property (shadow_q |-> `KCMT.cmt_err_q || (|inv_sbd_src));
Inv_C_ErrShadow:  assert property (`KCMT.cmt_err_q |-> shadow_q);
Inv_C_SpNoShadow: assert property (st_special |-> !shadow_q);
// ISSUE_SPECIAL is entered from WAIT_CMT0 with an empty scoreboard and no
// commit error; SLEEP (wfi) from ISSUE_SPECIAL, and nothing issues in it.
Inv_C_SpSbdEmpty: assert property (`KISS.ctrl_fsm_cs[super_pkg::CSM_ISSUE_SPECIAL] |->
                                   (inv_sbd_depth == 4'd0) && !`KCMT.cmt_err_q);
Inv_C_SleepEmpty: assert property (`KISS.ctrl_fsm_cs[super_pkg::CSM_SLEEP] |->
                                   (inv_sbd_depth == 4'd0) && !`KCMT.cmt_err_q && !shadow_q);

////////////////////// Group D: LS follower, LSU, bus //////////////////////

// Requests issued to ls_pipeline that the LSU has not yet started (ls_go or
// csr_go): the lsu_if delay register in DLY1/DLY1_WGNT, and the hold register
// in DLY0_WGNT/DLY1_WGNT while the LSU is still idle.
logic [2:0] inv_lsif_pend;
always_comb begin
  case (`KLSIF.lsif_fsm_q)
    3'd1:    inv_lsif_pend = 3'(inv_ls_idle);
    3'd2:    inv_lsif_pend = 3'(`KLSIF.req_dly_valid);
    3'd3:    inv_lsif_pend = 3'(`KLSIF.req_dly_valid) + 3'(inv_ls_idle);
    default: inv_lsif_pend = 3'd0;
  endcase
end

Inv_D_LsqCnt:    assert property (lsq_cnt_q == inv_lsif_pend);
// Every request in lsu_if is uncommitted, so it still has a scoreboard
// entry; ISSUE_SPECIAL (entered once the scoreboard drains) issues a CSR
// without checking lspl_rdy and relies on this.
Inv_D_SbdEmptyLsif: assert property ((inv_sbd_depth == 4'd0) |->
                                     (`KLSIF.lsif_fsm_q == 3'd0) && (lsq_cnt_q == 3'd0));
// Every LS instruction waiting for the LSU still holds its scoreboard entry:
// commit is in order and both are emptied by cmt_flush (feeds SbdEmptyLsif).
Inv_D_LsqSbd:    assert property (4'(lsq_cnt_q) <= inv_sbd_depth);
// Every issued, uncommitted LS instruction has one waw_fifo entry (pushed at
// issue, popped at commit, both cleared by flush) and one LS scoreboard
// entry, and is in exactly one place: waiting for the LSU (LSQ), in the LSU
// (outstanding_resp_q, one at a time) or in wb_fifo.
logic [3:0] inv_waw_cnt, inv_sbd_ls_cnt;
logic [2:0] inv_wb_cnt;
assign inv_waw_cnt    = `KLSP.waw_fifo_i.wr_ptr_q - `KLSP.waw_fifo_i.rd_ptr_q;
assign inv_wb_cnt     = `KLSP.wb_fifo_i.wr_ptr_q - `KLSP.wb_fifo_i.rd_ptr_q;
assign inv_sbd_ls_cnt = 4'($countones(inv_sbd_ls));
Inv_D_LsInFlight: assert property (inv_waw_cnt == 4'(lsq_cnt_q) + 4'(`KLSU.outstanding_resp_q) +
                                                  4'(inv_wb_cnt));
Inv_D_SbdLs:      assert property (inv_sbd_ls_cnt == inv_waw_cnt);
// FIFO occupancy bounds: the LSU starts an access only with wb_fifo room
// (wr_rdy2), so a pending response always has a free wb_fifo slot.
Inv_D_WbRoom:     assert property (4'(inv_wb_cnt) + 4'(`KLSU.outstanding_resp_q) <= 4'd4);
Inv_D_WawDepth:   assert property (inv_waw_cnt <= 4'd8);
Inv_D_LsqPtr:    assert property (2'(lsq_wp_q - lsq_rp_q) == lsq_cnt_q[1:0]);
Inv_D_LsqHead:   assert property ((lsq_cnt_q >= 3'd1) |-> lsq_mem[lsq_rp_q].valid);
Inv_D_LsqNext:   assert property ((lsq_cnt_q >= 3'd2) |-> lsq_mem[2'(lsq_rp_q + 2'd1)].valid);
Inv_D_LsuCur:    assert property (!inv_ls_idle |-> lsq_cur_q.valid);
// The LSU reads its request input (addr, be, wdata, is_cap, ...) for the whole
// transaction: while it is busy lsu_if presents the hold register, loaded
// with the request the LSU latched at ls_go (xfr2hold0/1). A flush cannot
// release it early (it needs resp_err_latched, so the LSU is idle).
Inv_D_LsuHold:   assert property (!inv_ls_idle |-> (`KLSIF.lsif_fsm_q inside {3'd1, 3'd3}) &&
                                                   (`KLSIF.req_hold_q == `KLSU.lsu_req_info_q));
// Commit errors come only from ls_pipeline (the other pipelines never set
// err). After an error response the LSU starts nothing (ds_rdy = 0) until
// the flush, so the erroring result is the youngest in wb_fifo, and once it
// commits (cmt_err) nothing is in flight; CMT_FLUSH is entered only on
// cmt_err, so a flush never strands an outstanding LSU response.
logic [3:0] inv_wb_err;
for (genvar j = 0; j < 4; j++) begin : g_inv_wb
  logic [2:0]         off;
  super_pkg::pl_out_t ent;
  assign off = 3'(2'(2'(j) - `KLSP.wb_fifo_i.rd_ptr_q[1:0]));
  assign ent = super_pkg::pl_out_t'(`KLSP.wb_fifo_i.fifo_mem[j]);
  assign inv_wb_err[j] = (off < inv_wb_cnt) && ent.err;
  Inv_D_WbErrLast: assert property (inv_wb_err[j] |-> off == inv_wb_cnt - 3'd1);
end
Inv_D_WbErrLatch: assert property ((|inv_wb_err) |-> `KLSP.resp_err_latched);
Inv_D_LatchSrc:   assert property (`KLSP.resp_err_latched |-> (|inv_wb_err) || `KCMT.cmt_err_q);
Inv_D_ErrIdle:    assert property (`KLSP.resp_err_latched |-> !`KLSU.outstanding_resp_q);
Inv_D_CmtErr:     assert property (`KCMT.cmt_err_q |-> `KLSP.resp_err_latched && (inv_wb_cnt == 3'd0));
Inv_D_FlushErr:   assert property (`KISS.ctrl_fsm_cs[super_pkg::CSM_CMT_FLUSH] |-> `KCMT.cmt_err_q);
Inv_D_ErrLatch:   assert property (`KLSP.resp_err_latched |-> shadow_q);
// The requests waiting in lsu_if and the one in the LSU are the LSQ entries'
// instructions: head = hold register in DLY0_WGNT/DLY1_WGNT while the LSU is
// idle, else the delay register; the second entry is the delay register.
super_pkg::lsu_req_info_t inv_lsif_hd;
assign inv_lsif_hd = ((`KLSIF.lsif_fsm_q inside {3'd1, 3'd3}) && inv_ls_idle) ?
                     `KLSIF.req_hold_q : `KLSIF.req_dly_q;
Inv_D_LsifHdInsn: assert property ((lsq_cnt_q != 3'd0) |->
                                   (inv_lsif_hd.insn == lsq_mem[lsq_rp_q].insn) &&
                                   (inv_lsif_hd.is_csr == lsq_mem[lsq_rp_q].csr));
Inv_D_LsifNxInsn: assert property ((lsq_cnt_q >= 3'd2) |->
                                   (`KLSIF.req_dly_q.insn == lsq_mem[2'(lsq_rp_q + 2'd1)].insn) &&
                                   (`KLSIF.req_dly_q.is_csr == lsq_mem[2'(lsq_rp_q + 2'd1)].csr));
Inv_D_LsuCurInsn: assert property (`KLSU.outstanding_resp_q |->
                                   (`KLSU.lsu_req_info_q.insn == lsq_cur_q.insn) &&
                                   (`KLSU.lsu_req_info_q.is_csr == lsq_cur_q.csr));

// Data bus: a response is due exactly when the LSU waits for one.
Inv_D_RspDue:    assert property (data_rsp_due == ((`KLSU.ls_fsm_cs == 3'd2) ||
                                                   (inv_ls_idle && `KLSU.outstanding_resp_q &&
                                                    !`KLSU.csr_go_q && !`KLSU.req_err_q)));
Inv_D_RspEnt:    assert property (data_rsp_due |-> lsq_rsp_ent_q.valid);
Inv_D_ReqIdxMis: assert property ((`KLSU.ls_fsm_cs == 3'd1) |-> !lsq_req_idx_q);
Inv_D_ReqIdxRv:  assert property ((`KLSU.ls_fsm_cs == 3'd2) |-> lsq_req_idx_q);
Inv_D_ReqIdxGnt: assert property ((`KLSU.ls_fsm_cs == 3'd3) |-> lsq_req_idx_q == `KLSU.handle_misaligned_q);

////////////////////// Group E: CSR state vs spec_past_* //////////////////////

// The spec steps an instruction at issue; Kudu applies its CSR effects later,
// in program order:
//   - a CSR instruction two cycles after csr_go (csr_chk1_q -> visible at
//     csr_chk2_q), with the post-state recorded in its LSQ entry;
//   - a serialised non-LS step or a trap at ISSUE_SPECIAL, visible the next
//     cycle (Special_Post);
//   - a shadowing trap at CMT_FLUSH, visible the next cycle; spec_past_* is
//     frozen at the trap's post-state while shadow_q is set.
// e_cur_* is the spec state Kudu has applied so far. Kudu's CSRs always equal
// it, and it equals spec_past_* when nothing is pending. mshwm (also written
// by stores) is tracked separately (group M).
t_Privilege    e_cur_priv;
kudu_mstatus_t e_cur_mstatus;
logic [31:0]   e_cur_mie, e_cur_mcause, e_cur_mtval, e_cur_mscratch, e_cur_mshwmb;
t_Capability   e_cur_mtvec, e_cur_mepc, e_cur_mscratchc, e_cur_mtdc;

logic e_app_flush, e_app_special, e_app_csr, e_pend;
assign e_app_flush   = `KDUT.cmt_flush && `KDUT.csr_save_cause;
assign e_app_special = s0_upd && st_special && (!`KISS.ir0_pl_sel[3] || `KDUT.csr_save_cause);
assign e_app_csr     = csr_chk1_q;
assign e_pend        = shadow_q || (lsq_cnt_q != 3'd0) || csr_chk1_q;

`define KE_SET(SRC) \
  e_cur_priv <= SRC``priv;  e_cur_mstatus <= SRC``mstatus; e_cur_mie <= SRC``mie; \
  e_cur_mcause <= SRC``mcause; e_cur_mtval <= SRC``mtval; e_cur_mscratch <= SRC``mscratch; \
  e_cur_mshwmb <= SRC``mshwmb; e_cur_mtvec <= SRC``mtvec; e_cur_mepc <= SRC``mepc; \
  e_cur_mscratchc <= SRC``mscratchc; e_cur_mtdc <= SRC``mtdc;
`define KE_SETS(SRC) \
  e_cur_priv <= SRC.priv;  e_cur_mstatus <= SRC.mstatus; e_cur_mie <= SRC.mie; \
  e_cur_mcause <= SRC.mcause; e_cur_mtval <= SRC.mtval; e_cur_mscratch <= SRC.mscratch; \
  e_cur_mshwmb <= SRC.mshwmb; e_cur_mtvec <= SRC.mtvec; e_cur_mepc <= SRC.mepc; \
  e_cur_mscratchc <= SRC.mscratchc; e_cur_mtdc <= SRC.mtdc;

// Before the first step there is no spec state: track Kudu's.
always_ff @(posedge clk_i) begin
  if      (e_app_flush)   begin `KE_SET(past_) end
  else if (e_app_special) begin `KE_SET(s0_post_) end
  else if (e_app_csr)     begin `KE_SETS(csr_ent1_q)
    // The entry's mstatus.mie predates any younger sentry CJALR that already
    // set/cleared it at EX1; only an mstatus write replaces it.
    if (!`KCSR.mstatus_en) e_cur_mstatus.mie <= e_cur_mstatus.mie;
  end
  else if (!past_valid)   begin `KE_SET(dut_) end
  // A sentry CJALR sets/clears mstatus.mie at EX1, overriding any same-cycle
  // CSR update (cs_registers mstatus_d_combi).
  if (`KCSR.ex1_cjalr_set_mie_i || `KCSR.ex1_cjalr_clr_mie_i)
    e_cur_mstatus.mie <= `KCSR.ex1_cjalr_set_mie_i;
end

`undef KE_SET
`undef KE_SETS

// Traps are the only source of cmt_flush (debug is off, bus errors trap in
// the spec), and the two Kudu-side application events never coincide.
Inv_E_FlushShadow: assert property (`KDUT.cmt_flush |-> shadow_q);
Inv_E_AppExcl:     assert property (!(e_app_csr && (e_app_flush || e_app_special)));

// Linking the pending LSQ/CSR entries to e_cur and spec_past_*. The entries
// older than a shadowing trap (and the trap itself) form a chain in program
// order; only the link to spec_past_* needs to be outside the shadow:
//   e_cur (or csr_ent1_q's post) = pre(head), post(k-1) = pre(k),
//   post(youngest) = spec_past_*;
// a non-CSR entry leaves the tracked CSRs unchanged. mstatus.mie is left out
// of the chain because a sentry CJALR (not in the LSQ) changes it at issue;
// writes to mstatus/mie (wmie) are serialised, so a wmie entry is the only
// one pending and its mie is linked too.
// Both sides are spec states (e_cur_* tracks applied spec state), so MEPCC is
// compared exactly; xepc_eq is only for Kudu-vs-spec.
function automatic logic e_st_eq(e_st_t a, e_st_t b, logic with_mie);
  if (!with_mie) b.mstatus.mie = a.mstatus.mie;
  return (a.priv == b.priv) && (a.mstatus == b.mstatus) && (a.mie == b.mie) &&
         (a.mcause == b.mcause) && (a.mtval == b.mtval) &&
         (a.mscratch == b.mscratch) && (a.mshwmb == b.mshwmb) &&
         cap_eq(a.mtvec, b.mtvec) && cap_eq(a.mepc, b.mepc) &&
         cap_eq(a.mscratchc, b.mscratchc) && cap_eq(a.mtdc, b.mtdc);
endfunction

function automatic e_st_t e_post(lsq_ent_t x);
  e_st_t r;
  r.priv = x.priv; r.mstatus = x.mstatus; r.mie = x.mie; r.mcause = x.mcause;
  r.mtval = x.mtval; r.mscratch = x.mscratch; r.mshwmb = x.mshwmb;
  r.mtvec = x.mtvec; r.mepc = x.mepc; r.mscratchc = x.mscratchc; r.mtdc = x.mtdc;
  return r;
endfunction

e_st_t    e_st_cur, e_st_past, e_st_prev;
lsq_ent_t e_head, e_young;
logic     e_p, e_wmie_pend;

always_comb begin
  e_st_cur.priv = e_cur_priv; e_st_cur.mstatus = e_cur_mstatus; e_st_cur.mie = e_cur_mie;
  e_st_cur.mcause = e_cur_mcause; e_st_cur.mtval = e_cur_mtval;
  e_st_cur.mscratch = e_cur_mscratch; e_st_cur.mshwmb = e_cur_mshwmb;
  e_st_cur.mtvec = e_cur_mtvec; e_st_cur.mepc = e_cur_mepc;
  e_st_cur.mscratchc = e_cur_mscratchc; e_st_cur.mtdc = e_cur_mtdc;
  e_st_past.priv = past_priv; e_st_past.mstatus = past_mstatus; e_st_past.mie = past_mie;
  e_st_past.mcause = past_mcause; e_st_past.mtval = past_mtval;
  e_st_past.mscratch = past_mscratch; e_st_past.mshwmb = past_mshwmb;
  e_st_past.mtvec = past_mtvec; e_st_past.mepc = past_mepc;
  e_st_past.mscratchc = past_mscratchc; e_st_past.mtdc = past_mtdc;
end

assign e_head      = lsq_mem[lsq_rp_q];
assign e_young     = lsq_mem[2'(lsq_wp_q - 2'd1)];
assign e_st_prev   = csr_chk1_q ? e_post(csr_ent1_q) : e_st_cur;
assign e_p         = past_valid && !shadow_q;
assign e_wmie_pend = ((lsq_cnt_q != 3'd0) && e_head.wmie) || (csr_chk1_q && csr_ent1_q.wmie);
// A write to mstatus/mie is a sysctl: issued alone in ISSUE_SPECIAL, after
// which the issuer waits in WAIT_FINAL until the scoreboard drains (or a
// commit error moves it to CMT_FLUSH, which clears the LSQ).
Inv_E_WmieFsm: assert property (e_wmie_pend |-> `KISS.ctrl_fsm_cs[super_pkg::CSM_WAIT_FINAL] ||
                                                `KISS.ctrl_fsm_cs[super_pkg::CSM_CMT_FLUSH]);

// The LSU request in flight, or the one whose error response is latched, is
// older than every LSQ entry. A Kudu error response is a spec trap: the only
// Kudu-to-spec link these need (lschk/ASR/illegal CSR on Kudu operands, F).
logic e_cur_live, e_cur_sh;
assign e_cur_live = `KLSU.outstanding_resp_q || `KLSP.resp_err_latched;
assign e_cur_sh   = lsq_cur_q.trap || lsq_cur_q.shadow;
Inv_E_RespErr: assert property (`KLSU.lsu_resp_err_o |-> e_cur_sh);
Inv_E_ErrCur:  assert property (`KLSP.resp_err_latched |-> e_cur_sh);
Inv_E_CurSh:   assert property (e_cur_live && e_cur_sh |-> shadow_q);
Inv_E_CurOrd:  assert property (e_cur_live && e_cur_sh && (lsq_cnt_q != 3'd0) |-> e_head.shadow);

for (genvar k = 0; k < LsqDepth; k++) begin : g_inv_lsq
  lsq_ent_t ent, prv;
  logic     occ;
  assign ent = lsq_mem[2'(lsq_rp_q + 2'(k))];
  assign prv = lsq_mem[2'(lsq_rp_q + 2'(k) - 2'd1)];
  assign occ = 3'(k) < lsq_cnt_q;
  Inv_E_LsqSh:   assert property (occ && (ent.shadow || ent.trap) |-> shadow_q);
  // After an error response the LSU accepts nothing (ds_rdy = 0) until the
  // flush, and every request still queued is younger than the trap.
  Inv_E_LsqErrSh: assert property (occ && `KLSP.resp_err_latched |-> ent.shadow);
  Inv_E_LsqId:   assert property (occ && !ent.shadow && !ent.trap && !ent.csr |->
                                  e_st_eq(ent.pre, e_post(ent), 1'b1));
  Inv_E_LsqWmie: assert property (occ && ent.wmie |-> (lsq_cnt_q == 3'd1) && !csr_chk1_q);
  Inv_E_LsqDec:  assert property (occ |-> ent.wmie == inv_wmie(ent.insn));
  if (k > 0) begin : g_chain
    Inv_E_LsqShOrd: assert property (occ && (prv.shadow || prv.trap) |-> ent.shadow);
    Inv_E_LsqChain: assert property (past_valid && occ && !ent.shadow |->
                                     e_st_eq(e_post(prv), ent.pre, 1'b0));
  end
end

Inv_E_HeadPre:  assert property (past_valid && (lsq_cnt_q != 3'd0) && !e_head.shadow |->
                                 e_st_eq(e_st_prev, e_head.pre, e_head.wmie));
Inv_E_Chk1Pre:  assert property (past_valid && csr_chk1_q && !csr_ent1_q.shadow |->
                                 e_st_eq(e_st_cur, csr_ent1_q.pre, csr_ent1_q.wmie));
Inv_E_Tail:     assert property (e_p && (lsq_cnt_q != 3'd0) |->
                                 e_st_eq(e_post(e_young), e_st_past, e_young.wmie));
Inv_E_Chk1Past: assert property (e_p && (lsq_cnt_q == 3'd0) && csr_chk1_q |->
                                 e_st_eq(e_post(csr_ent1_q), e_st_past, csr_ent1_q.wmie));
Inv_E_Mie:      assert property (e_p && !e_wmie_pend |-> e_cur_mstatus.mie == past_mstatus.mie);
Inv_E_Chk1Wmie: assert property (csr_chk1_q && `KCSR.mstatus_en |-> csr_ent1_q.wmie);
Inv_E_Chk1Insn: assert property (csr_chk1_q |-> `KLSU.csr_go_q && csr_ent1_q.csr &&
                                 (csr_ent1_q.insn == `KLSU.lsu_req_info_q.insn) &&
                                 (csr_ent1_q.wmie == inv_wmie(csr_ent1_q.insn)));
// csr_go loads both lsq_cur_q and csr_ent1_q from the LSQ head.
Inv_E_Chk1Cur:  assert property (`KLSU.csr_go_q |-> lsq_cur_q == csr_ent1_q);
Inv_E_SpEmpty:  assert property (st_special |-> (lsq_cnt_q == 3'd0) && !csr_chk1_q);

`define KE_CHK(NAME) \
  Inv_E_Cur_``NAME: assert property (past_valid |-> dut_``NAME == e_cur_``NAME); \
  Inv_E_Eq_``NAME:  assert property (past_valid && !e_pend |-> e_cur_``NAME == past_``NAME);
`define KE_CHKF(NAME, EQ) \
  Inv_E_Cur_``NAME: assert property (past_valid |-> EQ(dut_``NAME, e_cur_``NAME)); \
  Inv_E_Eq_``NAME:  assert property (past_valid && !e_pend |-> cap_eq(e_cur_``NAME, past_``NAME));

// Kudu's MEPCC is canonical except under Kudu divergence G (README 1.1): a
// trap from an untagged PCC with E > 24, whose raw bounds Kudu does not keep,
// builds MEPCC from Kudu's decoded bounds; xepc_eq then compares the address only.
// E = 24 too: a trap from a PCC that is not canonical (Inv_B_PccWF).
Inv_E_MepcCanon: assert property (inv_cap_canon(dut_mepc) || (dut_mepc.E == 5'd24) ||
                                  (!dut_mepc.tag && !e_cur_mepc.tag && (e_cur_mepc.E > 5'd24)));
`KE_CHK(priv)
`KE_CHK(mstatus)
`KE_CHK(mie)
`KE_CHK(mcause)
`KE_CHK(mtval)
`KE_CHK(mscratch)
`KE_CHK(mshwmb)
`KE_CHKF(mtvec,     cap_eq)
`KE_CHKF(mepc,      xepc_eq)
`KE_CHKF(mscratchc, cap_eq)
`KE_CHKF(mtdc,      cap_eq)

`undef KE_CHK
`undef KE_CHKF

////////////////////// Group F: Kudu trap decisions vs spec traps //////////////////////

// Kudu decides a load/store or CSR trap in the LSU response cycle, from its
// own request (lsu_req_info_t): the CHERI load/store checks (lsu_if delay
// register or LSU, check_ls_err) or the CSR legality/ASR checks. Each LSQ
// entry records the request ls_pipeline built at issue (kreq). These
// invariants carry kreq through lsu_if and the LSU, and tie the spec trap
// recorded at issue to Kudu's check of kreq.
function automatic cheri_pkg::lschk_err_t f_chk(super_pkg::lsu_req_info_t r);
  return cheri_pkg::check_ls_err(1'b1, 1'b0, r.cs1_fcap, r.cs2_valid, r.cs2_perms,
                                 r.addr, r.is_load, r.is_cap, r.data_type, r.amo_flag);
endfunction
// A stored lschk_err is either the decode default (0) or lsu_if's check of
// the same request; the LSU ORs it with its own check (CSR: ignored).
function automatic logic f_lschk_ok(super_pkg::lsu_req_info_t r);
  return r.is_csr || (r.lschk_err == '0) || (r.lschk_err == f_chk(r));
endfunction
// The request fields Kudu's trap decision and load result depend on.
function automatic logic f_req_eq(super_pkg::lsu_req_info_t a, super_pkg::lsu_req_info_t b);
  return (a.is_csr == b.is_csr) && (a.is_load == b.is_load) && (a.is_cap == b.is_cap) &&
         (a.amo_flag == b.amo_flag) && (a.data_type == b.data_type) && (a.addr == b.addr) &&
         (a.insn == b.insn) && (a.pc == b.pc) && (a.cs1_fcap == b.cs1_fcap) &&
         (a.cs2_valid == b.cs2_valid) && (a.cs2_perms == b.cs2_perms) &&
         (a.rs1 == b.rs1) && (a.mie == b.mie) && (a.rf_we == b.rf_we) && (a.rd == b.rd) &&
         (a.clrperm == b.clrperm) && (a.sign_ext == b.sign_ext) &&
         (a.early_load == b.early_load);
endfunction
// Mirror of load_store_unit csr_err (pmode 1, debug 0) for in-scope CSR
// instructions: cs_registers illegal_csr_insn (unknown SCR, write to a
// read-only CSR, privilege) or a missing PCC ASR permission. Inv_F_CsrErr
// checks it against the RTL.
// cs_registers illegal_csr_insn part of f_csr_err.
function automatic logic f_csr_ill(logic [31:0] insn, t_Privilege priv);
  logic        cheri, rd_only, ill_addr, ill_wr, ill_priv;
  logic [11:0] addr;
  cheri     = (insn[6:0] == 7'h5b);
  rd_only   = cheri ? (insn[19:15] == 5'd0) :
              ((insn[13:12] == 2'b00) || (insn[13] && (insn[19:15] == 5'd0)));
  addr      = cheri ? {7'h0, insn[24:20]} : insn[31:20];
  ill_addr  = cheri && !((insn[24:20] == cheri_pkg::CHERI_SCR_MEPCC) ||
                         (insn[24:20] == cheri_pkg::CHERI_SCR_MSCRATCHC) ||
                         (insn[24:20] == cheri_pkg::CHERI_SCR_MTDC) ||
                         (insn[24:20] == cheri_pkg::CHERI_SCR_MTCC));
  ill_wr    = (addr[11:10] == 2'b11) && !rd_only;
  ill_priv  = (addr[9:8] > ((priv == Machine) ? 2'b11 : 2'b00));
  return ill_addr || ill_wr || ill_priv;
endfunction
function automatic logic f_csr_err(logic [31:0] insn, t_Privilege priv,
                                   logic [super_pkg::RegW-1:0] pc);
  logic                         cheri, rd_only, ill_addr, ill_wr, ill_priv, always_ok;
  logic [11:0]                  addr;
  cheri_pkg::reg_cap_t          pcap;
  logic [cheri_pkg::PERMS_W-1:0] perms;
  cheri     = (insn[6:0] == 7'h5b);
  rd_only   = cheri ? (insn[19:15] == 5'd0) :
              ((insn[13:12] == 2'b00) || (insn[13] && (insn[19:15] == 5'd0)));
  addr      = cheri ? {7'h0, insn[24:20]} : insn[31:20];
  ill_addr  = cheri && !((insn[24:20] == cheri_pkg::CHERI_SCR_MEPCC) ||
                         (insn[24:20] == cheri_pkg::CHERI_SCR_MSCRATCHC) ||
                         (insn[24:20] == cheri_pkg::CHERI_SCR_MTDC) ||
                         (insn[24:20] == cheri_pkg::CHERI_SCR_MTCC));
  ill_wr    = (addr[11:10] == 2'b11) && !rd_only;
  ill_priv  = (addr[9:8] > ((priv == Machine) ? 2'b11 : 2'b00));
  always_ok = !cheri && rd_only && ((insn[31:28] == 4'hb) || (insn[31:28] == 4'hc)) &&
              (!insn[27] || (insn[26:25] == 2'b00));
  pcap      = cheri_pkg::reg_cap_t'(pc);
  perms     = cheri_pkg::expand_perms(pcap.cperms);
  return ill_addr || ill_wr || ill_priv || (!perms[cheri_pkg::PERM_SR] && !always_ok);
endfunction
// Kudu's trap for an entry, at the entry's spec pre-state privilege.
function automatic logic f_ktrap(lsq_ent_t e);
  return e.kreq.is_csr ? f_csr_err(e.kreq.insn, e.pre.priv, e.kreq.pc) : f_chk(e.kreq).any_fault;
endfunction

Inv_F_CsrErr: assert property (`KLSU.csr_go_q && `KLSU.lsu_req_info_q.is_csr |->
                               `KLSU.csr_err == f_csr_err(`KLSU.lsu_req_info_q.insn, dut_priv,
                                                         `KLSU.lsu_req_info_q.pc));

// Kudu's PCC ASR permission as the LSU sees it (lsu_req_info_t.pc is
// pcc2regcap of the EX1 PCC).
function automatic logic f_pcc_sr(cheri_pkg::pcc_cap_t p, logic [31:0] pc);
  cheri_pkg::reg_cap_t           r;
  logic [cheri_pkg::PERMS_W-1:0] perms;
  r     = cheri_pkg::pcc2regcap(p, pc, 1'b0);
  perms = cheri_pkg::expand_perms(r.cperms);
  return perms[cheri_pkg::PERM_SR];
endfunction

// Outside the shadow the spec privilege and PCC ASR permission are Kudu's:
// both change only at CJALR (EX1, at issue), serialised steps
// and traps, applied by Kudu in the cycle spec_past_* is updated (or, for a
// trap, at the flush that ends the shadow). The full PCC is not compared:
// a CJALR to a malformed capability (exponent > 24, not reachable in a
// register) decodes to different bounds in Kudu and the spec.
Inv_F_Priv:  assert property (past_valid && !shadow_q |-> past_priv == dut_priv);
// In a trap's shadow spec_past_* is the trap's post-state, whose PCC is MTCC
// (the next PC is its address with the mode bits cleared). An untagged MTCC
// is installed with its raw fields too (prepare_trap_vector: nextPCC = MTCC),
// so the spec PCC is MTCC exactly, divergence G included; Inv_F_Pcc then
// compares Kudu's flushed PCC with it (tag only for untagged E > 24).
// The spec's main_inner (from cheriot-ibex, issue #11) clears nextPCC.B[8]
// whenever E is the maximum (24), so compare against MTCC normalised the same way.
// prepare_trap_vector installs MTCC itself, so the PCC address (from which
// F_PccBnd decodes the bounds Kudu takes at the flush) is MTCC's too.
function automatic t_Capability inv_pcc_norm(t_Capability c);
  if (c.E == 24) c.B[8] = 1'b0;
  return c;
endfunction
Inv_F_ShPcc: assert property (past_valid && shadow_q |->
                              (past_pcc.tag == past_mtvec.tag) &&
                              (past_pcc.access_system_regs == past_mtvec.access_system_regs) &&
                              cap_eq_noaddr(past_pcc, inv_pcc_norm(past_mtvec)) &&
                              (past_pcc.address == past_mtvec.address));
// In the shadow the spec has taken the trap: its PC is the (aligned) MTCC
// address, which Kudu's flush loads as special_pc_q (Exc_FlushPC).
Inv_F_ShPc: assert property (past_valid && shadow_q |-> past_pc == past_mtvec.address);
// An untagged PCC faults every fetch, so its ASR is unobservable (and may
// differ: README 1.1, untagged E>24 MEPCC installed by MRET).
Inv_F_PccSr: assert property (past_valid && !shadow_q && past_pcc.tag |->
                              past_pcc.access_system_regs == f_pcc_sr(`KCSR.ex1_pcc_cap_q, past_pc));
// Full PCC link outside the shadow (as Special_State/Post_Pcc check it at
// special steps): an LS trap's MEPCC is pcc2regcap of this PCC (kreq.pc), so
// F_LsqCause/F_CurCause need it at push.
// Only divergence G (untagged, E > 24) loses raw bounds; any other untagged
// PCC is kept exactly, since a trap copies it into MEPCC (xepc_eq).
function automatic logic f_pcc_eq_k(t_Capability k, t_Capability s);
  if (!k.tag && !s.tag && (s.E > 5'd24)) return 1'b1;
  return cap_eq_noaddr(k, s);
endfunction
Inv_F_Pcc:   assert property (past_valid && !shadow_q |->
                              f_pcc_eq_k(dut_pcc_at(past_pc), past_pcc));
// Kudu's PCC also keeps decoded base32/top33, which pcc2fullcap's set_address
// uses for the representability check that sets an LS trap's MEPCC tag. They
// are the spec PCC's bounds decoded at its own address (as cap_well_formed
// decodes); after a CJALR the PC is the target but the address is cs1's.
function automatic logic [64:0] inv_cap_bounds(t_Capability c, logic [31:0] addr);
  longint a_top, a_hi, t_hi, base, top;
  int     e;
  e     = int'(c.E);
  a_hi  = (9'((addr >> e)) < c.B) ? 1 : 0;
  t_hi  = (c.T < c.B) ? 1 : 0;
  a_top = longint'(addr >> (e + 9));
  base  = ((a_top - a_hi) << (e + 9)) + (longint'(c.B) << e);
  top   = ((a_top + t_hi - a_hi) << (e + 9)) + (longint'(c.T) << e);
  return {top[32:0], base[31:0]};
endfunction
Inv_F_PccBnd: assert property (past_valid && !shadow_q && past_pcc.tag |->
                               {`KCSR.ex1_pcc_cap_q.top33, `KCSR.ex1_pcc_cap_q.base32} ==
                               inv_cap_bounds(past_pcc, past_pcc.address));

// The requests in lsu_if and the LSU carry their entries' kreq.
Inv_F_LsifHd:  assert property ((lsq_cnt_q != 3'd0) |-> f_req_eq(inv_lsif_hd, lsq_mem[lsq_rp_q].kreq));
Inv_F_LsifNx:  assert property ((lsq_cnt_q >= 3'd2) |->
                                f_req_eq(`KLSIF.req_dly_q, lsq_mem[2'(lsq_rp_q + 2'd1)].kreq));
Inv_F_LsuCur:  assert property (`KLSU.outstanding_resp_q |-> f_req_eq(`KLSU.lsu_req_info_q, lsq_cur_q.kreq));
Inv_F_ChkDly:  assert property (f_lschk_ok(`KLSIF.req_dly_q));
Inv_F_ChkHold: assert property (f_lschk_ok(`KLSIF.req_hold_q));
// lsu_if presents the hold register in DLY0_WGNT / DLY1_WGNT. DLY1_WGNT is
// entered only from DLY1 (xfr2hold1: req_dly_tmp, check filled in) and
// DLY0_WGNT only for an early load (xfr2hold0); the LSU issues the bus
// request at ls_go from this lschk_err.
Inv_F_HoldChk:   assert property ((`KLSIF.lsif_fsm_q == 3'd3) |->
                                  (`KLSIF.req_hold_q.lschk_err == f_chk(`KLSIF.req_hold_q)));
Inv_F_HoldEarly: assert property ((`KLSIF.lsif_fsm_q == 3'd1) |-> `KLSIF.req_hold_q.early_load);
Inv_F_ChkLsu:  assert property (f_lschk_ok(`KLSU.lsu_req_info_q));

// Entry traps: outside the shadow, the spec trap is Kudu's check of kreq.
// Privilege does not change while a non-shadow entry is pending.
// Only loads and CSR instructions write a register (A is out of scope, so no
// SC); otherwise a store's response would write bus data. A CSR request's
// cs1_fcap (SCR write data) is a register value, so it is well formed.
// Without A (no LR/SC, cmplx_unit idle) no request carries an AMO flag.
function automatic logic f_kreq_we_ok(super_pkg::lsu_req_info_t r);
  return (!r.rf_we || r.is_load || r.is_csr) && (r.amo_flag == '0) &&
         (!r.is_csr || inv_cap_ok(op2sail(r.cs1_fcap)));
endfunction
// ls_pipeline builds the request from the (expanded) instruction word alone:
// is_csr (Zicsr or CSpecialRW), otherwise a LOAD/STORE with is_load = LOAD,
// is_cap = CLC/CSC (funct3 3, pmode 1), data_type from funct3[1:0] and
// sign_ext = !funct3[2]. The spec accesses memory exactly for a non-trapping
// load (read) or store (write); a CSR instruction does neither.
function automatic logic f_is_csr(logic [31:0] insn);
  return ((insn[6:0] == 7'h73) && (insn[14:12] != 3'd0)) ||
         ((insn[6:0] == 7'h5b) && (insn[14:12] == 3'd0) && (insn[31:25] == 7'h01));
endfunction
function automatic logic f_kreq_dec_ok(super_pkg::lsu_req_info_t r);
  logic [1:0] dt;
  dt = (r.insn[13:12] == 2'b00) ? 2'b10 : (r.insn[13:12] == 2'b01) ? 2'b01 : 2'b00;
  return (r.is_csr == f_is_csr(r.insn)) &&
         // ls_pipeline sets early_load on every CSR request and only on loads
         // otherwise (it lets a trapping early load issue its read, Mem_GoTrap).
         (r.is_csr ? (!r.is_load && !r.is_cap && r.early_load) :
                     (!r.early_load || r.is_load)) &&
         (r.is_csr ? 1'b1 :
                     (((r.insn[6:0] == 7'h03) || (r.insn[6:0] == 7'h23)) &&
                      (r.is_load == (r.insn[6:0] == 7'h03)) &&
                      (r.is_cap == (r.insn[14:12] == 3'd3)) &&
                      (r.data_type == dt) && (r.sign_ext == !r.insn[14])));
endfunction
// Env_NoDivGRd0/1 exclude a MEPCC read of a divergence-G MEPCC at issue; carry
// that to every queued CSR request until its read (csr_chk1_q).
function automatic logic f_nodivg_ok(lsq_ent_t x);
  return !f_mepc_rd(x.insn) || !f_mepc_lossy(x.pre.mepc);
endfunction
function automatic logic f_rw_ok(lsq_ent_t x);
  return x.trap || ((x.rd == (!x.csr && x.kreq.is_load)) && (x.wr == (!x.csr && !x.kreq.is_load)));
endfunction
for (genvar k = 0; k < LsqDepth; k++) begin : g_inv_lsqf
  lsq_ent_t ent;
  logic     occ;
  assign ent = lsq_mem[2'(lsq_rp_q + 2'(k))];
  assign occ = 3'(k) < lsq_cnt_q;
  Inv_F_LsqReq:  assert property (occ |-> (ent.kreq.is_csr == ent.csr) && (ent.kreq.insn == ent.insn) &&
                                         f_kreq_we_ok(ent.kreq));
  Inv_F_LsqDec:  assert property (occ |-> f_kreq_dec_ok(ent.kreq));
  Inv_F_LsqNoDivG: assert property (occ && !ent.shadow && !ent.trap |-> f_nodivg_ok(ent));
  Inv_F_LsqRw:   assert property (occ && !ent.shadow |-> f_rw_ok(ent));
  Inv_F_LsqTrap: assert property (occ && !ent.shadow |-> ent.trap == f_ktrap(ent));
  Inv_F_LsqPriv: assert property (occ && !ent.shadow |-> ent.pre.priv == dut_priv);
end
Inv_F_CurReq:  assert property (`KLSU.outstanding_resp_q |->
                                (lsq_cur_q.kreq.is_csr == lsq_cur_q.csr) &&
                                (lsq_cur_q.kreq.insn == lsq_cur_q.insn) &&
                                f_kreq_we_ok(lsq_cur_q.kreq));
Inv_F_CurNoDivG:  assert property (`KLSU.outstanding_resp_q && !lsq_cur_q.shadow && !lsq_cur_q.trap |->
                                   f_nodivg_ok(lsq_cur_q));
Inv_F_Chk1NoDivG: assert property (csr_chk1_q |-> f_nodivg_ok(csr_ent1_q));
Inv_F_CurDec:  assert property (`KLSU.outstanding_resp_q |-> f_kreq_dec_ok(lsq_cur_q.kreq));
Inv_F_CurRw:   assert property (`KLSU.outstanding_resp_q && !lsq_cur_q.shadow |-> f_rw_ok(lsq_cur_q));
Inv_F_CurTrap: assert property (`KLSU.outstanding_resp_q && !lsq_cur_q.shadow |->
                                lsq_cur_q.trap == f_ktrap(lsq_cur_q));
Inv_F_CurPriv: assert property (`KLSU.outstanding_resp_q && !lsq_cur_q.shadow |->
                                lsq_cur_q.pre.priv == dut_priv);
// Kudu's request address is the spec's memory address (aligned-word spec
// memory: a split access's second word is the next one).
// Sail's checked_mem_read/write access the aligned word and, when the access
// crosses it, the next word (non-capability accesses only).
function automatic logic f_kreq_split(super_pkg::lsu_req_info_t r);
  return !r.is_cap && (((r.data_type == 2'b00) && (r.addr[1:0] != 2'b00)) ||
                       ((r.data_type == 2'b01) && (r.addr[1:0] == 2'b11)));
endfunction
function automatic logic f_addr_ok(lsq_ent_t x);
  return (!x.rd || ((x.kreq.addr[31:2] == x.rd_fst_addr[31:2]) && (x.rd_fst_addr[1:0] == 2'b00) &&
                    (x.kreq.is_cap || (x.rd_snd == f_kreq_split(x.kreq))) &&
                    (!x.rd_snd || (x.rd_snd_addr == x.rd_fst_addr + 32'd4)))) &&
         (!x.wr || ((x.kreq.addr[31:2] == x.wr_fst_addr[31:2]) && (x.wr_fst_addr[1:0] == 2'b00) &&
                    (x.kreq.is_cap || (x.wr_snd == f_kreq_split(x.kreq))) &&
                    (!x.wr_snd || (x.wr_snd_addr == x.wr_fst_addr + 32'd4))));
endfunction
for (genvar k = 0; k < LsqDepth; k++) begin : g_inv_lsqa
  lsq_ent_t ent;
  assign ent = lsq_mem[2'(lsq_rp_q + 2'(k))];
  Inv_F_LsqAddr: assert property ((3'(k) < lsq_cnt_q) && !ent.shadow && !ent.trap |-> f_addr_ok(ent));
end
Inv_F_CurAddr: assert property (`KLSU.outstanding_resp_q && !lsq_cur_q.shadow && !lsq_cur_q.trap |->
                                f_addr_ok(lsq_cur_q));

// Store data. f_req_eq leaves wdata out; lsu_if passes it through unchanged
// except that req_dly_tmp (DLY1 output, copied to req_hold_q by xfr2hold1)
// clears the tag on an SLC fault. The hold register is presented in
// DLY0/DLY1_WGNT; DLY0_WGNT holds only early loads, whose wdata is unused.
function automatic logic f_wd_eq(super_pkg::lsu_req_info_t a, super_pkg::lsu_req_info_t b, logic clr);
  return b.is_csr || b.is_load ||
         ((a.wdata[cheri_pkg::MEM_TAG-1:0] == b.wdata[cheri_pkg::MEM_TAG-1:0]) &&
          (a.wdata[cheri_pkg::MEM_TAG] == (b.wdata[cheri_pkg::MEM_TAG] && !(clr && f_chk(b).slc))));
endfunction
Inv_F_LsifHdWd: assert property ((lsq_cnt_q != 3'd0) |->
                                 f_wd_eq(inv_lsif_hd, lsq_mem[lsq_rp_q].kreq,
                                         (`KLSIF.lsif_fsm_q inside {3'd1, 3'd3}) && inv_ls_idle));
Inv_F_LsifNxWd: assert property ((lsq_cnt_q >= 3'd2) |->
                                 f_wd_eq(`KLSIF.req_dly_q, lsq_mem[2'(lsq_rp_q + 2'd1)].kreq, 1'b0));
Inv_F_LsuCurWd: assert property (`KLSU.outstanding_resp_q |-> f_wd_eq(`KLSU.lsu_req_info_q, lsq_cur_q.kreq, 1'b1));
// The spec's access width and store bytes are those of Kudu's request: the
// LSU byte enables are the size mask shifted by the address offset (split
// over the two words) and both words carry wdata rotated left by the offset.
function automatic logic [7:0] f_kbe(super_pkg::lsu_req_info_t r);
  logic [3:0] m;
  m = (r.data_type == 2'b00) ? 4'hf : (r.data_type == 2'b01) ? 4'h3 : 4'h1;
  return {4'h0, m} << r.addr[1:0];
endfunction
function automatic logic [31:0] f_krot(super_pkg::lsu_req_info_t r);
  logic [63:0] w2;
  w2 = {r.wdata[31:0], r.wdata[31:0]} << {r.addr[1:0], 3'b000};
  return w2[63:32];
endfunction
function automatic logic f_wr_ok(lsq_ent_t x);
  logic [7:0] be;
  be = f_kbe(x.kreq);
  return (!x.rd || (x.rd_cap == x.kreq.is_cap)) &&
         (!x.wr || ((x.wr_cap == x.kreq.is_cap) &&
                    (x.kreq.is_cap ?
                       ((x.wr_fst_data == x.kreq.wdata[31:0]) &&
                        (x.wr_tag == (x.kreq.wdata[cheri_pkg::MEM_TAG] && !f_chk(x.kreq).slc)) &&
                        (!x.wr_tag || cap_eq(memcap2sail(cheri_pkg::mem_cap_t'(x.kreq.wdata)),
                                             capBitsToCapability(1'b1, {x.wr_snd_data, x.wr_fst_data})))) :
                       ((x.wr_fst_be == be[3:0]) && be_data_eq(x.wr_fst_be, x.wr_fst_data, f_krot(x.kreq)) &&
                        (!x.wr_snd || ((x.wr_snd_be == be[7:4]) &&
                                       be_data_eq(x.wr_snd_be, x.wr_snd_data, f_krot(x.kreq))))))));
endfunction
for (genvar k = 0; k < LsqDepth; k++) begin : g_inv_lsqst
  lsq_ent_t ent;
  assign ent = lsq_mem[2'(lsq_rp_q + 2'(k))];
  Inv_F_LsqWr: assert property ((3'(k) < lsq_cnt_q) && !ent.shadow && !ent.trap |-> f_wr_ok(ent));
end
Inv_F_CurWr: assert property (`KLSU.outstanding_resp_q && !lsq_cur_q.shadow && !lsq_cur_q.trap |->
                              f_wr_ok(lsq_cur_q));

// CSR write post-state: a mirror of cs_registers' Zicsr read-modify-write
// for the plain 32-bit CSRs (mstatus, mie, mscratch, mcause, mtval, mshwmb) applied to the
// entry's pre-state and Kudu request. The spec computes the entry's post at
// issue; Kudu applies the write later at csr_chk1_q, so the entry must carry
// a post-state consistent with what Kudu will write.
function automatic logic f_csr_simple(logic [31:0] insn);
  return (insn[6:0] == 7'h73) && (insn[14:12] != 3'd0) &&
         ((insn[31:20] == 12'h300) || (insn[31:20] == 12'h304) ||
          (insn[31:20] == 12'h340) || (insn[31:20] == 12'h342) ||
          (insn[31:20] == 12'h343) || (insn[31:20] == 12'hbc2));
endfunction
function automatic e_st_t f_csr_post(lsq_ent_t x);
  e_st_t       r;
  logic [31:0] wd, old, nw;
  logic [11:0] a;
  r.priv = x.pre.priv; r.mstatus = x.pre.mstatus; r.mie = x.pre.mie;
  r.mcause = x.pre.mcause; r.mtval = x.pre.mtval; r.mscratch = x.pre.mscratch;
  r.mshwmb = x.pre.mshwmb; r.mtvec = x.pre.mtvec; r.mepc = x.pre.mepc;
  r.mscratchc = x.pre.mscratchc; r.mtdc = x.pre.mtdc;
  a  = x.insn[31:20];
  wd = x.insn[14] ? {27'h0, x.insn[19:15]} : x.kreq.cs1_fcap[31:0];
  old = '0;
  case (a)
    12'h300: begin
      old[3] = x.pre.mstatus.mie;  old[7] = x.pre.mstatus.mpie;
      old[12:11] = x.pre.mstatus.mpp; old[17] = x.pre.mstatus.mprv;
      old[21] = x.pre.mstatus.tw;
    end
    12'h304: old = x.pre.mie;
    12'h340: old = x.pre.mscratch;
    12'h342: old = x.pre.mcause;
    12'h343: old = x.pre.mtval;
    12'hbc2: old = x.pre.mshwmb;
    default: ;
  endcase
  // csrrs/csrrc with rs1 = x0 / uimm = 0 do not write (no legalisation).
  if (x.insn[13] && (x.insn[19:15] == 5'd0)) return r;
  case (x.insn[13:12])
    2'b01:   nw = wd;
    2'b10:   nw = old | wd;
    default: nw = old & ~wd;
  endcase
  case (a)
    12'h300: begin
      r.mstatus.mie = nw[3]; r.mstatus.mpie = nw[7]; r.mstatus.mprv = nw[17];
      r.mstatus.tw  = nw[21];
      r.mstatus.mpp = ((nw[12:11] == 2'b11) || (nw[12:11] == 2'b00)) ? nw[12:11] : 2'b11;
    end
    12'h304: r.mie = nw & 32'h7fff_0888;
    12'h340: r.mscratch = nw;
    // mcause is WLRL: the spec (patched like Kudu, README 1.1) keeps 31 and 4:0.
    12'h342: r.mcause = {nw[31], 26'h0, nw[4:0]};
    12'h343: r.mtval = nw;
    12'hbc2: r.mshwmb = {nw[31:4], 4'h0};   // legalize_mshwm
    default: ;
  endcase
  return r;
endfunction

// CSpecialRW to an existing SCR (cheri_insts.sail execute CSpecialRW): with
// cs1 != 0 the SCR takes cs1; MTCC/MEPCC clear the address alignment bits
// and drop the tag if they were set or the cap is sealed or not executable.
function automatic logic f_csr_cap(logic [31:0] insn);
  return (insn[6:0] == 7'h5b) && (insn[14:12] == 3'd0) && (insn[31:25] == 7'h01) &&
         (insn[24:22] == 3'b111);
endfunction
function automatic e_st_t f_csr_cap_post(lsq_ent_t x);
  e_st_t       r;
  t_Capability c;
  logic        inv;
  r.priv = x.pre.priv; r.mstatus = x.pre.mstatus; r.mie = x.pre.mie;
  r.mcause = x.pre.mcause; r.mtval = x.pre.mtval; r.mscratch = x.pre.mscratch;
  r.mshwmb = x.pre.mshwmb; r.mtvec = x.pre.mtvec; r.mepc = x.pre.mepc;
  r.mscratchc = x.pre.mscratchc; r.mtdc = x.pre.mtdc;
  if (x.insn[19:15] == 5'd0) return r;
  c = op2sail(x.kreq.cs1_fcap);
  case (x.insn[24:20])
    cheri_pkg::CHERI_SCR_MTCC: begin
      inv = (c.address[1:0] != 2'b00) || (c.otype != 4'd0) || !c.permit_execute;
      c.address[1:0] = 2'b00;
      if (inv) c.tag = 1'b0;
      r.mtvec = c;
    end
    cheri_pkg::CHERI_SCR_MEPCC: begin
      inv = c.address[0] || (c.otype != 4'd0) || !c.permit_execute;
      c.address[0] = 1'b0;
      if (inv) c.tag = 1'b0;
      r.mepc = c;
    end
    cheri_pkg::CHERI_SCR_MTDC:      r.mtdc = c;
    default:                        r.mscratchc = c;
  endcase
  return r;
endfunction
// Any in-scope CSR instruction (top.sv insn_in_scope): the other CSRs it can
// access (misa, mshwm, read-only IDs) are not part of e_st_t.
function automatic e_st_t f_csr_all(lsq_ent_t x);
  if (f_csr_cap(x.insn))    return f_csr_cap_post(x);
  if (f_csr_simple(x.insn)) return f_csr_post(x);
  return x.pre;
endfunction

// The LSU's CSR request is the entry's.
Inv_F_Chk1Req:  assert property (csr_chk1_q |-> f_req_eq(`KLSU.lsu_req_info_q, csr_ent1_q.kreq));
Inv_F_Chk1Post: assert property (csr_chk1_q && !csr_ent1_q.shadow && !csr_ent1_q.trap |->
                                 e_st_eq(e_post(csr_ent1_q), f_csr_all(csr_ent1_q), 1'b1));
for (genvar k = 0; k < LsqDepth; k++) begin : g_inv_lsqp
  lsq_ent_t ent;
  logic     occ;
  assign ent = lsq_mem[2'(lsq_rp_q + 2'(k))];
  assign occ = 3'(k) < lsq_cnt_q;
  Inv_F_LsqPost: assert property (occ && !ent.shadow && !ent.trap && ent.csr |->
                                  e_st_eq(e_post(ent), f_csr_all(ent), 1'b1));
end
// Kudu's response error is the spec trap.
Inv_F_RespTrap: assert property (`KLSU.lsu_resp_valid && !lsq_cur_q.shadow |->
                                 `KLSU.lsu_resp_err == lsq_cur_q.trap);

// The shadow has a source: the trapping LS instruction is still in the LSQ,
// in the LSU, or has responded with an error (latched until the flush).
logic [LsqDepth-1:0] f_lsq_src;
for (genvar k = 0; k < LsqDepth; k++) begin : g_inv_lsqs
  assign f_lsq_src[k] = (3'(k) < lsq_cnt_q) && g_inv_lsqf[k].ent.trap && !g_inv_lsqf[k].ent.shadow;
end
Inv_F_ShSrc: assert property (shadow_q |-> `KLSP.resp_err_latched || `KCMT.cmt_err_q ||
                              (`KLSU.outstanding_resp_q && lsq_cur_q.trap && !lsq_cur_q.shadow) ||
                              (|f_lsq_src));

// A CSR request is a legal, in-scope Zicsr instruction (funct3[1:0] = 00 is
// illegal in ir_decoder and traps at issue) or a CSpecialRW.
function automatic logic f_csr_ok(logic [31:0] insn);
  return ((insn[6:0] == 7'h73) && (insn[13:12] != 2'b00) && insn_in_scope(insn, 1'b0, 16'h0)) ||
         ((insn[6:0] == 7'h5b) && (insn[14:12] == 3'd0) && (insn[31:25] == 7'h01));
endfunction
// A trap writes only mcause, mtval, MEPCC, mstatus.mie/mpie/mpp and priv.
function automatic logic e_keep_eq(e_st_t a, e_st_t b);
  return (a.mie == b.mie) && (a.mscratch == b.mscratch) && (a.mshwmb == b.mshwmb) &&
         (a.mstatus.tw == b.mstatus.tw) && (a.mstatus.mprv == b.mstatus.mprv) &&
         cap_eq(a.mtvec, b.mtvec) && cap_eq(a.mscratchc, b.mscratchc) && cap_eq(a.mtdc, b.mtdc);
endfunction

// The mstatus/priv fields a trap writes (Sail trap handler): MIE cleared,
// MPP = the pre-state privilege, Machine mode.
function automatic logic e_trap_mst(e_st_t pre, e_st_t post);
  return !post.mstatus.mie && (post.priv == Machine) &&
         (post.mstatus.mpp == ((pre.priv == Machine) ? 2'b11 : 2'b00));
endfunction

// In a trap's shadow spec_past_* is frozen at the trap's post-state, which
// the trapping (shadow-source) entry recorded.
for (genvar k = 0; k < LsqDepth; k++) begin : g_inv_lsqt
  Inv_E_LsqCsrOk:  assert property ((3'(k) < lsq_cnt_q) && g_inv_lsqf[k].ent.csr |->
                                    f_csr_ok(g_inv_lsqf[k].ent.insn));
  Inv_E_LsqTKeep:  assert property (f_lsq_src[k] |->
                                    e_keep_eq(g_inv_lsqf[k].ent.pre, e_post(g_inv_lsqf[k].ent)));
  Inv_E_LsqTMst:   assert property (f_lsq_src[k] |->
                                    e_trap_mst(g_inv_lsqf[k].ent.pre, e_post(g_inv_lsqf[k].ent)));
  Inv_E_LsqShPast: assert property (shadow_q && f_lsq_src[k] |->
                                    e_st_eq(e_post(g_inv_lsqf[k].ent), e_st_past, 1'b1));
end
logic e_cur_src;
assign e_cur_src = e_cur_live && lsq_cur_q.trap && !lsq_cur_q.shadow;
Inv_E_Chk1CsrOk: assert property (csr_chk1_q |-> f_csr_ok(csr_ent1_q.insn));
Inv_E_CurTKeep:  assert property (e_cur_src |-> e_keep_eq(lsq_cur_q.pre, e_post(lsq_cur_q)));
Inv_E_CurTMst:   assert property (e_cur_src |-> e_trap_mst(lsq_cur_q.pre, e_post(lsq_cur_q)));
Inv_E_CurShPast: assert property (shadow_q && e_cur_src |-> e_st_eq(e_post(lsq_cur_q), e_st_past, 1'b1));
// The LS request in flight is the oldest pending step. A trapping CSR
// request never reaches csr_chk1_q, so e_cur stays at its pre-state.
Inv_E_CurPre:    assert property (past_valid && e_cur_live && !lsq_cur_q.shadow &&
                                  (!lsq_cur_q.csr || lsq_cur_q.trap) &&
                                  !csr_chk1_q |-> e_st_eq(e_st_cur, lsq_cur_q.pre, 1'b0));
Inv_E_CurCsrOk:  assert property (e_cur_live && lsq_cur_q.csr && !lsq_cur_q.shadow |->
                                  (lsq_cur_q.kreq.is_csr && (lsq_cur_q.kreq.insn == lsq_cur_q.insn) &&
                                   f_csr_ok(lsq_cur_q.insn)));

// In a trap's shadow, once every older step has been applied (whatever the
// shadow source), e_cur is the trap's pre-state: the fields the trap leaves
// alone equal spec_past_*, and the trap entered Machine mode.
logic [LsqDepth-1:0] e_lsq_old;
for (genvar k = 0; k < LsqDepth; k++) begin : g_inv_lsqo
  assign e_lsq_old[k] = (3'(k) < lsq_cnt_q) && !g_inv_lsqf[k].ent.shadow && !g_inv_lsqf[k].ent.trap;
end
logic e_older_pend;
assign e_older_pend = csr_chk1_q || (|e_lsq_old) ||
                      (e_cur_live && !lsq_cur_q.shadow && !lsq_cur_q.trap);
// A latched LS error is the spec trap of the request in lsq_cur_q (the LSU
// accepts nothing after it), and the trap info Kudu carries to the CSRs (the
// erroring wb_fifo entry, then committer cmt_err_info_q) gives that trap's
// post-state: mcause, mtval, MEPCC, and mpie = the mie captured at issue.
function automatic logic e_err_ok(logic [super_pkg::RegW-1:0] pc, logic mie,
                                  logic [5:0] mcause, logic [31:0] mtval, lsq_ent_t x);
  cheri_pkg::reg_cap_t rc;
  rc = cheri_pkg::reg_cap_t'(pc);
  return (widenMCause(mcause) == x.mcause) && (mtval == x.mtval) &&
         (mie == x.mstatus.mpie) && xepc_eq(regcap2sail(rc, rc.addr), x.mepc);
endfunction
Inv_E_ErrSrc:     assert property (`KLSP.resp_err_latched |-> lsq_cur_q.trap && !lsq_cur_q.shadow);
// Kudu's mcause/mtval for a trapping request (load_store_unit lsu_err_*,
// pmode 1, no bus error: Env_NoDataErr). A misalign fault is raised only for
// capability and AMO accesses, whose mtval is the request address.
function automatic logic [5:0] f_kmcause(lsq_ent_t e);
  logic [5:0] vc;
  if (e.kreq.is_csr)
    return f_csr_ill(e.kreq.insn, e.pre.priv) ? csr_pkg::EXC_CAUSE_ILLEGAL_INSN :
                                                csr_pkg::EXC_CAUSE_CHERI_FAULT;
  vc = cheri_pkg::vio_cause_enc(f_chk(e.kreq));
  if (vc[5])
    return (e.kreq.is_load && (e.kreq.amo_flag[3:2] == 2'b00)) ?
           csr_pkg::EXC_CAUSE_LOAD_ADDR_MISALIGN : csr_pkg::EXC_CAUSE_STORE_ADDR_MISALIGN;
  return csr_pkg::EXC_CAUSE_CHERI_FAULT;
endfunction
function automatic logic [31:0] f_kmtval(lsq_ent_t e);
  logic [5:0] vc;
  if (e.kreq.is_csr)
    return f_csr_ill(e.kreq.insn, e.pre.priv) ? 32'h0 :
           {21'h0, 1'b1, e.kreq.insn[24:20] & {5{e.kreq.insn[6:0] == 7'h5b}}, 5'h18};
  vc = cheri_pkg::vio_cause_enc(f_chk(e.kreq));
  return vc[5] ? e.kreq.addr : {22'h0, e.kreq.rs1, vc[4:0]};
endfunction
// Outside the shadow a trapping entry's spec trap is Kudu's trap of kreq
// (cause, mtval, MEPCC, mpie), the source of Inv_E_WbErrInfo/CmtErrInfo.
function automatic logic f_kcause_ok(lsq_ent_t e);
  return e_err_ok(e.kreq.pc, e.kreq.mie, f_kmcause(e), f_kmtval(e), e);
endfunction
for (genvar k = 0; k < LsqDepth; k++) begin : g_inv_lsqk
  Inv_F_LsqCause: assert property ((3'(k) < lsq_cnt_q) && !g_inv_lsqf[k].ent.shadow &&
                                   g_inv_lsqf[k].ent.trap |-> f_kcause_ok(g_inv_lsqf[k].ent));
end
Inv_F_CurCause: assert property (e_cur_live && !lsq_cur_q.shadow && lsq_cur_q.trap |->
                                 f_kcause_ok(lsq_cur_q));
Inv_F_LsuCause: assert property (`KLSU.outstanding_resp_q && !lsq_cur_q.shadow && `KLSU.lsu_resp_err_o |->
                                 (`KLSU.lsu_err_mcause == f_kmcause(lsq_cur_q)) &&
                                 (`KLSU.lsu_err_mtval == f_kmtval(lsq_cur_q)));
Inv_F_CsrIll:   assert property (`KLSU.csr_go_q && `KLSU.lsu_req_info_q.is_csr |->
                                 `KLSU.illegal_csr_insn_i == f_csr_ill(`KLSU.lsu_req_info_q.insn, dut_priv));
// Frame: a non-trapping CSR step changes only the SCR it addresses (exactly,
// so the relaxed xepc_eq on an untagged E>24 MEPCC cannot hide a change).
// Zicsr reaches MTCC/MEPCC only through mtvec/mepc.
function automatic logic e_csr_frame(lsq_ent_t x);
  logic       cheri;
  logic [4:0] scr;
  logic [11:0] ca;
  cheri = (x.insn[6:0] == 7'h5b);
  scr   = x.insn[24:20];
  ca    = x.insn[31:20];
  return (cheri ? (scr == 5'd28) : (ca == 12'h305)) || cap_eq(x.pre.mtvec, x.mtvec);
endfunction
function automatic logic e_csr_frame2(lsq_ent_t x);
  logic       cheri;
  logic [4:0] scr;
  logic [11:0] ca;
  cheri = (x.insn[6:0] == 7'h5b);
  scr   = x.insn[24:20];
  ca    = x.insn[31:20];
  return ((cheri ? (scr == 5'd31) : (ca == 12'h341)) || cap_eq(x.pre.mepc, x.mepc)) &&
         ((cheri && (scr == 5'd29)) || cap_eq(x.pre.mtdc, x.mtdc)) &&
         ((cheri && (scr == 5'd30)) || cap_eq(x.pre.mscratchc, x.mscratchc));
endfunction
for (genvar k = 0; k < LsqDepth; k++) begin : g_inv_lsqc
  Inv_E_LsqCsrFrm: assert property ((3'(k) < lsq_cnt_q) && g_inv_lsqf[k].ent.csr &&
                                    !g_inv_lsqf[k].ent.shadow && !g_inv_lsqf[k].ent.trap |->
                                    e_csr_frame(g_inv_lsqf[k].ent) && e_csr_frame2(g_inv_lsqf[k].ent));
end
Inv_E_CurCsrFrm:  assert property (e_cur_live && lsq_cur_q.csr && !lsq_cur_q.shadow && !lsq_cur_q.trap |->
                                   e_csr_frame(lsq_cur_q) && e_csr_frame2(lsq_cur_q));
Inv_E_Chk1CsrFrm: assert property (csr_chk1_q && !csr_ent1_q.shadow |->
                                   e_csr_frame(csr_ent1_q) && e_csr_frame2(csr_ent1_q));
// committer loads cmt_err_info_q only with has_pcc = 1, clrtag = 0 (reset
// leaves has_pcc = 0, which would make the CSRs take mpie/MEPCC from the PCC
// path instead of the latched trap info).
Inv_E_CmtErrPcc:  assert property (`KCMT.cmt_err_q |->
                                   `KCMT.cmt_err_info_q.has_pcc && !`KCMT.cmt_err_info_q.clrtag);
Inv_E_CmtErrInfo: assert property (`KCMT.cmt_err_q |->
                                   e_err_ok(`KCMT.cmt_err_info_q.pc, `KCMT.cmt_err_info_q.mie,
                                            `KCMT.cmt_err_info_q.mcause, `KCMT.cmt_err_info_q.mtval,
                                            lsq_cur_q));
for (genvar j = 0; j < 4; j++) begin : g_inv_wbe
  Inv_E_WbErrInfo: assert property (inv_wb_err[j] |->
                                    e_err_ok(g_inv_wb[j].ent.pc, g_inv_wb[j].ent.mie,
                                             g_inv_wb[j].ent.mcause, g_inv_wb[j].ent.mtval,
                                             lsq_cur_q));
end
Inv_E_ShKeep:    assert property (past_valid && shadow_q && !e_older_pend |->
                                  e_keep_eq(e_st_cur, e_st_past));
Inv_E_ShPriv:    assert property (past_valid && shadow_q |-> past_priv == Machine);

// Every full capability the LS pipeline receives is op2fullcap of an op_cap
// (issuer forwarding), so its derived fields (base32/top33/perms, used by
// set_address in CSpecialRW legalisation) are consistent with the rest.
function automatic logic f_fcap_wf(cheri_pkg::full_cap_t c);
  // derived fields agree with the op_cap form, and (for tagged caps) the
  // correction bits agree with the address as reg2opcap recomputes them
  return (c == cheri_pkg::op2fullcap(cheri_pkg::op_cap_t'(c[cheri_pkg::OpCapW-1:0]))) &&
         (!c.valid || (c[cheri_pkg::OpCapW-1:0] ==
                       cheri_pkg::reg2opcap(cheri_pkg::reg_cap_t'(c[cheri_pkg::RegCapW-1:0]))));
endfunction
for (genvar k = 0; k < LsqDepth; k++) begin : g_inv_lsqw
  Inv_F_LsqFcap: assert property ((3'(k) < lsq_cnt_q) |-> f_fcap_wf(g_inv_lsqf[k].ent.kreq.cs1_fcap));
end
Inv_F_CurFcap:  assert property (e_cur_live |-> f_fcap_wf(lsq_cur_q.kreq.cs1_fcap));
// A CSR request's cs1 (SCR write data) is a register value: well formed and
// canonical (Inv_A_LsuCs1WF needs it when lsu_if hands the request over).
function automatic logic f_cs1_ok(super_pkg::lsu_req_info_t r);
  return !r.is_csr || (inv_cap_ok(op2sail(r.cs1_fcap)) && inv_cap_canon(op2sail(r.cs1_fcap)));
endfunction
for (genvar k = 0; k < LsqDepth; k++) begin : g_inv_lsqc1
  Inv_F_LsqCs1WF: assert property ((3'(k) < lsq_cnt_q) |-> f_cs1_ok(g_inv_lsqf[k].ent.kreq));
end
Inv_F_HoldCs1WF: assert property (f_cs1_ok(`KLSIF.req_hold_q));
Inv_F_DlyCs1WF:  assert property (f_cs1_ok(`KLSIF.req_dly_q));
Inv_F_Chk1Fcap: assert property (csr_chk1_q |-> f_fcap_wf(csr_ent1_q.kreq.cs1_fcap));

////////////////////// Group M: mshwm //////////////////////

// The spec lowers mshwm when it steps a store with mshwmb <= addr < mshwm
// (ext_check_phys_mem_write); Kudu does so at the store's LSU response
// (cs_registers csr_mshwm_set, comparing addr[31:4], equivalent because both
// registers are 16-byte aligned). A CSR write to mshwm (0xbc1) is applied
// with the other CSRs (csr_chk1_q). m_cur is the spec mshwm Kudu has applied;
// the LSU's current request, csr_ent1_q and the LSQ entries chain through
// pre_mshwm -> mshwm in program order to spec_past_mshwm.
function automatic logic [31:0] m_post(lsq_ent_t x);
  logic [31:0] wd, nw;
  if (x.csr) begin
    if ((x.insn[6:0] != 7'h73) || (x.insn[31:20] != 12'hbc1) ||
        (x.insn[13] && (x.insn[19:15] == 5'd0))) return x.pre_mshwm;
    wd = x.insn[14] ? {27'h0, x.insn[19:15]} : x.kreq.cs1_fcap[31:0];
    case (x.insn[13:12])
      2'b01:   nw = wd;
      2'b10:   nw = x.pre_mshwm | wd;
      default: nw = x.pre_mshwm & ~wd;
    endcase
    return {nw[31:4], 4'h0};
  end
  if (!x.kreq.is_load && (x.kreq.addr >= x.pre.mshwmb) && (x.kreq.addr < x.pre_mshwm))
    return {x.kreq.addr[31:4], 4'h0};
  return x.pre_mshwm;
endfunction

logic [31:0] m_cur, m_prev;
logic        m_cur_pend, m_app_st;
assign m_cur_pend = `KLSU.outstanding_resp_q && !lsq_cur_q.csr;
assign m_app_st   = `KLSU.lsu_resp_valid && !`KLSU.lsu_resp_err && !`KLSU.lsu_req_info_q.is_csr;
assign m_prev     = csr_chk1_q ? csr_ent1_q.mshwm : (m_cur_pend ? lsq_cur_q.mshwm : m_cur);

always_ff @(posedge clk_i) begin
  if      (e_app_flush)   m_cur <= past_mshwm;
  else if (e_app_special) m_cur <= s0_post_mshwm;
  else if (e_app_csr)     m_cur <= csr_ent1_q.mshwm;
  else if (m_app_st)      m_cur <= lsq_cur_q.mshwm;
  else if (!past_valid)   m_cur <= dut_mshwm;
end

Inv_M_Cur:      assert property (past_valid |-> dut_mshwm == m_cur);
Inv_M_DutAlign: assert property ((dut_mshwm[3:0] == 4'h0) && (dut_mshwmb[3:0] == 4'h0));
Inv_M_PstAlign: assert property (past_valid |-> (past_mshwm[3:0] == 4'h0) && (past_mshwmb[3:0] == 4'h0));
Inv_M_AppExcl:  assert property (m_app_st |-> !(e_app_flush || e_app_special || e_app_csr));
// The LSU's current non-CSR request follows m_cur (a CSR request is applied
// at csr_chk1_q, before a younger request can start).
Inv_M_CurPre:   assert property (past_valid && m_cur_pend && !lsq_cur_q.shadow |->
                                 (lsq_cur_q.pre_mshwm == m_cur) &&
                                 (lsq_cur_q.pre.mshwmb == e_cur_mshwmb));
Inv_M_CurPost:  assert property (m_cur_pend && !lsq_cur_q.shadow && !lsq_cur_q.trap |->
                                 lsq_cur_q.mshwm == m_post(lsq_cur_q));
Inv_M_Chk1Pre:  assert property (past_valid && csr_chk1_q && !csr_ent1_q.shadow |->
                                 csr_ent1_q.pre_mshwm == m_cur);
Inv_M_Chk1Post: assert property (csr_chk1_q && !csr_ent1_q.shadow && !csr_ent1_q.trap |->
                                 csr_ent1_q.mshwm == m_post(csr_ent1_q));
Inv_M_HeadPre:  assert property (past_valid && (lsq_cnt_q != 3'd0) && !e_head.shadow |->
                                 e_head.pre_mshwm == m_prev);
for (genvar k = 0; k < LsqDepth; k++) begin : g_inv_lsqm
  lsq_ent_t ent, prv;
  logic     occ;
  assign ent = lsq_mem[2'(lsq_rp_q + 2'(k))];
  assign prv = lsq_mem[2'(lsq_rp_q + 2'(k) - 2'd1)];
  assign occ = 3'(k) < lsq_cnt_q;
  Inv_M_LsqPost: assert property (occ && !ent.shadow && !ent.trap |-> ent.mshwm == m_post(ent));
  Inv_M_LsqTKeep: assert property (f_lsq_src[k] |-> ent.mshwm == ent.pre_mshwm);
  Inv_M_LsqShPast: assert property (shadow_q && f_lsq_src[k] |-> ent.mshwm == past_mshwm);
  if (k > 0) begin : g_chain
    Inv_M_LsqChain: assert property (past_valid && occ && !ent.shadow |-> ent.pre_mshwm == prv.mshwm);
  end
end
Inv_M_Tail:     assert property (e_p && (lsq_cnt_q != 3'd0) |-> e_young.mshwm == past_mshwm);
Inv_M_CurPast:  assert property (e_p && (lsq_cnt_q == 3'd0) && m_cur_pend |->
                                 lsq_cur_q.mshwm == past_mshwm);
Inv_M_Chk1Past: assert property (e_p && (lsq_cnt_q == 3'd0) && csr_chk1_q |->
                                 csr_ent1_q.mshwm == past_mshwm);
Inv_M_Eq:       assert property (e_p && (lsq_cnt_q == 3'd0) && !m_cur_pend && !csr_chk1_q |->
                                 m_cur == past_mshwm);
// A trapping LS instruction leaves mshwm unchanged; in its shadow
// spec_past_mshwm is its post-state.
Inv_M_CurTKeep:  assert property (e_cur_src |-> lsq_cur_q.mshwm == lsq_cur_q.pre_mshwm);
Inv_M_CurShPast: assert property (shadow_q && e_cur_src |-> lsq_cur_q.mshwm == past_mshwm);
// Whatever the shadow source, once every older step is applied m_cur is the
// trap's pre-state mshwm, which the trap keeps (mshwm analogue of Inv_E_ShKeep).
Inv_M_ShPast:    assert property (past_valid && shadow_q && !e_older_pend |-> m_cur == past_mshwm);

////////////////////// Group G: fetch front end //////////////////////

// Env_NoInstrErr: no fetch error is ever stored in the prefetch buffer, the
// ALT table, or the IR stage FIFOs (all reset to 0).
`define KPF `KDUT.if_stage_i.prefetch_buffer_i
Inv_G_FErrIn:  assert property (!`KPF.instr_err_in);
Inv_G_FErrQ:   assert property (`KPF.fifo_i.err_q == '0);
// fetch_fifo64's precomputed instr1 addresses track instr_addr_q. Out of
// reset all three are zero until the first clear (boot pc_set), and nothing
// has been fetched yet: no fetch data, request or IR entry. The issuer is
// still in RESET (fetch_req = 0) or BOOT_SET (pc_set clears the fifo); it
// never returns to either state.
Inv_G_FAddrP: assert property (
  ((`KPF.fifo_i.instr_addrp2_q == `KPF.fifo_i.instr_addr_q + 31'd1) &&
   (`KPF.fifo_i.instr_addrp4_q == `KPF.fifo_i.instr_addr_q + 31'd2)) ||
  ((`KPF.fifo_i.instr_addr_q == '0) && (`KPF.fifo_i.instr_addrp2_q == '0) &&
   (`KPF.fifo_i.instr_addrp4_q == '0) && (`KPF.fifo_i.valid_q == '0) &&
   (`KISS.ctrl_fsm_cs[super_pkg::CSM_RESET] || `KISS.ctrl_fsm_cs[super_pkg::CSM_BOOT_SET]) &&
   !`KPF.valid_req_q && !`KPF.discard_req_q && (`KPF.branch_discard_q == '0) &&
   (`KPF.rdata_outstanding_q == '0) &&
   (`KIRS.gen_stage0_buffer.s0_fifo.wr_ptr_q == `KIRS.gen_stage0_buffer.s0_fifo.rd_ptr_q) &&
   (`KDUT.ir_valid == '0)));
for (genvar i = 0; i < 2; i++) begin : g_inv_galt
  Inv_G_FErrAlt: assert property (`KPF.fifo_i.gen_alt.alt_table[i].err == '0);
end
// Mirror of branch_predict dec_target (UseBtb = 0 target computation).
function automatic logic [31:0] g_dtgt(super_pkg::ir_reg_t r);
  logic [31:0] i32, ij, ib;
  logic [15:0] h;
  h = r.insn[15:0];
  if (r.is_branch && (r.insn[1:0] == 2'b01) && (r.insn[15:14] == 2'b11))
    i32 = {{4{h[12]}}, h[6:5], h[2], 5'b0, 2'b01, h[9:7], 2'b00, h[13], h[11:10], h[4:3],
           h[12], 7'h63};
  else if (r.is_jal && (r.insn[1:0] == 2'b01) && (r.insn[14:13] == 2'b01))
    i32 = {h[12], h[8], h[10:9], h[6], h[7], h[2], h[11], h[5:3], {9{h[12]}}, 4'b0, ~h[15], 7'h6f};
  else
    i32 = r.insn;
  ij = {{12{i32[31]}}, i32[19:12], i32[20], i32[30:21], 1'b0};
  ib = {{19{i32[31]}}, i32[31], i32[7], i32[30:25], i32[11:8], 1'b0};
  return r.pc + (r.is_branch ? ib : ij);
endfunction
for (genvar i = 0; i < int'(KuduE2eCfg.IrS0Depth); i++) begin : g_inv_gs0
  super_pkg::ir_reg_t r;
  assign r = super_pkg::ir_reg_t'(`KIRS.gen_stage0_buffer.s0_fifo.fifo_mem[i]);
  Inv_G_FErrS0: assert property (!r.errs.fetch_err);
  Inv_G_AltIdS0: assert property (!r.alt_id[1]);
  // Predicted branch/JAL targets are branch_predict's dec_target (pc + imm,
  // compressed forms decoded from the raw low parcel); PredictUseBtb = 0, so
  // branch_unit does not re-check them.
  Inv_G_PtgtS0: assert property (r.ptaken && (r.is_branch || r.is_jal) |-> r.ptarget == g_dtgt(r));
  // is_branch / is_jal are fetch_fifo64's dec_branch / dec_jal of the low parcel.
  // ptaken only on branch / JAL / branch_predict dec_jalr_ra (ret-style, rs1 = ra, imm 0).
  Inv_G_PtkS0: assert property (r.ptaken |-> r.is_branch || r.is_jal ||
    ((r.insn[6:0] == 7'h2) && (r.insn[15:13] == 3'b100) && (r.insn[11:7] == 5'h1)) ||
    ((r.insn[6:0] == 7'h67) && (r.insn[19:15] == 5'h1) && (r.insn[31:20] == 12'h0) &&
     (r.insn[14:12] == 3'b000)));
  Inv_G_EvenS0: assert property (!r.pc[0] && !(r.ptaken && r.ptarget[0]));
  Inv_G_KindS0: assert property (
    (r.is_branch == (((r.insn[1:0] == 2'b01) && (r.insn[15:14] == 2'b11)) || (r.insn[6:0] == 7'h63))) &&
    (r.is_jal    == (((r.insn[1:0] == 2'b01) && (r.insn[14:13] == 2'b01)) || (r.insn[6:0] == 7'h6f))));
end
for (genvar i = 0; i < 2; i++) begin : g_inv_gs1
  super_pkg::ir_dec_t d;
  assign d = super_pkg::ir_dec_t'(`KIRS.gen_stage1.s1_fifo.fifo_mem[i]);
  Inv_G_FErrS1: assert property (!d.errs.fetch_err);
  Inv_G_AltIdS1: assert property (!d.alt_id[1]);
  Inv_G_PtgtS1: assert property (d.ptaken && (d.is_branch || d.is_jal) |-> d.ptarget[31:0] == d.btarget);
  // A predicted JALR is ret-style, so branch_unit's ptarget == cs1 check is exact.
  // A kept RA prediction has ptarget == cur_ra and cur_ra[31:0] == the even s0 ptarget.
  Inv_G_EvenS1: assert property (!d.pc[0] && !((d.is_branch || d.is_jal) && d.btarget[0]) &&
                                 !(d.is_jalr && d.ptaken && d.ptarget[0]));
  Inv_G_PtkS1: assert property (d.ptaken && d.is_jalr |-> (d.insn[19:15] == 5'h1) && (d.insn[31:20] == 12'h0));
end
// NumAlt = 2: an ALT id >= 2 indexes past alt_table (X read).
Inv_G_AltIdEx: assert property (!`KDUT.if_stage_i.ex_alt_ctrl_i.id0[1] && !`KDUT.if_stage_i.ex_alt_ctrl_i.id1[1]);

// PC chain (top): Kudu's next-IR0 PC tracks the spec PC outside the shadow,
// and the IR entries carry consecutive predicted PCs.
function automatic logic [31:0] g_rnxt(super_pkg::ir_dec_t d);
  return ((d.is_branch | d.is_jal | d.is_jalr) & d.ptaken) ? d.ptarget : d.pc_nxt;
endfunction
Inv_G_NxtPc: assert property (past_valid && !shadow_q |-> `KISS.ir0_nxt_pc_q == past_pc);
Inv_G_Ir0Pc: assert property (`KDUT.ir_valid[0] |-> `KISS.ir0_dec.pc == `KISS.ir0_nxt_pc_q);
Inv_G_Ir1Pc: assert property (`KDUT.ir_valid[0] && `KDUT.ir_valid[1] &&
                              !(`KISS.ir0_dec.is_jalr && !`KISS.ir0_dec.ptaken)
                              |-> `KISS.ir1_dec.pc == g_rnxt(`KISS.ir0_dec));
// Rest of the chain: s1 (ir0/ir1_dec) -> s0 dual_fifo (oldest first) ->
// fetch_fifo64 instr_addr_q (next PC to be fetched out). A successor follows
// the predicted path; an s1 JALR whose RA prediction was dropped
// (update_cjalr_instr clears ptaken) always mispredicts, so it ends the chain.
function automatic logic [31:0] g_rnxt_r(super_pkg::ir_reg_t r);
  return r.ptaken ? r.ptarget : (r.pc + (r.is_comp ? 32'd2 : 32'd4));
endfunction
`define KS0 `KIRS.gen_stage0_buffer.s0_fifo
localparam int GS0D = int'(KuduE2eCfg.IrS0Depth);
localparam int GS0W = $clog2(GS0D) + 1;
logic [GS0W-1:0]    g_s0n;
super_pkg::ir_reg_t g_s0e[GS0D];
super_pkg::ir_reg_t g_s0y;
super_pkg::ir_dec_t g_s1y;
logic               g_s1end;
logic [31:0]        g_fpc;
assign g_s0n = `KS0.wr_ptr_q - `KS0.rd_ptr_q;
for (genvar j = 0; j < GS0D; j++) begin : g_s0ord
  assign g_s0e[j] = super_pkg::ir_reg_t'(`KS0.fifo_mem[(GS0W-1)'(`KS0.rd_ptr_q[GS0W-2:0] + (GS0W-1)'(j))]);
end
assign g_s0y   = super_pkg::ir_reg_t'(`KS0.fifo_mem[(GS0W-1)'(`KS0.wr_ptr_q[GS0W-2:0] - 1'b1)]);
assign g_s1y   = `KDUT.ir_valid[1] ? `KISS.ir1_dec : `KISS.ir0_dec;
assign g_s1end = g_s1y.is_jalr && !g_s1y.ptaken;
assign g_fpc   = {`KPF.fifo_i.instr_addr_q, 1'b0};
// s0 dual_fifo occupancy and status flags (as for sbd_fifo).
Inv_G_S0Depth: assert property (g_s0n <= GS0W'(GS0D));
Inv_G_S0Fill:  assert property (`KS0.fill_status_q == {g_s0n > GS0W'(1), g_s0n > GS0W'(0)});
Inv_G_S0Room:  assert property (`KS0.room_status_q == {g_s0n < GS0W'(GS0D-1), g_s0n < GS0W'(GS0D)});
for (genvar j = 0; j + 1 < GS0D; j++) begin : g_inv_s0ch
  Inv_G_PcS0Ch: assert property (g_s0n > GS0W'(j + 1) |-> g_s0e[j+1].pc == g_rnxt_r(g_s0e[j]));
end
Inv_G_PcS0Ft:   assert property (g_s0n != 0 |-> g_rnxt_r(g_s0y) == g_fpc);
Inv_G_PcS1S0:   assert property (`KDUT.ir_valid[0] && (g_s0n != 0) && !g_s1end |-> g_s0e[0].pc == g_rnxt(g_s1y));
Inv_G_PcS1Ft:   assert property (`KDUT.ir_valid[0] && (g_s0n == 0) && !g_s1end |-> g_rnxt(g_s1y) == g_fpc);
Inv_G_PcNoneS0: assert property (!`KDUT.ir_valid[0] && (g_s0n != 0) |-> g_s0e[0].pc == `KISS.ir0_nxt_pc_q);
Inv_G_PcNoneFt: assert property (!`KDUT.ir_valid[0] && (g_s0n == 0) |-> g_fpc == `KISS.ir0_nxt_pc_q);
Inv_G_S1V:      assert property (`KDUT.ir_valid[1] |-> `KDUT.ir_valid[0]);
// s1 stage_fifo (2 entries, 1-bit pointers): full only with equal pointers.
Inv_G_S1Full:   assert property (`KIRS.gen_stage1.s1_fifo.full_stat_q |-> `KIRS.gen_stage1.s1_fifo.wr_ptr_q == `KIRS.gen_stage1.s1_fifo.rd_ptr_q);
Inv_G_EvenNxt: assert property (!`KISS.ir0_nxt_pc_q[0]);
Inv_G_EvenSpc: assert property (!`KISS.special_pc_q[0]);
// MEPCC's address is even (trap PCs are even; legalize_scr clears bit 0).
Inv_G_EvenMepc: assert property (!`KCSR.mepc_q[0]);
// LS request PCs come from IR0/IR1 (even by Ir0Pc/Ir1Pc/EvenNxt); a trapping
// entry's spec mepc equals this PC (F_LsqCause/F_CurCause), keeping MEPCC even.
for (genvar k = 0; k < LsqDepth; k++) begin : g_inv_evlsq
  Inv_G_EvenLsq: assert property ((3'(k) < lsq_cnt_q) |-> !g_inv_lsqf[k].ent.kreq.pc[0]);
end
Inv_G_EvenCur: assert property (e_cur_live |-> !lsq_cur_q.kreq.pc[0]);

////////////////////// Group H: register correspondence //////////////////////
// Links spec_past_regs to Kudu's register file, pipeline results and RaW
// tracking, so Reg_Cont*/Cmt_Wr hold from a free state.
// A pending writer of x_i is an occupied, non-shadow, non-trapping scoreboard
// entry whose spec step writes x_i (i != 0). Ages count from rd_ptr (0 =
// oldest). Only alu0/alu1 WB and mult WB forward (DCacheEn = 0: no LS
// forwarding).
logic [2:0]          inv_age     [SbdDepth];
logic [SbdDepth-1:0] inv_occ;
logic [SbdDepth-1:0] inv_ok      [SbdDepth];   // non-shadow, non-trapping, occupied
logic [SbdDepth-1:0] inv_younger [SbdDepth];   // occupied entries younger than e
logic [SbdDepth-1:0] inv_older   [SbdDepth];   // occupied entries older than e
logic [SbdDepth-1:0] inv_pw      [32];         // inv_pw[i][e]: e is a pending writer of x_i
logic [SbdDepth-1:0] inv_yw      [32];         // youngest pending writer of x_i
logic [SbdDepth-1:0] inv_wx;                   // entry e writes a GPR (spec, rd != 0)

for (genvar e = 0; e < SbdDepth; e++) begin : g_inv_hage
  assign inv_age[e] = 3'(e - `KSBD.rd_ptr_q[2:0]);
  assign inv_occ[e] = (4'(inv_age[e]) < inv_sbd_depth);
  assign inv_wx[e]  = fol_wx_en[e] && (fol_wx_addr[e] != 5'd0);
  for (genvar f = 0; f < SbdDepth; f++) begin : g_f
    assign inv_younger[e][f] = inv_occ[f] && (inv_age[f] > inv_age[e]);
    assign inv_older[e][f]   = inv_occ[f] && (inv_age[f] < inv_age[e]);
  end
end
logic [SbdDepth-1:0] inv_nsok;
for (genvar e = 0; e < SbdDepth; e++) begin : g_inv_hnsok
  assign inv_nsok[e] = inv_occ[e] && !fol_shadow[e] && !fol_err[e];
end
for (genvar i = 0; i < 32; i++) begin : g_inv_hpw
  for (genvar e = 0; e < SbdDepth; e++) begin : g_e
    assign inv_pw[i][e] = (i != 0) && inv_nsok[e] && inv_wx[e] && (fol_wx_addr[e] == 5'(i));
    assign inv_yw[i][e] = inv_pw[i][e] && !(|(inv_pw[i] & inv_younger[e]));
  end
end

// H1: the spec value of a register with pending writers is the youngest
// writer's result. H2: with none, it is the register file value.
logic [31:1] inv_h1_ok, inv_h2_ok;
for (genvar i = 1; i < 32; i++) begin : g_inv_hreg
  logic [SbdDepth-1:0] ok;
  for (genvar e = 0; e < SbdDepth; e++) begin : g_e
    assign ok[e] = !inv_yw[i][e] || (past_has_reg[i] && (past_regs[i] == fol_wx[e]));
  end
  assign inv_h1_ok[i] = &ok;
  assign inv_h2_ok[i] = !past_has_reg[i] || (|inv_pw[i]) ||
                        alas(past_regs[i], rfw2sail(`KRF.rf_reg[i]));
end
Inv_H_RegPend: assert property (&inv_h1_ok);
Inv_H_RegRf:   assert property (&inv_h2_ok);

// Normally issued writers set reg_wrsv (cleared only by the youngest
// writer's commit, see the *Young invariants). Special-issued instructions
// do not, but the FSM drains the scoreboard (WAIT_FINAL) before DECODE.
logic inv_spst;
assign inv_spst = `KISS.ctrl_fsm_cs[super_pkg::CSM_WAIT_FINAL] | `KISS.ctrl_fsm_cs[super_pkg::CSM_WAIT_CMPLX];
// ISSUE_SPECIAL is entered from WAIT_CMT0 with an empty scoreboard, and SLEEP
// holds only the WFI (no GPR write); SLEEP exits to DECODE without draining.
Inv_H_SpNoPw: assert property (`KISS.ctrl_fsm_cs[super_pkg::CSM_ISSUE_SPECIAL] |
                               `KISS.ctrl_fsm_cs[super_pkg::CSM_SLEEP] |-> !(|(inv_nsok & inv_wx)));
logic [31:1] inv_wrsv_ok;
for (genvar i = 1; i < 32; i++) begin : g_inv_hwrsv
  assign inv_wrsv_ok[i] = inv_spst || !(|inv_pw[i]) || `KISS.reg_wrsv_q[i];
end
Inv_H_Wrsv: assert property (&inv_wrsv_ok);

// Kudu's destination register at a normal issue matches the spec's write.
Inv_H_IssueRd0: assert property (s0_normal && s0_upd && !s0_trap |->
  ((s0_dec.rf_we && (s0_dec.rd != 5'd0)) == (s0_wx_en && (s0_wx_addr != 5'd0))) &&
  (!(s0_wx_en && (s0_wx_addr != 5'd0)) || (s0_dec.rd == s0_wx_addr)));
Inv_H_IssueRd1: assert property (s1_upd && !s1_trap |->
  ((s1_dec.rf_we && (s1_dec.rd != 5'd0)) == (s1_wx_en && (s1_wx_addr != 5'd0))) &&
  (!(s1_wx_en && (s1_wx_addr != 5'd0)) || (s1_dec.rd == s1_wx_addr)));

// Single-stage ALU pipelines: the WB stage holds the only scoreboard entry of
// the pipeline. Its forwarding slot is valid only while no younger pending
// writer of the same register exists (WAW clears it).
`define KH_ALU(P) \
  logic [SbdDepth-1:0] inv_alu``P``_ent, inv_alu``P``_ok, inv_alu``P``_dok; \
  logic                inv_alu``P``_wv, inv_alu``P``_fv; \
  logic [4:0]          inv_alu``P``_rd; \
  assign inv_alu``P``_wv = `KDUT.alu_pipeline``P``_i.wb_valid; \
  assign inv_alu``P``_fv = `KDUT.alu_pipeline``P``_i.wb_fwd_valid_q; \
  assign inv_alu``P``_rd = `KDUT.alu_pipeline``P``_i.wb_reg.rd; \
  for (genvar e = 0; e < SbdDepth; e++) begin : g_inv_halu``P \
    assign inv_alu``P``_ent[e] = inv_occ[e] && fol_pl[e][1+P]; \
    assign inv_alu``P``_ok[e]  = !inv_alu``P``_ent[e] || fol_shadow[e] || fol_err[e] || \
      (((`KDUT.alu_pipeline``P``_i.wb_reg.rf_we && (inv_alu``P``_rd != 5'd0)) == inv_wx[e]) && \
       (!inv_wx[e] || (inv_alu``P``_rd == fol_wx_addr[e])) && \
       (!inv_alu``P``_fv || !(|(inv_pw[inv_alu``P``_rd] & inv_younger[e])))); \
    assign inv_alu``P``_dok[e] = !(inv_alu``P``_ent[e] && inv_nsok[e] && inv_wx[e]) || \
      alas(fol_wx[e], rfw2sail(`KDUT.alupl``P``_output.wdata)); \
  end \
  Inv_H_AluData``P: assert property (&inv_alu``P``_dok); \
  Inv_H_AluCnt``P: assert property ($countones(inv_alu``P``_ent) == int'(inv_alu``P``_wv)); \
  Inv_H_AluEnt``P: assert property (&inv_alu``P``_ok); \
  Inv_H_AluFwd``P: assert property ((!inv_alu``P``_fv || (inv_alu``P``_wv && \
      `KDUT.alu_pipeline``P``_i.wb_reg.rf_we && (inv_alu``P``_rd != 5'd0))) && \
      (`KDUT.alupl``P``_fwd_act == (inv_alu``P``_fv ? (32'h1 << inv_alu``P``_rd) : 32'h0)));

`KH_ALU(0)
`KH_ALU(1)
`undef KH_ALU

// Issue-time ALU check, case-split by opcode class for the solver. ALU
// pipeline P's EX1 reads ira (P=0) / irb (P=1), the same operand bus as the
// spec step, and the result reaches WB (alupl output) the next cycle. With
// these assumed, Inv_H_AluData needs only the WB hold case.
function automatic logic [4:0] f_alu_cls(logic [31:0] insn);
  case (insn[6:0])
    7'h13:   return {2'b00, insn[14:12]};
    7'h33:   return {2'b01, insn[14:12]};
    7'h5b:   return {2'b10, insn[14:12]};
    7'h37:   return 5'd24;
    7'h17:   return 5'd25;
    7'h6f:   return 5'd26;
    default: return 5'd27;
  endcase
endfunction

// Class 16 (CHERI opcode, funct3 0) is split further by funct7, and by
// rs2 for funct7 0x7f: the 25 decoded operations plus everything else.
localparam int NCxK = 25;
localparam logic [6:0] CxK [NCxK] = '{7'h01, 7'h08, 7'h09, 7'h0a, 7'h0b, 7'h0c, 7'h0d, 7'h10, 7'h11,
  7'h14, 7'h16, 7'h20, 7'h21, 7'h40, 7'h41, 7'h42, 7'h43, 7'h44, 7'h48, 7'h49, 7'h4a, 7'h4b,
  7'h4f, 7'h57, 7'h58};
function automatic logic [6:0] f_cx_key(logic [31:0] insn);
  return (insn[31:25] == 7'h7f) ? {2'b10, insn[24:20]} : (insn[31] ? 7'h7e : insn[31:25]);
endfunction
function automatic logic f_cx_known(logic [31:0] insn);
  logic k;
  k = 1'b0;
  for (int i = 0; i < NCxK; i++) if (f_cx_key(insn) == CxK[i]) k = 1'b1;
  return k;
endfunction

`define KH_ALUISS(P, SEL0) \
  logic        inv_aiss``P``_v; \
  t_Capability inv_aiss``P``_wx; \
  logic [4:0]  inv_aiss``P``_cls; \
  assign inv_aiss``P``_v = `KDUT.ex_valid[1+P] && `KDUT.alu_pipeline``P``_i.wb_rdy && \
    ((SEL0) ? (s0_upd && !s0_trap && s0_wx_en && (s0_wx_addr != 5'd0)) \
            : (s1_upd && !s1_trap && s1_wx_en && (s1_wx_addr != 5'd0))); \
  assign inv_aiss``P``_wx  = (SEL0) ? s0_wx : s1_wx; \
  assign inv_aiss``P``_cls = f_alu_cls(`KDUT.alu_pipeline``P``_i.instr_i.insn); \
  for (genvar c = 0; c < 28; c++) begin : g_inv_aiss``P \
    if (c != 16) begin : g_c \
    Inv_H_AluIss_C: assert property (inv_aiss``P``_v && (inv_aiss``P``_cls == 5'(c)) |=> \
      !`KDUT.alu_pipeline``P``_i.wb_valid || \
      alas($past(inv_aiss``P``_wx), rfw2sail(`KDUT.alupl``P``_output.wdata))); \
    end \
  end \
  for (genvar s = 0; s <= NCxK; s++) begin : g_inv_aisx``P \
    logic m; \
    if (s < NCxK) begin : g_k \
      assign m = (f_cx_key(`KDUT.alu_pipeline``P``_i.instr_i.insn) == CxK[s]); \
    end else begin : g_o \
      assign m = !f_cx_known(`KDUT.alu_pipeline``P``_i.instr_i.insn); \
    end \
    Inv_H_AluIss_X: assert property (inv_aiss``P``_v && (inv_aiss``P``_cls == 5'd16) && m |=> \
      !`KDUT.alu_pipeline``P``_i.wb_valid || \
      alas($past(inv_aiss``P``_wx), rfw2sail(`KDUT.alupl``P``_output.wdata))); \
  end

`KH_ALUISS(0, `KDUT.ira_is0)
`KH_ALUISS(1, !`KDUT.ira_is0)
`undef KH_ALUISS

// CTestSubset lemmas (issue cycle, operands as the ALU sees them): the spec
// decodes bounds/perms of op2sail(operand); Kudu uses the precomputed
// full_cap_t fields. Proven at a lower level, they let Inv_H_AluIss_X[11]
// avoid re-deriving both bounds decodes in one SAT problem.
function automatic logic f_fcap_bnd_eq(logic [super_pkg::FullW-1:0] x);
  cheri_pkg::full_cap_t c;
  t_ztuplez3z5i64_z5i64 b;
  c = cheri_pkg::full_cap_t'(x);
  b = getCapBounds(op2sail(c));
  return (b.ztuplez3z5i64_z5i640 == {32'h0, c.base32}) &&
         (b.ztuplez3z5i64_z5i641 == {31'h0, c.top33});
endfunction
function automatic logic f_fcap_perm_eq(logic [super_pkg::FullW-1:0] x);
  cheri_pkg::full_cap_t c;
  c = cheri_pkg::full_cap_t'(x);
  return getCapPerms(op2sail(c)) == c.perms;
endfunction
`define KH_CTSTL(P) \
  logic inv_ctst``P``_v; \
  assign inv_ctst``P``_v = inv_aiss``P``_v && (inv_aiss``P``_cls == 5'd16) && \
    (f_cx_key(`KDUT.alu_pipeline``P``_i.instr_i.insn) == 7'h20); \
  Inv_H_CtstB1_``P: assert property (inv_ctst``P``_v |-> \
    f_fcap_bnd_eq(`KDUT.alu_pipeline``P``_i.full_data2_i.d0)); \
  Inv_H_CtstB2_``P: assert property (inv_ctst``P``_v |-> \
    f_fcap_bnd_eq(`KDUT.alu_pipeline``P``_i.full_data2_i.d1)); \
  Inv_H_CtstP1_``P: assert property (inv_ctst``P``_v |-> \
    f_fcap_perm_eq(`KDUT.alu_pipeline``P``_i.full_data2_i.d0)); \
  Inv_H_CtstP2_``P: assert property (inv_ctst``P``_v |-> \
    f_fcap_perm_eq(`KDUT.alu_pipeline``P``_i.full_data2_i.d1));
`KH_CTSTL(0)
`KH_CTSTL(1)
`undef KH_CTSTL

// Mult pipeline: EX2 and WB, in order. WB holds the oldest mult entry, EX2
// the youngest. Only WB forwards; EX2's ex2_fwd_ok tracks WAW cancellation.
`define KMP `KDUT.mult_pipeline_i
logic [SbdDepth-1:0] inv_mul_ent, inv_mul_old, inv_mul_yng, inv_mul_ok, inv_mul_dok, inv_mul_x2ok, inv_div_fol;
for (genvar e = 0; e < SbdDepth; e++) begin : g_inv_hmul
  assign inv_mul_ent[e] = inv_occ[e] && fol_pl[e][4];
  assign inv_mul_old[e] = inv_mul_ent[e] && !(|(inv_mul_ent & inv_older[e]));
  assign inv_mul_yng[e] = inv_mul_ent[e] && !(|(inv_mul_ent & inv_younger[e]));
  assign inv_mul_ok[e]  = !inv_mul_ent[e] || fol_shadow[e] || fol_err[e] ||
    ((!(inv_mul_old[e] && `KMP.wb_valid) ||
      (((`KMP.wb_reg.rf_we && (`KMP.wb_reg.rd != 5'd0)) == inv_wx[e]) &&
       (!inv_wx[e] || (`KMP.wb_reg.rd == fol_wx_addr[e])) &&
       (!`KMP.wb_fwd_valid_q || !(|(inv_pw[`KMP.wb_reg.rd] & inv_younger[e]))))) &&
     (!(inv_mul_yng[e] && `KMP.ex2_valid) ||
      (((`KMP.ex2_reg.rf_we && (`KMP.ex2_reg.rd != 5'd0)) == inv_wx[e]) &&
       (!inv_wx[e] || (`KMP.ex2_reg.rd == fol_wx_addr[e])) &&
       (!(`KMP.ex2_fwd_ok && `KMP.ex2_reg.rf_we && (`KMP.ex2_reg.rd != 5'd0)) ||
        !(|(inv_pw[`KMP.ex2_reg.rd] & inv_younger[e]))))));
  // Div data comes from multdiv32 under Env_DivLemma (Inv_H_Div*).
  assign inv_mul_dok[e] = !(inv_mul_old[e] && `KMP.wb_valid &&
                            inv_nsok[e] && inv_wx[e]) ||
    alas(fol_wx[e], rfw2sail(`KDUT.multpl_output.wdata));
  // EX2's finished result (CJALR link, CSetBounds*/CRRL/CRAM from the
  // registered EX1 state, mult from the multiplier's stage registers) is
  // the youngest mult entry's; a divide's is multdiv32's (Inv_H_DivFol/Done).
  assign inv_mul_x2ok[e] = !(inv_mul_yng[e] && `KMP.ex2wb_valid &&
                             inv_nsok[e] && inv_wx[e]) ||
    alas(fol_wx[e], rfw2sail(`KMP.ex2wb_reg.wdata));
  // A divide in EX2 (the youngest mult entry) was recorded at its start
  // (spec_instance.sv, Env_DivLemma) with this entry's Sail result.
  assign inv_div_fol[e] = !(inv_mul_yng[e] && `KMP.ex2_valid && `KMP.ex2_reg.flags.is_div &&
                            inv_nsok[e] && inv_wx[e]) ||
    (div_rec_ok && alas(fol_wx[e], rfw2sail(super_pkg::RegW'(div_rec_res))));
end
// multdiv32 is busy only for the divide in EX2, whose latched inputs are the
// recorded Sail operands, operator and signed mode; after MD_FINISH it is
// idle with div_done_q set and holds the result in imd_val_q[0] (Env_DivLemma
// gives it at MD_FINISH) until EX2 hands the divide to WB.
Inv_H_DivFol:  assert property (&inv_div_fol);
Inv_H_DivBusy: assert property ((`KMD.md_state_q != 3'd0) |->
                                `KMP.ex2_valid && `KMP.ex2_reg.flags.is_div && !`KMP.div_done_q &&
                                (`KMD.md_state_q <= 3'd6) && div_rec_v &&
                                (`KMP.ex2_reg.insn == div_rec_insn) && f_is_divrem(div_rec_insn) &&
                                (`KMD.op_a_q == div_rec_a) && (`KMD.op_b_q == div_rec_b) &&
                                (`KMD.operator_q == f_div_op(div_rec_insn)) &&
                                (kdiv_sm_q == f_div_sm(div_rec_insn)));
Inv_H_DivWait: assert property (`KMP.ex2_valid && `KMP.ex2_reg.flags.is_div |->
                                (`KMD.md_state_q != 3'd0) || `KMP.div_done_q);
// A divide in EX2 is only a divide: its kind flags and cheri_op come from
// decoding its own insn (mult_pipeline ex1to2_reg), so op_done and
// ex2wb_valid wait for div_done_q (s2ind74r MulEx2Data cex: is_div with
// cheri_op.cscrrw).
Inv_H_DivKind: assert property (`KMP.ex2_valid && `KMP.ex2_reg.flags.is_div |->
                                f_is_divrem(`KMP.ex2_reg.insn) && !`KMP.ex2_reg.flags.is_mult &&
                                !`KMP.ex2_reg.flags.is_cjalr && (`KMP.ex2_reg.cheri_op == '0));
Inv_H_DivDone: assert property (`KMP.div_done_q |->
                                `KMP.ex2_valid && `KMP.ex2_reg.flags.is_div && (`KMD.md_state_q == 3'd0) &&
                                div_rec_v && (`KMP.ex2_reg.insn == div_rec_insn) &&
                                (!div_rec_ok || (`KMD.imd_val_q[0][31:0] == div_rec_res)));
// Issue-time mult-pipeline check (non-divide), case-split by operation for
// the solver: an instruction entering EX2 has the spec's write value as its
// EX2 result while it is there (CJALR link, mul*, CSetBounds*/CRRL/CRAM).
logic        inv_miss_v, inv_miss_s0;
t_Capability inv_miss_wx;
logic [3:0]  inv_miss_cls;
assign inv_miss_s0 = (`KMP.sel_ira_i == `KDUT.ira_is0);
assign inv_miss_v  = `KDUT.ex_valid[4] && `KMP.ex2_rdy && !`KMP.div_sel &&
  (inv_miss_s0 ? (s0_upd && !s0_trap && s0_wx_en && (s0_wx_addr != 5'd0))
               : (s1_upd && !s1_trap && s1_wx_en && (s1_wx_addr != 5'd0)));
assign inv_miss_wx = inv_miss_s0 ? s0_wx : s1_wx;
always_comb begin
  if (`KMP.ex1_is_cjalr)                              inv_miss_cls = 4'd0;
  else if (`KMP.mult_sel)                             inv_miss_cls = 4'd1 + 4'(`KMP.instr_dec.insn[13:12]);
  else if (`KMP.instr_dec.cheri_op.csetbounds)        inv_miss_cls = 4'd5;
  else if (`KMP.instr_dec.cheri_op.csetboundsex)      inv_miss_cls = 4'd6;
  else if (`KMP.instr_dec.cheri_op.csetboundsimm)     inv_miss_cls = 4'd7;
  else if (`KMP.instr_dec.cheri_op.csetboundsrndn)    inv_miss_cls = 4'd8;
  else if (`KMP.instr_dec.cheri_op.crrl)              inv_miss_cls = 4'd9;
  else if (`KMP.instr_dec.cheri_op.cram)              inv_miss_cls = 4'd10;
  else                                                inv_miss_cls = 4'd11;
end
for (genvar c = 0; c < 12; c++) begin : g_inv_miss
  Inv_H_MulIss_C: assert property (inv_miss_v && (inv_miss_cls == 4'(c)) |=>
    !`KMP.ex2_valid || alas($past(inv_miss_wx), rfw2sail(`KMP.ex2wb_reg.wdata)));
end
// Multiplier product lemma, proven at block level outside this harness:
// Conformal LEC proves the combinational signed_mult_33x33_wallace equal to
// a*b for all inputs (kudu_e2e/mullec2_*, V2/V3 split on b[32]; a mutated
// compressor gives 64/66 non-equivalent), and Jasper (kudu_e2e/mulpipe_*)
// proves the plStageNum=5 instance's product == $past(combinational product).
// Assumed so the solver need not re-derive the Wallace tree.
// Subsumed by Env_MulLemma (spec_instance.sv); kept as an opt-in.
`ifdef E2E_MULPROD
`define KMUL `KMD.gen_no_dw_mult.mult33_i
Ext_K_MulProd: assume property ($past(rst_ni) && $past(`KMUL.en_i) |->
  `KMUL.product == $past(66'(`KMUL.a) * 66'(`KMUL.b)));
// Also proven by mulpipe (P_Hold); needed when the product net is cut (stopat).
Ext_K_MulHold: assume property ($past(rst_ni) && !$past(`KMUL.en_i) |-> $stable(`KMUL.product));
`endif
Inv_H_MulData:    assert property (&inv_mul_dok);
Inv_H_MulEx2Data: assert property (&inv_mul_x2ok);
Inv_H_MulCnt: assert property ($countones(inv_mul_ent) == int'(`KMP.ex2_valid) + int'(`KMP.wb_valid));
Inv_H_MulEnt: assert property (&inv_mul_ok);
Inv_H_MulFwd: assert property ((!`KMP.wb_fwd_valid_q || (`KMP.wb_valid && `KMP.wb_reg.rf_we &&
                                                        (`KMP.wb_reg.rd != 5'd0))) &&
  (`KDUT.multpl_fwd_act == (`KMP.wb_fwd_valid_q ? (32'h1 << `KMP.wb_reg.rd) : 32'h0)));
`undef KMP

// LS pipeline: the k-th waw_fifo / wb_fifo entry (from its read pointer)
// belongs to the k-th oldest LS scoreboard entry. waw_fifo bit 5 is the
// write reservation (lspl wrsv); WAW from a younger writer clears it.
logic [2:0] inv_ls_rank [SbdDepth];
for (genvar e = 0; e < SbdDepth; e++) begin : g_inv_hlsr
  assign inv_ls_rank[e] = 3'($countones(inv_sbd_ls & inv_older[e]));
end
logic [7:0] inv_waw_ok;
for (genvar j = 0; j < 8; j++) begin : g_inv_hwaw
  logic [2:0]          off;
  logic [5:0]          w;
  logic [SbdDepth-1:0] ok;
  assign off = 3'(j - `KLSP.waw_fifo_i.rd_ptr_q[2:0]);
  assign w   = `KLSP.waw_fifo_i.fifo_mem[j];
  for (genvar e = 0; e < SbdDepth; e++) begin : g_e
    assign ok[e] = !((4'(off) < inv_waw_cnt) && inv_sbd_ls[e] && (inv_ls_rank[e] == off) &&
                     inv_nsok[e] && inv_wx[e]) ||
                   ((w[4:0] == fol_wx_addr[e]) && (!w[5] || !(|(inv_pw[w[4:0]] & inv_younger[e]))));
  end
  assign inv_waw_ok[j] = &ok;
end
Inv_H_LsWaw: assert property (&inv_waw_ok);
logic [3:0] inv_lswb_ok;
for (genvar j = 0; j < 4; j++) begin : g_inv_hwb
  logic [2:0]          off;
  super_pkg::pl_out_t  ent;
  logic [SbdDepth-1:0] ok;
  assign off = 3'(2'(2'(j) - `KLSP.wb_fifo_i.rd_ptr_q[1:0]));
  assign ent = super_pkg::pl_out_t'(`KLSP.wb_fifo_i.fifo_mem[j]);
  for (genvar e = 0; e < SbdDepth; e++) begin : g_e
    assign ok[e] = !((off < inv_wb_cnt) && inv_sbd_ls[e] && (inv_ls_rank[e] == off) &&
                     inv_nsok[e] && !ent.err) ||
                   (((ent.we && (ent.waddr != 5'd0)) == inv_wx[e]) &&
                    (!inv_wx[e] || ((ent.waddr == fol_wx_addr[e]) && alas(fol_wx[e], rfw2sail(ent.wdata)))));
  end
  assign inv_lswb_ok[j] = &ok;
end
Inv_H_LsWbData: assert property (&inv_lswb_ok);
// A non-shadow LS response's error flag is the spec trap of its entry.
logic [3:0][SbdDepth-1:0] inv_lswe_ok;
for (genvar j = 0; j < 4; j++) begin : g_inv_hwe
  logic [2:0]         off;
  super_pkg::pl_out_t ent;
  assign off = 3'(2'(2'(j) - `KLSP.wb_fifo_i.rd_ptr_q[1:0]));
  assign ent = super_pkg::pl_out_t'(`KLSP.wb_fifo_i.fifo_mem[j]);
  for (genvar e = 0; e < SbdDepth; e++) begin : g_e
    assign inv_lswe_ok[j][e] = !((off < inv_wb_cnt) && inv_sbd_ls[e] && (inv_ls_rank[e] == off) &&
                                 !fol_shadow[e]) || (ent.err == fol_err[e]);
  end
end
Inv_H_LsWbErr: assert property (&inv_lswe_ok);
// The request in the LSU (outstanding_resp_q) is the LS entry of rank
// wb_cnt and the i-th LSQ entry that of rank wb_cnt + outstanding + i
// (Inv_D_LsInFlight order). Its PC is the entry's, and Kudu's rd / rf_we
// (written into wb_fifo by the LSU) are the spec's for non-trapping entries.
// The spec steps a load at issue on free read data (rd_*_data), later tied
// to the bus response (Mem_Rdata*): its integer result is that data formatted
// with Kudu's request (offset kreq.addr[1:0], data_type, sign_ext), as the
// LSU does (rdata_w/h/b_ext; a split access combines rdata_q with the second
// word).
function automatic logic [31:0] inv_lfmt(lsq_ent_t l);
  logic [63:0] w;
  w = {l.rd_snd_data, l.rd_fst_data} >> {l.kreq.addr[1:0], 3'b000};
  case (l.kreq.data_type)
    2'b00:   return w[31:0];
    2'b01:   return l.kreq.sign_ext ? {{16{w[15]}}, w[15:0]} : {16'h0, w[15:0]};
    default: return l.kreq.sign_ext ? {{24{w[7]}}, w[7:0]} : {24'h0, w[7:0]};
  endcase
endfunction
// A capability load: the 65-bit read (tag, high, low word) through Kudu's
// mem2regcap with the request's clrperm (load-global / load-mutable masking).
function automatic cheri_pkg::reg_cap_t inv_lcap(lsq_ent_t l);
  return cheri_pkg::mem2regcap(cheri_pkg::mem_cap_t'({l.rd_tag, l.rd_snd_data, l.rd_fst_data}),
                               l.kreq.clrperm);
endfunction
// A CSR instruction's result is the old value of its CSR in the entry's
// pre-state (Sail CSpecialRW / Zicsr read before write); an SCR goes through
// wC's encodeDecodePermsOf (spec_api wx_o). mstatus.MIE comes
// from Kudu's request (the LSU overrides cs_registers' bit with kreq.mie).
function automatic logic f_csr_rd_ok(lsq_ent_t x, t_Capability v);
  logic [31:0] r;
  if (f_csr_cap(x.insn))
    case (x.insn[24:20])
      cheri_pkg::CHERI_SCR_MTCC:  return cap_eq(v, encodeDecodePermsOf(x.pre.mtvec));
      cheri_pkg::CHERI_SCR_MEPCC: return !f_mepc_lossy(x.pre.mepc) && // Env_NoDivGRd*
                                         cap_eq(v, encodeDecodePermsOf(x.pre.mepc));
      cheri_pkg::CHERI_SCR_MTDC:  return cap_eq(v, encodeDecodePermsOf(x.pre.mtdc));
      default:                    return cap_eq(v, encodeDecodePermsOf(x.pre.mscratchc));
    endcase
  r = '0;
  case (x.insn[31:20])
    12'h300: begin
      r[3] = x.kreq.mie;  r[7] = x.pre.mstatus.mpie;
      r[12:11] = x.pre.mstatus.mpp; r[17] = x.pre.mstatus.mprv;
      r[21] = x.pre.mstatus.tw;
    end
    12'h301: r = dut_misa;
    12'h304: r = x.pre.mie;
    12'h340: r = x.pre.mscratch;
    12'h342: r = x.pre.mcause;
    12'h343: r = x.pre.mtval;
    12'hf11: r = csr_pkg::CSR_MVENDORID_CHERI_VALUE;
    12'hf12: r = csr_pkg::CSR_MARCHID_CHERI_VALUE;
    12'hf13: r = csr_pkg::CSR_MIMPID_VALUE;
    12'hf14: r = hart_id_i;
    12'hbc1: r = x.pre_mshwm;
    12'hbc2: r = x.pre.mshwmb;
    default: ;
  endcase
  return alas(v, rfw2sail(super_pkg::RegW'(r)));
endfunction
function automatic logic inv_lsk_ok(lsq_ent_t l, logic [31:0] pc, logic sh, logic er, logic nsok,
                                    logic wx, logic [4:0] wa, t_Capability v);
  return (l.pc == pc) && (l.shadow == sh) && (sh || (l.trap == er)) &&
         (!nsok || (((l.kreq.rf_we && (l.kreq.rd != 5'd0)) == wx) && (!wx || (l.kreq.rd == wa)))) &&
         (!nsok || !wx || l.csr || !l.kreq.is_load ||
          alas(v, rfw2sail(l.kreq.is_cap ? inv_lcap(l) : super_pkg::RegW'(inv_lfmt(l))))) &&
         (!nsok || !wx || !l.csr || f_csr_rd_ok(l, v));
endfunction
logic [SbdDepth-1:0] inv_lscur_ok;
logic [3:0][SbdDepth-1:0] inv_lsq_ok;
for (genvar e = 0; e < SbdDepth; e++) begin : g_inv_hlsk
  assign inv_lscur_ok[e] = !(`KLSU.outstanding_resp_q && inv_sbd_ls[e] &&
                             (inv_ls_rank[e] == inv_wb_cnt)) ||
                           inv_lsk_ok(lsq_cur_q, fol_pc[e], fol_shadow[e], fol_err[e], inv_nsok[e],
                                      inv_wx[e], fol_wx_addr[e], fol_wx[e]);
  for (genvar i = 0; i < 4; i++) begin : g_i
    assign inv_lsq_ok[i][e] = !((3'(i) < lsq_cnt_q) && inv_sbd_ls[e] &&
                                (4'(inv_ls_rank[e]) == 4'(inv_wb_cnt) + 4'(`KLSU.outstanding_resp_q) + 4'(i))) ||
                              inv_lsk_ok(lsq_mem[2'(lsq_rp_q + 2'(i))], fol_pc[e], fol_shadow[e], fol_err[e], inv_nsok[e],
                                         inv_wx[e], fol_wx_addr[e], fol_wx[e]);
  end
end
Inv_H_LsCurEnt: assert property (&inv_lscur_ok);
Inv_H_LsqEnt:   assert property (&inv_lsq_ok);
// LSU load-data state of the outstanding request: the byte offset (ctrl_update
// at issue; a split's WAIT_GNT reloads it from the same held request) and, in
// the second part of a split load, the first word's upper bytes (rdata_update).
// A request faulting lsu_if/LSU checks (lschk_err) goes without ctrl_update;
// its error response carries no data. A first access still waiting for its
// grant (WAIT_GNT_MIS, or WAIT_GNT of a non-split) loads it on the grant.
Inv_H_LsuOff: assert property (`KLSU.outstanding_resp_q && !`KLSU.lsu_req_info_q.is_csr &&
                               !`KLSU.lsu_req_info_q.lschk_err.any_fault &&
                               !(`KLSU.ls_fsm_cs == 3'd1) &&
                               !((`KLSU.ls_fsm_cs == 3'd3) && !`KLSU.handle_misaligned_q) |->
                               `KLSU.rdata_offset_q == (`KLSU.lsu_req_info_q.is_cap ? 2'b00
                                                                                    : `KLSU.lsu_req_info_q.addr[1:0]));
logic inv_lsu_split;
assign inv_lsu_split = !`KLSU.lsu_req_info_q.is_cap &&
                       (((`KLSU.lsu_req_info_q.data_type == 2'b00) && (`KLSU.lsu_req_info_q.addr[1:0] != 2'b00)) ||
                        ((`KLSU.lsu_req_info_q.data_type == 2'b01) && (`KLSU.lsu_req_info_q.addr[1:0] == 2'b11)));
// LSU FSM phase vs the held request: a split is in WAIT_GNT_MIS (first part
// not granted), WAIT_RVALID_MIS (handle_misaligned_q) or WAIT_GNT with
// handle_misaligned_q (second part); a non-split waits in WAIT_GNT with it
// clear. Faulting and CSR requests never leave IDLE.
Inv_H_LsuMis: assert property (
  ((`KLSU.ls_fsm_cs == 3'd0) |-> !`KLSU.handle_misaligned_q) and
  ((`KLSU.ls_fsm_cs != 3'd0) |-> `KLSU.outstanding_resp_q && !`KLSU.lsu_req_info_q.is_csr &&
                                 !`KLSU.lsu_req_info_q.lschk_err.any_fault) and
  ((`KLSU.ls_fsm_cs == 3'd1) |-> !`KLSU.handle_misaligned_q && inv_lsu_split) and
  ((`KLSU.ls_fsm_cs == 3'd2) |-> `KLSU.handle_misaligned_q && inv_lsu_split) and
  ((`KLSU.ls_fsm_cs == 3'd3) |-> (`KLSU.handle_misaligned_q == inv_lsu_split)));
Inv_H_LsuRdq: assert property (`KLSU.outstanding_resp_q && `KLSU.lsu_req_info_q.is_load &&
                               !`KLSU.lsu_req_info_q.is_csr && inv_lsu_split &&
                               (`KLSU.ls_fsm_cs inside {3'd0, 3'd3}) &&
                               !lsq_cur_q.shadow && !lsq_cur_q.trap && lsq_cur_q.rd |->
                               `KLSU.rdata_q == lsq_cur_q.rd_fst_data[31:8]);

`undef KS0
`undef KPF

`undef KLSIF
`undef KLSP
`undef KCPX
