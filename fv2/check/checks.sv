// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Stage-1 checks (README section 4.3), plain SVA. Included last inside
// kudu_e2e_top. Assertion names follow <Class>_<What>[<slot>].
//
// Classes:
//   Spec_*    the spec accepted the step (no internal error, mode matched)
//   PC_*      next PC continuity
//   Reg_*     GPR operand continuity (forwarding/RF vs spec_past_regs)
//   Special_* serialised steps (CSM_ISSUE_SPECIAL) and trap entry
//   Exc_*     trap handler/target PC
//   Local_*   instructions with no scoreboard entry
//   Fol_*/Cmt_* committer: trap and GPR write per scoreboard entry
//   Mem_*     LSU bus requests vs spec read_ram/write_ram
//   CSR_*     CSR instruction effect
//   Harness_* harness-internal consistency
//   Cov_*     each class can retire

localparam logic [31:0] BootPc = {BootAddr[31:8], 8'h80};

////////////////////// Harness scope //////////////////////

// Excluded by the environment: breakpoints/debug.
Harness_NoDebugCase: assert property (!(`KISS.special_case_q inside {super_pkg::DEBUG, super_pkg::STEP}));

// Each scoreboard write comes from a spec step; cmplx_unit writes the AMO
// read entry in its step cycle and the write entry after a non-trapping step.
Harness_SbdWrStep0: assert property (`KSBD.wr_data_en[0] && !`KDUT.cmplx_sbd_wr
                                     |-> (sbd_wr_src1[0] ? s1_step : s0_step));
Harness_SbdWrStep1: assert property (`KSBD.wr_data_en[1] |-> s0_step && s1_step && !`KDUT.cmplx_sbd_wr);
Harness_CmplxWr:    assert property (`KDUT.cmplx_sbd_wr |-> (amo_sbd_rd ? s0_cmplx : amo_rec_v_q) &&
                                                         !(|`KISS.ir_fifo_wr));

// LS follower: every LSU go has a follower entry; the follower does not
// overflow.
Harness_LsqGo:     assert property (lsq_go |-> lsq_head.valid);
Harness_LsqNoOvf:  assert property (lsq_push |-> (lsq_cnt_q < 3'(LsqDepth)) || lsq_go);
Harness_LsqOnePush:assert property ($onehot0({lsq_push0, lsq_push1, lsq_pusha}) &&
                                   !(s0_cmplx && amo_wr_pend_q));

////////////////////// Spec acceptance //////////////////////

Spec_NoIntErr0: assert property (s0_upd |-> !s0_int_err);
Spec_NoIntErr1: assert property (s1_upd |-> !s1_int_err);

////////////////////// PC continuity //////////////////////

PC_Boot:  assert property (s0_upd && !past_valid |-> s0_pc == BootPc);
PC_Cont0: assert property (s0_upd && past_valid  |-> s0_pc == past_pc);
PC_Cont1: assert property (s1_upd                |-> s1_pc == s0_post_pc);

////////////////////// GPR operand continuity //////////////////////

// Operands Kudu forwards must equal the latest spec value of the register
// (at least as strict: Kudu may have cleared a tag).
Reg_Cont0_Rs1: assert property (
  s0_upd && !s0_irq && s0_dec.rf_ren[0] && (s0_dec.rs1 != 0) && past_has_reg[s0_dec.rs1]
  |-> alas(past_regs[s0_dec.rs1], op2sail(s0_op.d0)));
Reg_Cont0_Rs2: assert property (
  s0_upd && !s0_irq && s0_dec.rf_ren[1] && (s0_dec.rs2 != 0) && past_has_reg[s0_dec.rs2]
  |-> alas(past_regs[s0_dec.rs2], op2sail(s0_op.d1)));
Reg_Cont1_Rs1: assert property (
  s1_upd && s1_dec.rf_ren[0] && (s1_dec.rs1 != 0) && s1_chain_has[s1_dec.rs1]
  |-> alas(s1_chain_regs[s1_dec.rs1], op2sail(s1_op.d0)));
Reg_Cont1_Rs2: assert property (
  s1_upd && s1_dec.rf_ren[1] && (s1_dec.rs2 != 0) && s1_chain_has[s1_dec.rs2]
  |-> alas(s1_chain_regs[s1_dec.rs2], op2sail(s1_op.d1)));

////////////////////// Serialised steps //////////////////////

// At CSM_ISSUE_SPECIAL every older instruction has committed, so Kudu's CSRs
// must equal spec_past_*. The cycle after a trap entry (csr_save_cause) or a
// non-LS serialised instruction (mret, wfi, fence.i, ...) they must equal
// the post-state of that step.
logic special_pre_chk, special_post_chk_q;

assign special_pre_chk = s0_upd && st_special && past_valid;

always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) special_post_chk_q <= 1'b0;
  else         special_post_chk_q <= `KDUT.csr_save_cause ||
                                     (s0_upd && st_special && !`KISS.ir0_pl_sel[3] && !s0_cmplx);
end

`define KCSR_CHK(NAME, EN) \
  NAME``_Priv:      assert property (EN |-> dut_priv == past_priv); \
  NAME``_Mstatus:   assert property (EN |-> dut_mstatus == past_mstatus); \
  NAME``_Mie:       assert property (EN |-> dut_mie == past_mie); \
  NAME``_Mcause:    assert property (EN |-> dut_mcause == past_mcause); \
  NAME``_Mtval:     assert property (EN |-> dut_mtval == past_mtval); \
  NAME``_Mscratch:  assert property (EN |-> dut_mscratch == past_mscratch); \
  NAME``_Mshwm:     assert property (EN |-> dut_mshwm == past_mshwm); \
  NAME``_Mshwmb:    assert property (EN |-> dut_mshwmb == past_mshwmb); \
  NAME``_Mtvec:     assert property (EN |-> cap_eq(dut_mtvec, past_mtvec)); \
  NAME``_Mepc:      assert property (EN |-> xepc_eq(dut_mepc, past_mepc)); \
  NAME``_Mscratchc: assert property (EN |-> cap_eq(dut_mscratchc, past_mscratchc)); \
  NAME``_Mtdc:      assert property (EN |-> cap_eq(dut_mtdc, past_mtdc));

`KCSR_CHK(Special_State, special_pre_chk)
`KCSR_CHK(Special_Post,  special_post_chk_q)

`undef KCSR_CHK

Special_State_Pcc: assert property (special_pre_chk |-> pcc_eq_noaddr(dut_pcc_at(s0_pc), past_pcc));
Special_Post_Pcc:  assert property (special_post_chk_q |-> pcc_eq_noaddr(dut_pcc_at(past_pc), past_pcc));

// Issue-time exceptions and interrupts trap in the spec too; a non-LS
// SYSCTL instruction traps exactly when Kudu saves a cause (ecall/ebreak).
Special_TrapExec:   assert property (s0_upd && s0_exec |-> s0_trap);
Special_TrapIrq:    assert property (s0_upd && s0_irq  |-> s0_trap);
Special_TrapSysctl: assert property (s0_upd && s0_sysctl && !`KISS.ir0_pl_sel[3]
                                     |-> s0_trap == `KDUT.csr_save_cause);

// Serialised steps without a scoreboard entry write no GPR (an AMO writes
// through its cmplx_unit entries).
Special_NoWrite: assert property (s0_upd && st_special && !(|`KISS.ir0_pl_sel[4:1]) && !s0_cmplx
                                  |-> !(s0_wx_en && (s0_wx_addr != 0)));

////////////////////// Trap/target PC //////////////////////

// special_pc_q is Kudu's PC target for setpc specials (trap handler, mepc for
// mret, pc+4 for fence.i) and for cmt_flush (trap handler).
Exc_HandlerPC: assert property (s0_upd && st_special && `KISS.special_setpc_q
                                |-> `KISS.special_pc_q == s0_post_pc);
Exc_FlushPC:   assert property (`KISS.ctrl_fsm_cs[super_pkg::CSM_CMT_FLUSH] && `KDUT.csr_save_cause && past_valid
                                |-> `KISS.special_pc_q == past_pc);

////////////////////// Local instructions //////////////////////

// Normally issued instructions with no scoreboard entry (branches) neither
// trap nor write a GPR.
logic s0_local, s1_local;
assign s0_local = s0_normal && !(|`KISS.ir0_pl_sel[4:1]);
assign s1_local = !(|`KISS.ir1_pl_sel[4:1]);

Local_NoTrap0:  assert property (s0_upd && s0_local |-> !s0_trap);
Local_NoTrap1:  assert property (s1_upd && s1_local |-> !s1_trap);
Local_NoWrite0: assert property (s0_upd && s0_local |-> !(s0_wx_en && (s0_wx_addr != 0)));
Local_NoWrite1: assert property (s1_upd && s1_local |-> !(s1_wx_en && (s1_wx_addr != 0)));

////////////////////// Commit //////////////////////

logic                      cmt_we    [2];
logic [4:0]                cmt_waddr [2];
logic [super_pkg::RegW-1:0] cmt_wdata [2];
logic                      cmt_chk   [2];

for (genvar k = 0; k < 2; k++) begin : g_cmt
  logic is_ls, we_ls, we_alu;
  assign is_ls  = cmt_fpl[k][3];
  // A load whose write is dropped because the paired instruction writes the
  // same register still counts as written (regfile write ordering).
  assign we_ls  = `KDUT.rf_we2 ||
                  ((k == 0) && `KCMT.load_early && `KCMT.load_waddr_conflict);
  assign we_alu = (k == 0) ? `KDUT.rf_we0 : `KDUT.rf_we1;

  assign cmt_we[k]    = is_ls ? we_ls : we_alu;
  assign cmt_waddr[k] = is_ls ? `KDUT.rf_waddr2 : ((k == 0) ? `KDUT.rf_waddr0 : `KDUT.rf_waddr1);
  assign cmt_wdata[k] = is_ls ? `KDUT.rf_wdata2 : ((k == 0) ? `KDUT.rf_wdata0 : `KDUT.rf_wdata1);
  assign cmt_chk[k]   = `KCMT.sbd_deq[k] && cmt_fvalid[k] && !cmt_fshadow[k];

  Fol_Valid: assert property (`KCMT.sbd_deq[k] |-> cmt_fvalid[k]);
  Fol_Pc:    assert property (`KCMT.sbd_deq[k] && cmt_fvalid[k] |->
                              cmt_fpc[k] == ((k == 0) ? `KDUT.sbdfifo_rdata0.pc : `KDUT.sbdfifo_rdata1.pc));
  Fol_Pl:    assert property (`KCMT.sbd_deq[k] && cmt_fvalid[k] |->
                              cmt_fpl[k] == ((k == 0) ? `KDUT.sbdfifo_rdata0.pl : `KDUT.sbdfifo_rdata1.pl));

  // Kudu reports an error for the entry exactly when the spec trapped.
  Cmt_Trap: assert property (cmt_chk[k] |-> `KCMT.instr_err[k] == cmt_ferr[k]);

  // GPR write: address and value of the spec wX/wC; no write otherwise.
  // Divide data is reported separately (Cmt_DivData): it rests on
  // Env_DivLemma (spec_instance.sv), which composes two lemmas proven outside
  // this harness, so the integer/CHERI write data above stays assumption-free.
  logic is_div;
  assign is_div = cmt_fpl[k][4] && `KDUT.mult_pipeline_i.wb_reg.flags.is_div;
  Cmt_Wr: assert property (cmt_chk[k] && !cmt_ferr[k] && cmt_fwx_en[k] && (cmt_fwx_addr[k] != 0)
                           |-> cmt_we[k] && (cmt_waddr[k] == cmt_fwx_addr[k]) &&
                               (is_div || alas(cmt_fwx[k], rfw2sail(cmt_wdata[k]))));
  Cmt_DivData: assert property (cmt_chk[k] && !cmt_ferr[k] && cmt_fwx_en[k] && (cmt_fwx_addr[k] != 0) &&
                                is_div |-> alas(cmt_fwx[k], rfw2sail(cmt_wdata[k])));
  Cmt_NoWr: assert property (cmt_chk[k] && !cmt_ferr[k] && !(cmt_fwx_en[k] && (cmt_fwx_addr[k] != 0))
                             |-> !(cmt_we[k] && (cmt_waddr[k] != 0)));
end

////////////////////// Memory //////////////////////

logic mem_chk;
assign mem_chk = data_req_o && lsq_req_ent.valid && !lsq_req_ent.shadow && !lsq_req_ent.trap;

// An SC.W always makes a write request; the memory performs it only when the
// reservation holds (data_sc_fail_i = 0, tied to the spec's sc_ok by
// Mem_ScFail). A failing SC has no spec write, so its data/be are unchecked.
logic req_wr;
assign req_wr = lsq_req_ent.wr || lsq_req_ent.sc;

// No bus request from a shadow (younger than a trapping) instruction.
Mem_ReqEnt:      assert property (data_req_o |-> lsq_req_ent.valid);
Mem_NoShadowReq: assert property (data_req_o |-> !lsq_req_ent.shadow);

// At ls_go: a request is made iff the spec does not trap, and the access is
// split iff the spec accesses a second word. Exception: early loads (RAM
// region only, ls_pipeline decode_early_load_addr) skip the request-side
// CHERI check and are checked at the response, so a trapping early load may
// still issue a read.
Mem_GoReq:     assert property (`KLSU.ls_go && lsq_head.valid && !lsq_head.shadow && !lsq_head.trap
                                |-> data_req_o);
Mem_GoTrap:    assert property (`KLSU.ls_go && lsq_head.valid && !lsq_head.shadow && lsq_head.trap
                                |-> !data_req_o || `KLSU.lsu_req_info_i.early_load);
Mem_TrapRead:  assert property (data_req_o && lsq_req_ent.valid && lsq_req_ent.trap
                                |-> !data_we_o);
Mem_GoSplit: assert property (`KLSU.ls_go && lsq_head.valid && !lsq_head.shadow && !lsq_head.trap
                              |-> `KLSU.split_misaligned_access ==
                                  (lsq_head.rd ? (!lsq_head.rd_cap && lsq_head.rd_snd)
                                               : (!lsq_head.wr_cap && lsq_head.wr_snd)));
// CSR instructions make no memory access in the spec.
// A trapping entry's rd/wr are meaningless (no access either way).
Mem_CsrGo:   assert property (`KLSU.csr_go && lsq_head.valid && !lsq_head.shadow && !lsq_head.trap
                              |-> !lsq_head.rd && !lsq_head.wr);

// Request kind.
Mem_Kind:  assert property (mem_chk |-> (lsq_req_ent.rd != req_wr) &&
                                        (data_we_o == req_wr));
Mem_IsCap: assert property (mem_chk |-> data_is_cap_o == (lsq_req_ent.wr ? lsq_req_ent.wr_cap
                                                                         : lsq_req_ent.rd_cap));
Mem_Idx:   assert property (mem_chk |-> !lsq_req_idx ||
                                        (req_wr ? (lsq_req_ent.wr_snd && !lsq_req_ent.wr_cap)
                                                        : (lsq_req_ent.rd_snd && !lsq_req_ent.rd_cap)));

// Integer accesses: word-aligned address, byte enables and enabled bytes.
function automatic logic be_data_eq(logic [3:0] be, logic [31:0] a, logic [31:0] b);
  logic eq;
  eq = 1'b1;
  for (int i = 0; i < 4; i++) if (be[i] && (a[8*i +: 8] != b[8*i +: 8])) eq = 1'b0;
  return eq;
endfunction

logic [31:0] mem_spec_addr;
assign mem_spec_addr = lsq_req_ent.sc ? lsq_req_ent.sc_addr :
                       lsq_req_ent.wr ? (lsq_req_idx ? lsq_req_ent.wr_snd_addr : lsq_req_ent.wr_fst_addr)
                                      : (lsq_req_ent.rd_snd ? (lsq_req_idx ? lsq_req_ent.rd_snd_addr
                                                                           : lsq_req_ent.rd_fst_addr)
                                                            : lsq_req_ent.rd_fst_addr);

Mem_Addr: assert property (mem_chk |-> data_addr_o == {mem_spec_addr[31:2], 2'b00});

Mem_StoreBe:   assert property (mem_chk && lsq_req_ent.wr && !lsq_req_ent.wr_cap
                                |-> data_be_o == (lsq_req_idx ? lsq_req_ent.wr_snd_be : lsq_req_ent.wr_fst_be));
Mem_StoreData: assert property (mem_chk && lsq_req_ent.wr && !lsq_req_ent.wr_cap
                                |-> be_data_eq(data_be_o, data_wdata_o[31:0],
                                               lsq_req_ent.wr_snd ? (lsq_req_idx ? lsq_req_ent.wr_snd_data
                                                                                 : lsq_req_ent.wr_fst_data)
                                                                  : lsq_req_ent.wr_fst_data));

// Capability stores: one 65-bit transaction carrying address word and tag;
// a tagged capability decodes to the spec capability.
Mem_CapStoreAddr: assert property (mem_chk && lsq_req_ent.wr && lsq_req_ent.wr_cap
                                   |-> data_wdata_o[31:0] == lsq_req_ent.wr_fst_data);
Mem_CapStoreTag:  assert property (mem_chk && lsq_req_ent.wr && lsq_req_ent.wr_cap
                                   |-> data_wdata_o[MemW-1] == lsq_req_ent.wr_tag);
Mem_CapStoreCap:  assert property (mem_chk && lsq_req_ent.wr && lsq_req_ent.wr_cap && lsq_req_ent.wr_tag
                                   |-> cap_eq(memcap2sail(cheri_pkg::mem_cap_t'(data_wdata_o)),
                                              capBitsToCapability(1'b1, {lsq_req_ent.wr_snd_data,
                                                                         lsq_req_ent.wr_fst_data})));
// An untagged capability store writes the spec's 64 bits unchanged (Sail
// stores capToBits of the register, tag or not).
Mem_CapStoreBits: assert property (mem_chk && lsq_req_ent.wr && lsq_req_ent.wr_cap && !lsq_req_ent.wr_tag
                                   |-> data_wdata_o[63:0] == {lsq_req_ent.wr_snd_data, lsq_req_ent.wr_fst_data});
Mem_CapStoreBe:   assert property (mem_chk && lsq_req_ent.wr && lsq_req_ent.wr_cap |-> data_be_o == 4'hf);

// data_amo_flag_o: LR 0001, SC 0010, AMO read 0100 / write 1000, else 0.
Mem_AmoFlag: assert property (mem_chk |-> data_amo_flag_o == lsq_req_ent.amo_flag);

// cheri_fatal_err_o (Kudu, informational) vs the spec's mtcc_unrecoverable:
// the spec flags a fetch exception taken while MTCC itself fails the fetch
// checks; Kudu flags any trap entry (csr_save_cause) with such an MTCC. A
// fetch exception is an issue-time trap, entered in the issue cycle, so
// Kudu's flag must be set in the next cycle. Waived: MTCC address within 2
// bytes of top (addr <= top < addr + 2), which the spec treats as out of
// bounds (whole parcel) and Kudu does not (cs_registers.sv comment).
logic fatal_near_top;
assign fatal_near_top = (33'(`KCSR.gen_scr.mtvec_fcap.addr) <= `KCSR.gen_scr.mtvec_fcap.top33) &&
                        (33'(`KCSR.gen_scr.mtvec_fcap.addr) + 33'd2 > `KCSR.gen_scr.mtvec_fcap.top33);
Out_FatalErr0: assert property (s0_upd && s0_mtcc_unrec && !fatal_near_top
                                |-> `KDUT.csr_save_cause ##1 cheri_fatal_err_o);
Out_FatalErr1: assert property (!(s1_upd && s1_mtcc_unrec));
Cov_FatalErr:  cover property (s0_upd && s0_mtcc_unrec ##1 cheri_fatal_err_o);

// Bus request stability: an ungranted request is held, unchanged, to the next
// cycle.
Bus_InstrReqHold: assert property (instr_req_o && !instr_gnt_i |=> instr_req_o && $stable(instr_addr_o));
Bus_DataReqHold:  assert property (data_req_o && !data_gnt_i
                                   |=> data_req_o && $stable({data_addr_o, data_we_o, data_be_o, data_is_cap_o}) &&
                                       (!data_we_o || $stable(data_wdata_o)));

// Load data: the bus response returns the data given to the spec (symbolic
// memory). Assumes, not asserts: they tie the free spec read inputs to the
// bus data.
logic rsp_chk;
assign rsp_chk = data_rvalid_i && lsq_rsp_ent_q.valid && !lsq_rsp_ent_q.shadow && lsq_rsp_ent_q.rd;

Mem_RdataInt: assume property (rsp_chk && !lsq_rsp_ent_q.rd_cap
                               |-> data_rdata_i[31:0] == (lsq_rsp_idx_q ? lsq_rsp_ent_q.rd_snd_data
                                                                        : lsq_rsp_ent_q.rd_fst_data));
Mem_RdataCapAddr: assume property (rsp_chk && lsq_rsp_ent_q.rd_cap
                                   |-> data_rdata_i[31:0] == lsq_rsp_ent_q.rd_fst_data);
Mem_RdataCapTag:  assume property (rsp_chk && lsq_rsp_ent_q.rd_cap
                                   |-> data_rdata_i[MemW-1] == lsq_rsp_ent_q.rd_tag);
Mem_RdataCap:     assume property (rsp_chk && lsq_rsp_ent_q.rd_cap
                                   |-> cap_eq(memcap2sail(cheri_pkg::mem_cap_t'(data_rdata_i)),
                                              capBitsToCapability(lsq_rsp_ent_q.rd_tag,
                                                                  {lsq_rsp_ent_q.rd_snd_data,
                                                                   lsq_rsp_ent_q.rd_fst_data})));
// SC.W response: the memory reports the reservation outcome the spec was
// given (both free; this only ties them).
Mem_ScFail: assume property (data_rvalid_i && lsq_rsp_ent_q.valid && !lsq_rsp_ent_q.shadow &&
                             !lsq_rsp_ent_q.trap && lsq_rsp_ent_q.sc
                             |-> data_sc_fail_i == !lsq_rsp_ent_q.sc_ok);
// Memory holds only capabilities software can derive: a tagged capability is
// well formed (E <= 24, 0 <= base <= top <= 2^32). Kudu and Sail legitimately
// differ on malformed encodings (CEX_TRIAGE.md cause E).
Mem_RdataCapWF:   assume property (rsp_chk && lsq_rsp_ent_q.rd_cap
                                   |-> cap_well_formed(capBitsToCapability(lsq_rsp_ent_q.rd_tag,
                                                                           {lsq_rsp_ent_q.rd_snd_data,
                                                                            lsq_rsp_ent_q.rd_fst_data})));
// The same for every tagged bus response, including loads in a trap shadow
// (no rsp_chk): their data still enters the LS write-back FIFO. Untagged
// responses are unconstrained, so integer load data stay free.
Mem_RdataCapWFAny: assume property (data_rvalid_i && data_rdata_i[MemW-1]
                                    |-> cap_well_formed(memcap2sail(cheri_pkg::mem_cap_t'(data_rdata_i))));
// The same assumption at the spec's read, which comes at issue, before the DUT
// response that Mem_RdataCapWF constrains: otherwise a bounded trace that
// ends before the response (or a flushed load) can give the spec a malformed
// capability.
Mem_SpecRdCapWF0: assume property (s0_mem_read && s0_mem_read_cap
                                   |-> cap_well_formed(capBitsToCapability(spec0_rd_tag_i,
                                                                           {spec0_rd_snd_i, spec0_rd_fst_i})));
Mem_SpecRdCapWF1: assume property (s1_mem_read && s1_mem_read_cap
                                   |-> cap_well_formed(capBitsToCapability(spec1_rd_tag_i,
                                                                           {spec1_rd_snd_i, spec1_rd_fst_i})));

////////////////////// CSR instructions //////////////////////

// mstatus.mie and the PCC are excluded here: a younger CJALR may update them
// before this point. They are checked at serialised points (Special_*).
CSR_Post_Priv:      assert property (csr_chk2_q |-> dut_priv == csr_ent2_q.priv);
CSR_Post_Mstatus:   assert property (csr_chk2_q |-> (dut_mstatus.mpie == csr_ent2_q.mstatus.mpie) &&
                                                    (dut_mstatus.mpp  == csr_ent2_q.mstatus.mpp)  &&
                                                    (dut_mstatus.mprv == csr_ent2_q.mstatus.mprv) &&
                                                    (dut_mstatus.tw   == csr_ent2_q.mstatus.tw));
CSR_Post_Mie:       assert property (csr_chk2_q |-> dut_mie == csr_ent2_q.mie);
CSR_Post_Mcause:    assert property (csr_chk2_q |-> dut_mcause == csr_ent2_q.mcause);
CSR_Post_Mtval:     assert property (csr_chk2_q |-> dut_mtval == csr_ent2_q.mtval);
CSR_Post_Mscratch:  assert property (csr_chk2_q |-> dut_mscratch == csr_ent2_q.mscratch);
CSR_Post_Mshwm:     assert property (csr_chk2_q |-> dut_mshwm == csr_ent2_q.mshwm);
CSR_Post_Mshwmb:    assert property (csr_chk2_q |-> dut_mshwmb == csr_ent2_q.mshwmb);
CSR_Post_Mtvec:     assert property (csr_chk2_q |-> cap_eq(dut_mtvec, csr_ent2_q.mtvec));
CSR_Post_Mepc:      assert property (csr_chk2_q |-> xepc_eq(dut_mepc, csr_ent2_q.mepc));
CSR_Post_Mscratchc: assert property (csr_chk2_q |-> cap_eq(dut_mscratchc, csr_ent2_q.mscratchc));
CSR_Post_Mtdc:      assert property (csr_chk2_q |-> cap_eq(dut_mtdc, csr_ent2_q.mtdc));

////////////////////// Covers //////////////////////

for (genvar k = 0; k < 2; k++) begin : g_cov_cmt
  Cov_CmtAlu:   cover property (cmt_chk[k] && !cmt_ferr[k] && (cmt_fpl[k][2:1] != 0) && !cmt_fpl[k][0]);
  Cov_CmtJump:  cover property (cmt_chk[k] && !cmt_ferr[k] && cmt_fpl[k][0]);
  Cov_CmtMult:  cover property (cmt_chk[k] && !cmt_ferr[k] && cmt_fpl[k][4] && !cmt_fpl[k][0]);
  Cov_CmtLs:    cover property (cmt_chk[k] && !cmt_ferr[k] && cmt_fpl[k][3]);
  Cov_CmtWrite: cover property (cmt_chk[k] && !cmt_ferr[k] && cmt_we[k] && (cmt_waddr[k] != 0));
  Cov_CmtErr:   cover property (cmt_chk[k] && cmt_ferr[k]);
end

Cov_Step0:       cover property (s0_upd);
Cov_DualIssue:   cover property (s1_upd);
Cov_Branch:      cover property (s0_upd && s0_local);
Cov_Load:        cover property (mem_chk && lsq_req_ent.rd && !lsq_req_ent.rd_cap);
Cov_Store:       cover property (mem_chk && lsq_req_ent.wr && !lsq_req_ent.wr_cap);
Cov_LoadCap:     cover property (mem_chk && lsq_req_ent.rd_cap);
Cov_StoreCap:    cover property (mem_chk && lsq_req_ent.wr_cap);
Cov_Misaligned:  cover property (mem_chk && lsq_req_idx);
Cov_LoadRsp:     cover property (rsp_chk);
Cov_Csr:         cover property (csr_chk2_q);
Cov_Sysctl:      cover property (s0_upd && s0_sysctl);
Cov_Ecall:       cover property (s0_upd && s0_sysctl && `KDUT.csr_save_cause);
Cov_Mret:        cover property (s0_upd && s0_sysctl && `KDUT.csr_restore_mret);
Cov_Exec:        cover property (s0_upd && s0_exec);
Cov_FetchExc:    cover property (s0_upd && s0_exec && (s0_mode == MAIN_IFERR));
Cov_Irq:         cover property (s0_upd && s0_irq);
Cov_CmtFlush:    cover property (`KISS.ctrl_fsm_cs[super_pkg::CSM_CMT_FLUSH] && `KDUT.csr_save_cause);
Cov_SpecialPost: cover property (special_post_chk_q);

// A and B extensions (scope widened 2026-11-26).
function automatic logic f_opc(logic [31:0] i, logic [6:0] o); return i[6:0] == o; endfunction
Cov_Lr:       cover property (mem_chk && (lsq_req_ent.amo_flag == 4'b0001));
Cov_ScOk:     cover property (mem_chk && lsq_req_ent.sc && lsq_req_ent.sc_ok);
Cov_ScFail:   cover property (mem_chk && lsq_req_ent.sc && !lsq_req_ent.sc_ok);
Cov_ScRsp:    cover property (data_rvalid_i && lsq_rsp_ent_q.valid && lsq_rsp_ent_q.sc && data_sc_fail_i);
Cov_AmoStep:  cover property (s0_upd && s0_cmplx && !s0_trap);
Cov_AmoTrap:  cover property (s0_upd && s0_cmplx && s0_trap);
Cov_AmoRd:    cover property (mem_chk && (lsq_req_ent.amo_flag == 4'b0100));
Cov_AmoWr:    cover property (mem_chk && (lsq_req_ent.amo_flag == 4'b1000));
Cov_AmoCmt:   cover property (cmt_chk[0] && !cmt_ferr[0] && cmt_fpl[0][3] && cmt_fwx_en[0] &&
                              (cmt_fwx_addr[0] != 0) && (`KCPX.cmplx_fsm_cs == 2'h3));
Cov_AmoDone:  cover property (`KISS.ctrl_fsm_cs[super_pkg::CSM_WAIT_CMPLX] ##1
                              `KISS.ctrl_fsm_cs[super_pkg::CSM_WAIT_FINAL]);
Cov_BZba:     cover property (s0_upd && !s0_trap && f_opc(s0_dec.insn, 7'h33) && (s0_dec.insn[31:25] == 7'h10));
Cov_BClmul:   cover property (s0_upd && !s0_trap && f_opc(s0_dec.insn, 7'h33) && (s0_dec.insn[31:25] == 7'h05) &&
                              (s0_dec.insn[14] == 1'b0));
Cov_BMinMax:  cover property (s0_upd && !s0_trap && f_opc(s0_dec.insn, 7'h33) && (s0_dec.insn[31:25] == 7'h05) &&
                              s0_dec.insn[14]);
Cov_BRot:     cover property (s0_upd && !s0_trap && f_opc(s0_dec.insn, 7'h33) && (s0_dec.insn[31:25] == 7'h30));
Cov_BUnary:   cover property (s0_upd && !s0_trap && f_opc(s0_dec.insn, 7'h13) && (s0_dec.insn[31:25] == 7'h30) &&
                              (s0_dec.insn[14:12] == 3'd1));
Cov_BBit:     cover property (s0_upd && !s0_trap && (s0_dec.insn[31:25] inside {7'h14, 7'h24, 7'h34}));
Cov_BIllegal: cover property (s0_upd && s0_exec && f_opc(s0_dec.insn, 7'h33) && (s0_dec.insn[31:25] == 7'h04) &&
                              (s0_dec.insn[24:20] != 5'd0));
