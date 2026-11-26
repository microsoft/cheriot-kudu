// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Followers (README section 4.3). Included inside kudu_e2e_top after
// spec_instance.sv.
//
// 1. Scoreboard follower: one entry per sbd_fifo slot, holding the spec
//    results of the instruction written there. It is written with the
//    fifo's own write enables/addresses, read with the committer's dequeue
//    and the fifo's read addresses, and cleared by cmt_flush.
//
// 2. LS follower: the spec memory/CSR results of every instruction issued to
//    ls_pipeline, in issue order. ls_pipeline executes in order, so the head
//    entry belongs to the next LSU ls_go/csr_go. The entry of the current LSU
//    request is kept in lsq_cur_q until the next go; the entry of each granted
//    bus request is kept for its response (one cycle later, see Env_DataRsp).
//
// AMOs (cmplx_unit) are one spec step (s0_cmplx, at CSM_ISSUE_SPECIAL) but
// two LSU requests and two scoreboard entries: a read (amo_flag 0100, no GPR
// write, carries the spec trap) and a write (amo_flag 1000, carries wX).
// The LS follower gets a read entry at the step and the write entry in the
// next cycle (cmplx_unit cannot request the write earlier: AMO_WAIT_RD needs
// the read response); the scoreboard follower takes cmplx_sbd_wr writes
// from the step (read) or from amo_rec_* (write).

localparam int SbdDepth = 8;
localparam int LsqDepth = 4;

////////////////////// Scoreboard follower //////////////////////

logic        fol_valid  [SbdDepth];
logic        fol_shadow [SbdDepth];
logic        fol_err    [SbdDepth];
logic [4:0]  fol_pl     [SbdDepth];
logic [31:0] fol_pc     [SbdDepth];
logic        fol_wx_en  [SbdDepth];
logic [4:0]  fol_wx_addr[SbdDepth];
t_Capability fol_wx     [SbdDepth];

// Source of each fifo write port: port 0 takes ir0 unless only ir1 writes
// the scoreboard (ir0 is a local instruction), port 1 always takes ir1.
// cmplx_unit writes port 0 (cmplx_sbd_wr, no other write in that cycle).
logic [1:0]  sbd_wr_src1;
assign sbd_wr_src1[0] = ~`KISS.ir_fifo_wr[0];
assign sbd_wr_src1[1] = 1'b1;

`define KCPX `KDUT.comlx_unit_i
logic        amo_sbd_rd;   // cmplx_unit writes the read entry (start cycle)
assign amo_sbd_rd = `KDUT.cmplx_sbd_wr && (`KCPX.cmplx_fsm_cs == 2'h0);

// Spec results of the latest AMO step, for its write entry.
logic        amo_rec_v_q, amo_rec_shadow_q, amo_rec_wx_en_q;
logic [31:0] amo_rec_pc_q;
logic [4:0]  amo_rec_wx_addr_q;
t_Capability amo_rec_wx_q;

always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    amo_rec_v_q       <= 1'b0;
    amo_rec_shadow_q  <= 1'b0;
    amo_rec_wx_en_q   <= 1'b0;
    amo_rec_pc_q      <= '0;
    amo_rec_wx_addr_q <= '0;
    amo_rec_wx_q      <= nullCap();
  end else if (`KDUT.cmt_flush) begin
    amo_rec_v_q <= 1'b0;
  end else if (s0_cmplx) begin
    amo_rec_v_q       <= !s0_trap;
    amo_rec_shadow_q  <= s0_shadow;
    amo_rec_wx_en_q   <= s0_wx_en;
    amo_rec_pc_q      <= s0_pc;
    amo_rec_wx_addr_q <= s0_wx_addr;
    amo_rec_wx_q      <= s0_wx;
  end
end

logic        sw_shadow [2];
logic        sw_err    [2];
logic [4:0]  sw_pl     [2];
logic [31:0] sw_pc     [2];
logic        sw_wx_en  [2];
logic [4:0]  sw_wx_addr[2];
t_Capability sw_wx     [2];

for (genvar k = 0; k < 2; k++) begin : g_sbd_src
  always_comb begin
    if ((k == 0) && `KDUT.cmplx_sbd_wr) begin
      sw_pl[k]      = 5'h1 << 3;
      sw_shadow[k]  = amo_sbd_rd ? s0_shadow : amo_rec_shadow_q;
      sw_err[k]     = amo_sbd_rd ? s0_trap   : 1'b0;
      sw_pc[k]      = amo_sbd_rd ? s0_pc     : amo_rec_pc_q;
      sw_wx_en[k]   = amo_sbd_rd ? 1'b0      : amo_rec_wx_en_q;
      sw_wx_addr[k] = amo_rec_wx_addr_q;
      sw_wx[k]      = amo_rec_wx_q;
    end else if (sbd_wr_src1[k]) begin
      sw_pl[k]      = `KISS.ir1_pl_sel;
      sw_shadow[k]  = s1_shadow;
      sw_err[k]     = s1_trap;
      sw_pc[k]      = s1_pc;
      sw_wx_en[k]   = s1_wx_en;
      sw_wx_addr[k] = s1_wx_addr;
      sw_wx[k]      = s1_wx;
    end else begin
      sw_pl[k]      = `KISS.ir0_pl_sel;
      sw_shadow[k]  = s0_shadow;
      sw_err[k]     = s0_trap;
      sw_pc[k]      = s0_pc;
      sw_wx_en[k]   = s0_wx_en;
      sw_wx_addr[k] = s0_wx_addr;
      sw_wx[k]      = s0_wx;
    end
  end
end

always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    for (int e = 0; e < SbdDepth; e++) begin
      fol_valid[e]   <= 1'b0;
      fol_shadow[e]  <= 1'b0;
      fol_err[e]     <= 1'b0;
      fol_pl[e]      <= '0;
      fol_pc[e]      <= '0;
      fol_wx_en[e]   <= 1'b0;
      fol_wx_addr[e] <= '0;
      fol_wx[e]      <= nullCap();
    end
  end else if (`KDUT.cmt_flush) begin
    for (int e = 0; e < SbdDepth; e++) fol_valid[e] <= 1'b0;
  end else begin
    for (int k = 0; k < 2; k++) begin
      if (`KCMT.sbd_deq[k]) fol_valid[`KSBD.rd_mem_addr[k]] <= 1'b0;
    end
    for (int k = 0; k < 2; k++) begin
      if (`KSBD.wr_data_en[k]) begin
        fol_valid  [`KSBD.wr_mem_addr[k]] <= 1'b1;
        fol_shadow [`KSBD.wr_mem_addr[k]] <= sw_shadow[k];
        fol_err    [`KSBD.wr_mem_addr[k]] <= sw_err[k];
        fol_pl     [`KSBD.wr_mem_addr[k]] <= sw_pl[k];
        fol_pc     [`KSBD.wr_mem_addr[k]] <= sw_pc[k];
        fol_wx_en  [`KSBD.wr_mem_addr[k]] <= sw_wx_en[k];
        fol_wx_addr[`KSBD.wr_mem_addr[k]] <= sw_wx_addr[k];
        fol_wx     [`KSBD.wr_mem_addr[k]] <= sw_wx[k];
      end
    end
  end
end

// Entry at each committer read port.
logic [2:0]  cmt_idx      [2];
logic        cmt_fvalid   [2];
logic        cmt_fshadow  [2];
logic        cmt_ferr     [2];
logic [4:0]  cmt_fpl      [2];
logic [31:0] cmt_fpc      [2];
logic        cmt_fwx_en   [2];
logic [4:0]  cmt_fwx_addr [2];
t_Capability cmt_fwx      [2];

for (genvar k = 0; k < 2; k++) begin : g_cmt_port
  assign cmt_idx[k]      = `KSBD.rd_mem_addr[k];
  assign cmt_fvalid[k]   = fol_valid  [cmt_idx[k]];
  assign cmt_fshadow[k]  = fol_shadow [cmt_idx[k]];
  assign cmt_ferr[k]     = fol_err    [cmt_idx[k]];
  assign cmt_fpl[k]      = fol_pl     [cmt_idx[k]];
  assign cmt_fpc[k]      = fol_pc     [cmt_idx[k]];
  assign cmt_fwx_en[k]   = fol_wx_en  [cmt_idx[k]];
  assign cmt_fwx_addr[k] = fol_wx_addr[cmt_idx[k]];
  assign cmt_fwx[k]      = fol_wx     [cmt_idx[k]];
end

////////////////////// LS follower //////////////////////

// Spec CSR state tracked by group E (inv.sv); mshwm is not covered.
typedef struct {
  t_Privilege    priv;
  kudu_mstatus_t mstatus;
  logic [31:0]   mie, mcause, mtval, mscratch, mshwmb;
  t_Capability   mtvec, mepc, mscratchc, mtdc;
} e_st_t;

typedef struct {
  logic          valid;
  logic          shadow;
  logic          trap;
  logic [31:0]   pc;
  logic [31:0]   insn;     // decoded instruction word (ir_dec_t.insn)
  logic          csr;      // CSR instruction (applied at csr_chk1_q)
  logic          wmie;     // serialised CSR write to mstatus/mie
  e_st_t         pre;      // spec CSR state before the step
  logic [31:0]   pre_mshwm; // spec mshwm before the step (stores also write it)
  // spec memory reads, with the free read data given to the spec
  logic          rd;
  logic          rd_snd;
  logic          rd_cap;
  logic [31:0]   rd_fst_addr;
  logic [31:0]   rd_snd_addr;
  logic [31:0]   rd_fst_data;
  logic [31:0]   rd_snd_data;
  logic          rd_tag;
  // spec memory writes
  logic          wr;
  logic          wr_snd;
  logic          wr_cap;
  logic          wr_tag;
  logic [31:0]   wr_fst_addr;
  logic [31:0]   wr_snd_addr;
  logic [31:0]   wr_fst_data;
  logic [31:0]   wr_snd_data;
  logic [3:0]    wr_fst_be;
  logic [3:0]    wr_snd_be;
  // SC.W: the spec checked the reservation (sc), its free outcome (sc_ok)
  // and address; amo_flag: the data_amo_flag_o this request must carry
  logic          sc;
  logic          sc_ok;
  logic [31:0]   sc_addr;
  logic [3:0]    amo_flag;
  // spec CSR post-state (checked for CSR instructions)
  t_Privilege    priv;
  kudu_mstatus_t mstatus;
  logic [31:0]   mie;
  logic [31:0]   mcause;
  logic [31:0]   mtval;
  logic [31:0]   mscratch;
  logic [31:0]   mshwm;
  logic [31:0]   mshwmb;
  t_Capability   mtvec;
  t_Capability   mepc;
  t_Capability   mscratchc;
  t_Capability   mtdc;
  // Kudu's request for the instruction, as decoded by ls_pipeline at issue
  // (group F links its CHERI/CSR checks to trap)
  super_pkg::lsu_req_info_t kreq;
} lsq_ent_t;

lsq_ent_t s0_lent, s1_lent, lsq_push_ent, lsq_null;

// amo_flag of the (first) request: {amo1, amo0, sc, lr}.
function automatic logic [3:0] f_amo_flag(logic [31:0] insn);
  if (insn[6:0] != 7'h2f)       return 4'b0000;
  if (insn[31:27] == 5'b00010)  return 4'b0001;   // LR.W
  if (insn[31:27] == 5'b00011)  return 4'b0010;   // SC.W
  return 4'b0100;                                 // AMO read
endfunction

`define KLSQ_ENT(N, SH, PRE) \
  always_comb begin \
    s``N``_lent.valid       = 1'b1; \
    s``N``_lent.shadow      = SH; \
    s``N``_lent.trap        = s``N``_trap; \
    s``N``_lent.pc          = s``N``_pc; \
    s``N``_lent.insn        = s``N``_dec.insn; \
    s``N``_lent.csr         = s``N``_dec.is_csr; \
    s``N``_lent.wmie        = s``N``_dec.sysctl.csrw; \
    s``N``_lent.pre.priv      = PRE``priv; \
    s``N``_lent.pre.mstatus   = PRE``mstatus; \
    s``N``_lent.pre.mie       = PRE``mie; \
    s``N``_lent.pre.mcause    = PRE``mcause; \
    s``N``_lent.pre.mtval     = PRE``mtval; \
    s``N``_lent.pre.mscratch  = PRE``mscratch; \
    s``N``_lent.pre.mshwmb    = PRE``mshwmb; \
    s``N``_lent.pre.mtvec     = PRE``mtvec; \
    s``N``_lent.pre.mepc      = PRE``mepc; \
    s``N``_lent.pre.mscratchc = PRE``mscratchc; \
    s``N``_lent.pre.mtdc      = PRE``mtdc; \
    s``N``_lent.pre_mshwm     = PRE``mshwm; \
    s``N``_lent.rd          = s``N``_mem_read; \
    s``N``_lent.rd_snd      = s``N``_mem_read_snd; \
    s``N``_lent.rd_cap      = s``N``_mem_read_cap; \
    s``N``_lent.rd_fst_addr = s``N``_mem_read_fst_addr; \
    s``N``_lent.rd_snd_addr = s``N``_mem_read_snd_addr; \
    s``N``_lent.rd_fst_data = spec``N``_rd_fst_i; \
    s``N``_lent.rd_snd_data = spec``N``_rd_snd_i; \
    s``N``_lent.rd_tag      = spec``N``_rd_tag_i; \
    s``N``_lent.wr          = s``N``_mem_write; \
    s``N``_lent.wr_snd      = s``N``_mem_write_snd; \
    s``N``_lent.wr_cap      = s``N``_mem_write_cap; \
    s``N``_lent.wr_tag      = s``N``_mem_write_tag; \
    s``N``_lent.wr_fst_addr = s``N``_mem_write_fst_addr; \
    s``N``_lent.wr_snd_addr = s``N``_mem_write_snd_addr; \
    s``N``_lent.wr_fst_data = s``N``_mem_write_fst_wdata; \
    s``N``_lent.wr_snd_data = s``N``_mem_write_snd_wdata; \
    s``N``_lent.wr_fst_be   = s``N``_mem_write_fst_be; \
    s``N``_lent.wr_snd_be   = s``N``_mem_write_snd_be; \
    s``N``_lent.sc          = s``N``_mem_sc; \
    s``N``_lent.sc_ok       = spec``N``_sc_ok_i; \
    s``N``_lent.sc_addr     = s``N``_mem_sc_addr; \
    s``N``_lent.amo_flag    = f_amo_flag(s``N``_dec.insn); \
    s``N``_lent.priv        = s``N``_post_priv; \
    s``N``_lent.mstatus     = s``N``_post_mstatus; \
    s``N``_lent.mie         = s``N``_post_mie; \
    s``N``_lent.mcause      = s``N``_post_mcause; \
    s``N``_lent.mtval       = s``N``_post_mtval; \
    s``N``_lent.mscratch    = s``N``_post_mscratch; \
    s``N``_lent.mshwm       = s``N``_post_mshwm; \
    s``N``_lent.mshwmb      = s``N``_post_mshwmb; \
    s``N``_lent.mtvec       = s``N``_post_mtvec; \
    s``N``_lent.mepc        = s``N``_post_mepc; \
    s``N``_lent.mscratchc   = s``N``_post_mscratchc; \
    s``N``_lent.mtdc        = s``N``_post_mtdc; \
    s``N``_lent.kreq        = `KDUT.ls_pipeline_i.lsu_req_dec; \
  end

`KLSQ_ENT(0, s0_shadow, s0_pre_)
`KLSQ_ENT(1, s1_shadow, s0_post_)

`undef KLSQ_ENT

always_comb begin
  lsq_null       = s0_lent;
  lsq_null.valid = 1'b0;
end

// AMO entries: the read part at the step, the write part one cycle later.
lsq_ent_t amo_rd_ent, amo_wr_ent_q;
logic     amo_wr_pend_q;

always_comb begin
  amo_rd_ent          = s0_lent;
  amo_rd_ent.wr       = 1'b0;
  amo_rd_ent.wr_snd   = 1'b0;
  amo_rd_ent.wr_cap   = 1'b0;
end

always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    amo_wr_pend_q <= 1'b0;
    amo_wr_ent_q  <= lsq_null;
  end else begin
    amo_wr_pend_q <= s0_cmplx && !s0_trap && !`KDUT.cmt_flush;
    if (s0_cmplx) begin
      amo_wr_ent_q          <= s0_lent;
      amo_wr_ent_q.rd       <= 1'b0;
      amo_wr_ent_q.rd_snd   <= 1'b0;
      amo_wr_ent_q.rd_cap   <= 1'b0;
      amo_wr_ent_q.amo_flag <= 4'b1000;
    end
  end
end

// At most one instruction per cycle can go to ls_pipeline: ir1 cannot select
// a pipeline ir0 already uses (issuer ex_rdy_for_ir1). An AMO is serialised
// (pl_sel LOCAL), so its pushes never meet another.
logic lsq_push0, lsq_push1, lsq_pusha, lsq_push, lsq_go;

assign lsq_push0    = `KISS.ir0_issued & `KISS.ir0_pl_sel[3];
assign lsq_push1    = `KISS.ir1_issued & `KISS.ir1_pl_sel[3];
assign lsq_pusha    = s0_cmplx | amo_wr_pend_q;
assign lsq_push     = lsq_push0 | lsq_push1 | lsq_pusha;
assign lsq_push_ent = s0_cmplx      ? amo_rd_ent   :
                      amo_wr_pend_q ? amo_wr_ent_q :
                      lsq_push0     ? s0_lent      : s1_lent;
assign lsq_go       = `KLSU.ls_go | `KLSU.csr_go;

lsq_ent_t    lsq_mem[LsqDepth];
logic [1:0]  lsq_rp_q, lsq_wp_q;
logic [2:0]  lsq_cnt_q;
lsq_ent_t    lsq_head;
logic        lsq_bypass;

assign lsq_bypass = (lsq_cnt_q == 3'd0);
assign lsq_head   = lsq_bypass ? (lsq_push ? lsq_push_ent : lsq_null) : lsq_mem[lsq_rp_q];

always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    lsq_rp_q  <= '0;
    lsq_wp_q  <= '0;
    lsq_cnt_q <= '0;
    for (int e = 0; e < LsqDepth; e++) lsq_mem[e] <= lsq_null;
  end else if (`KDUT.cmt_flush) begin
    lsq_rp_q  <= '0;
    lsq_wp_q  <= '0;
    lsq_cnt_q <= '0;
  end else if (lsq_go && lsq_bypass) begin
    // The pushed entry (if any) is consumed in the same cycle.
  end else begin
    if (lsq_push) begin
      lsq_mem[lsq_wp_q] <= lsq_push_ent;
      lsq_wp_q          <= lsq_wp_q + 2'd1;
    end
    if (lsq_go) begin
      lsq_rp_q <= lsq_rp_q + 2'd1;
    end
    lsq_cnt_q <= lsq_cnt_q + 3'(lsq_push) - 3'(lsq_go);
  end
end

// Entry of the LSU request in flight, and request index within it
// (0 = first word, 1 = second word of a split misaligned access).
lsq_ent_t lsq_cur_q, lsq_req_ent;
logic     lsq_req_idx_q, lsq_req_idx;

assign lsq_req_ent = `KLSU.ls_go ? lsq_head : lsq_cur_q;
assign lsq_req_idx = `KLSU.ls_go ? 1'b0 : lsq_req_idx_q;

always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    lsq_cur_q     <= lsq_null;
    lsq_req_idx_q <= 1'b0;
  end else begin
    if (lsq_go) lsq_cur_q <= lsq_head;
    if (lsq_go)
      lsq_req_idx_q <= `KLSU.ls_go & data_req_o & data_gnt_i;
    else if (data_req_o && data_gnt_i)
      lsq_req_idx_q <= 1'b1;
  end
end

// Entry/index of the bus request granted in the previous cycle; its response
// arrives now (Env_DataRsp).
lsq_ent_t lsq_rsp_ent_q;
logic     lsq_rsp_idx_q;

always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    lsq_rsp_ent_q <= lsq_null;
    lsq_rsp_idx_q <= 1'b0;
  end else if (data_req_o && data_gnt_i) begin
    lsq_rsp_ent_q <= lsq_req_ent;
    lsq_rsp_idx_q <= lsq_req_idx;
  end
end

// CSR instructions: the CSR op is performed in the cycle after csr_go
// (csr_op_en_o = csr_go_q) and is visible in cs_registers two cycles after
// csr_go.
lsq_ent_t csr_ent1_q, csr_ent2_q;
logic     csr_chk1_q, csr_chk2_q;

always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    csr_chk1_q <= 1'b0;
    csr_chk2_q <= 1'b0;
    csr_ent1_q <= lsq_null;
    csr_ent2_q <= lsq_null;
  end else begin
    csr_chk1_q <= `KLSU.csr_go & lsq_head.valid & ~lsq_head.shadow & ~lsq_head.trap;
    csr_chk2_q <= csr_chk1_q;
    if (`KLSU.csr_go) csr_ent1_q <= lsq_head;
    csr_ent2_q <= csr_ent1_q;
  end
end
