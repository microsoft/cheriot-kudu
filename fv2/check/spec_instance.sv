// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Two chained spec instances evaluated at issue (README sections 4.1, 4.2).
// Included inside kudu_e2e_top after abs.sv.
//
//   spec0: the instruction in IR slot 0 (time-ordered ir0_dec), evaluated at
//          - CSM_DECODE when ir0 is normally issued,
//          - CSM_ISSUE_SPECIAL for a SYSCTL, an issue-time exception (EXEC),
//            an interrupt (IRQ) or an AMO (CMPLX, cmplx_unit start).
//   spec1: ir1_dec when it is dual-issued; its pre-state is spec0's
//          post-state.
//
// Pre-state:
//   - GPRs read by the instruction come from the operands Kudu forwards to
//     the pipelines (ira/irb_full_data2_fwd). Unread GPRs are free inputs.
//   - PC/PCC/CSRs/privilege come from spec_past_*, the post-state of the
//     latest non-shadow step. Before the first step they come from the DUT
//     (abs.sv).
//
// Trap shadow: a step that traps without Kudu entering the handler in the
// same cycle (an LS fault, reported later through cmt_err) puts every younger
// step in its shadow until cmt_flush. Shadow steps are not checked and do not
// update spec_past_*. A trap that Kudu fails to take is caught by Cmt_Trap or
// Local_NoTrap (checks.sv).

////////////////////// Step conditions //////////////////////

logic st_decode, st_special;
super_pkg::special_case_e sp_case;

assign st_decode  = `KISS.ctrl_fsm_cs[super_pkg::CSM_DECODE];
assign st_special = `KISS.ctrl_fsm_cs[super_pkg::CSM_ISSUE_SPECIAL];
assign sp_case    = `KISS.special_case_q;

logic s0_normal, s0_sysctl, s0_exec, s0_irq, s0_cmplx, s0_step, s1_step;

assign s0_normal = st_decode & `KISS.ir0_normal_issued;
assign s0_sysctl = st_special & (sp_case == super_pkg::SYSCTL);
assign s0_exec   = st_special & (sp_case == super_pkg::EXEC);
assign s0_irq    = st_special & (sp_case == super_pkg::IRQ);
assign s0_cmplx  = st_special & (sp_case == super_pkg::CMPLX);
assign s0_step   = s0_normal | s0_sysctl | s0_exec | s0_irq | s0_cmplx;
assign s1_step   = `KISS.ir1_issued;

super_pkg::ir_dec_t     s0_dec, s1_dec;
super_pkg::full_data2_t s0_op, s1_op;

assign s0_dec = `KISS.ir0_dec;
assign s1_dec = `KISS.ir1_dec;
assign s0_op  = `KDUT.ira_is0 ? `KDUT.ira_full_data2_fwd : `KDUT.irb_full_data2_fwd;
assign s1_op  = `KDUT.ira_is0 ? `KDUT.irb_full_data2_fwd : `KDUT.ira_full_data2_fwd;

t_MainMode s0_mode, s1_mode;

always_comb begin
  if (s0_irq)
    s0_mode = MAIN_IRQ;
  else if (s0_exec && (s0_dec.errs.perm_vio || s0_dec.errs.bound_vio || s0_dec.errs.fetch_err))
    s0_mode = MAIN_IFERR;
  else
    s0_mode = MAIN_IDEX;
end

// ir1 is never issued with an error (normal_ex_enable[1]).
assign s1_mode = MAIN_IDEX;

logic [31:0] s0_pc, s0_nextpc, s1_pc, s1_nextpc;
logic [31:0] s0_insn, s1_insn;

assign s0_pc     = s0_irq ? (`KDUT.ir_valid[0] ? s0_dec.pc : `KISS.ir0_nxt_pc_q) : s0_dec.pc;
assign s0_nextpc = s0_irq ? s0_pc : (s0_pc + (s0_dec.is_comp ? 32'd2 : 32'd4));
assign s1_pc     = s1_dec.pc;
assign s1_nextpc = s1_pc + (s1_dec.is_comp ? 32'd2 : 32'd4);
assign s0_insn   = insn_bits_of(s0_dec);
assign s1_insn   = insn_bits_of(s1_dec);

////////////////////// spec_past_* state //////////////////////

logic          past_valid;
logic [31:0]   past_pc;
t_Capability   past_pcc;
t_Privilege    past_priv;
kudu_mstatus_t past_mstatus;
logic [31:0]   past_mie;
logic [31:0]   past_mcause;
logic [31:0]   past_mtval;
logic [31:0]   past_mscratch;
logic [31:0]   past_mshwm;
logic [31:0]   past_mshwmb;
t_Capability   past_mtvec;
t_Capability   past_mepc;
t_Capability   past_mscratchc;
t_Capability   past_mtdc;
logic [31:1]   past_has_reg;
t_Capability   past_regs[31:1];

////////////////////// Shadow //////////////////////

logic shadow_q;
logic s0_shadow, s1_shadow;
logic s0_trap, s1_trap;
logic s0_upd, s1_upd;

assign s0_shadow = shadow_q;
assign s1_shadow = shadow_q | s0_trap;
assign s0_upd    = s0_step & ~s0_shadow;
assign s1_upd    = s1_step & ~s1_shadow;

always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    shadow_q <= 1'b0;
  end else if (`KDUT.cmt_flush) begin
    shadow_q <= 1'b0;
  end else if ((s0_upd & s0_trap & ~(st_special & `KDUT.csr_save_cause)) |
               (s1_upd & s1_trap)) begin
    shadow_q <= 1'b1;
  end
end

////////////////////// GPR pre-state //////////////////////

t_Capability s0_regs[31:1];
t_Capability s1_regs[31:1];
logic [31:1] s0_rd0, s0_rd1, s1_rd0, s1_rd1;

for (genvar i = 1; i < 32; i++) begin : g_regs
  assign s0_rd0[i] = ~s0_irq & s0_dec.rf_ren[0] & (s0_dec.rs1 == i);
  assign s0_rd1[i] = ~s0_irq & s0_dec.rf_ren[1] & (s0_dec.rs2 == i);
  assign s1_rd0[i] = s1_dec.rf_ren[0] & (s1_dec.rs1 == i);
  assign s1_rd1[i] = s1_dec.rf_ren[1] & (s1_dec.rs2 == i);

  assign s0_regs[i] = s0_rd0[i] ? op2sail(s0_op.d0) :
                      s0_rd1[i] ? op2sail(s0_op.d1) :
                      capBitsToCapability(spec0_free_regs_i[i][64], spec0_free_regs_i[i][63:0]);
  assign s1_regs[i] = s1_rd0[i] ? op2sail(s1_op.d0) :
                      s1_rd1[i] ? op2sail(s1_op.d1) :
                      capBitsToCapability(spec1_free_regs_i[i][64], spec1_free_regs_i[i][63:0]);
end

////////////////////// CSR/PC pre-state //////////////////////

t_Capability   s0_pre_pcc;
t_Privilege    s0_pre_priv;
kudu_mstatus_t s0_pre_mstatus;
logic [31:0]   s0_pre_mie, s0_pre_mcause, s0_pre_mtval, s0_pre_mscratch;
logic [31:0]   s0_pre_mshwm, s0_pre_mshwmb;
t_Capability   s0_pre_mtvec, s0_pre_mepc, s0_pre_mscratchc, s0_pre_mtdc;

assign s0_pre_pcc       = past_valid ? past_pcc       : dut_pcc_at(s0_pc);
assign s0_pre_priv      = past_valid ? past_priv      : dut_priv;
assign s0_pre_mstatus   = past_valid ? past_mstatus   : dut_mstatus;
assign s0_pre_mie       = past_valid ? past_mie       : dut_mie;
assign s0_pre_mcause    = past_valid ? past_mcause    : dut_mcause;
assign s0_pre_mtval     = past_valid ? past_mtval     : dut_mtval;
assign s0_pre_mscratch  = past_valid ? past_mscratch  : dut_mscratch;
assign s0_pre_mshwm     = past_valid ? past_mshwm     : dut_mshwm;
assign s0_pre_mshwmb    = past_valid ? past_mshwmb    : dut_mshwmb;
assign s0_pre_mtvec     = past_valid ? past_mtvec     : dut_mtvec;
assign s0_pre_mepc      = past_valid ? past_mepc      : dut_mepc;
assign s0_pre_mscratchc = past_valid ? past_mscratchc : dut_mscratchc;
assign s0_pre_mtdc      = past_valid ? past_mtdc      : dut_mtdc;

////////////////////// Spec instances //////////////////////

// Post-state and side-effect wires of one spec instance.
`define KSPEC_DECL(N) \
  logic          s``N``_int_err; \
  logic          s``N``_mtcc_unrec; \
  logic          s``N``_wx_en; \
  t_Capability   s``N``_wx; \
  logic [4:0]    s``N``_wx_addr; \
  logic [31:0]   s``N``_post_pc; \
  t_Capability   s``N``_post_pcc; \
  t_Privilege    s``N``_post_priv; \
  kudu_mstatus_t s``N``_post_mstatus; \
  logic [31:0]   s``N``_post_mie; \
  logic [31:0]   s``N``_post_mcause; \
  logic [31:0]   s``N``_post_mtval; \
  logic [31:0]   s``N``_post_mscratch; \
  logic [31:0]   s``N``_post_mshwm; \
  logic [31:0]   s``N``_post_mshwmb; \
  t_Capability   s``N``_post_mtvec; \
  t_Capability   s``N``_post_mepc; \
  t_Capability   s``N``_post_mscratchc; \
  t_Capability   s``N``_post_mtdc; \
  logic          s``N``_mem_read; \
  logic          s``N``_mem_read_snd; \
  logic [31:0]   s``N``_mem_read_fst_addr; \
  logic [31:0]   s``N``_mem_read_snd_addr; \
  logic          s``N``_mem_read_cap; \
  logic          s``N``_mem_write; \
  logic          s``N``_mem_write_snd; \
  logic [31:0]   s``N``_mem_write_fst_addr; \
  logic [31:0]   s``N``_mem_write_snd_addr; \
  logic [31:0]   s``N``_mem_write_fst_wdata; \
  logic [31:0]   s``N``_mem_write_snd_wdata; \
  logic [3:0]    s``N``_mem_write_fst_be; \
  logic [3:0]    s``N``_mem_write_snd_be; \
  logic          s``N``_mem_sc; \
  logic [31:0]   s``N``_mem_sc_addr; \
  logic          s``N``_mem_write_tag; \
  logic          s``N``_mem_write_cap;

`KSPEC_DECL(0)
`KSPEC_DECL(1)

`define KSPEC_INST(N, PRE) \
  kudu_spec_api spec``N``_i ( \
    .main_mode            (s``N``_mode), \
    .regs_i               (s``N``_regs), \
    .wx_en_o              (s``N``_wx_en), \
    .wx_o                 (s``N``_wx), \
    .wx_addr_o            (s``N``_wx_addr), \
    .nextpc_i             (s``N``_nextpc), \
    .pc_i                 (s``N``_pc), \
    .pc_o                 (s``N``_post_pc), \
    .misa_i               (dut_misa), \
    .mip_i                (dut_mip), \
    .mvendor_id_i         (csr_pkg::CSR_MVENDORID_CHERI_VALUE), \
    .march_id_i           (csr_pkg::CSR_MARCHID_CHERI_VALUE), \
    .mimp_id_i            (csr_pkg::CSR_MIMPID_VALUE), \
    .mhart_id_i           (hart_id_i), \
    .mconfigptr_i         (32'h0), \
    .mseccfg_i            (32'h0), \
    .mseccfg_o            (), \
    .mie_i                (PRE``_mie), \
    .mie_o                (s``N``_post_mie), \
    .priv_i               (PRE``_priv), \
    .priv_o               (s``N``_post_priv), \
    .mstatus_i            (PRE``_mstatus), \
    .mstatus_o            (s``N``_post_mstatus), \
    .mcause_i             (PRE``_mcause), \
    .mcause_o             (s``N``_post_mcause), \
    .mcycle_i             (64'h0), \
    .mcycle_o             (), \
    .mtval_i              (PRE``_mtval), \
    .mtval_o              (s``N``_post_mtval), \
    .mtvec_i              (PRE``_mtvec), \
    .mtvec_o              (s``N``_post_mtvec), \
    .mscratch_i           (PRE``_mscratch), \
    .mscratch_o           (s``N``_post_mscratch), \
    .mepc_i               (PRE``_mepc), \
    .mepc_o               (s``N``_post_mepc), \
    .mshwmb_i             (PRE``_mshwmb), \
    .mshwmb_o             (s``N``_post_mshwmb), \
    .mshwm_i              (PRE``_mshwm), \
    .mshwm_o              (s``N``_post_mshwm), \
    .mcounteren_i         (32'h0), \
    .mcounteren_o         (), \
    .pcc_i                (PRE``_pcc), \
    .pcc_o                (s``N``_post_pcc), \
    .mscratchc_i          (PRE``_mscratchc), \
    .mscratchc_o          (s``N``_post_mscratchc), \
    .mtdc_i               (PRE``_mtdc), \
    .mtdc_o               (s``N``_post_mtdc), \
    .insn_bits            (s``N``_insn), \
    .int_err_o            (s``N``_int_err), \
    .trap_o               (s``N``_trap), \
    .mtcc_unrec_o         (s``N``_mtcc_unrec), \
    .mem_read_o           (s``N``_mem_read), \
    .mem_read_snd_gran_o  (s``N``_mem_read_snd), \
    .mem_read_fst_addr_o  (s``N``_mem_read_fst_addr), \
    .mem_read_snd_addr_o  (s``N``_mem_read_snd_addr), \
    .mem_read_fst_rdata_i (spec``N``_rd_fst_i), \
    .mem_read_snd_rdata_i (spec``N``_rd_snd_i), \
    .mem_read_tag_i       (spec``N``_rd_tag_i), \
    .mem_read_cap_o       (s``N``_mem_read_cap), \
    .mem_revoke_en_o      (), \
    .mem_revoke_granule_o (), \
    .mem_revoke_i         (1'b0), \
    .mem_sc_o             (s``N``_mem_sc), \
    .mem_sc_addr_o        (s``N``_mem_sc_addr), \
    .mem_sc_ok_i          (spec``N``_sc_ok_i), \
    .mem_write_o          (s``N``_mem_write), \
    .mem_write_snd_gran_o (s``N``_mem_write_snd), \
    .mem_write_fst_addr_o (s``N``_mem_write_fst_addr), \
    .mem_write_snd_addr_o (s``N``_mem_write_snd_addr), \
    .mem_write_fst_wdata_o(s``N``_mem_write_fst_wdata), \
    .mem_write_snd_wdata_o(s``N``_mem_write_snd_wdata), \
    .mem_write_fst_be_o   (s``N``_mem_write_fst_be), \
    .mem_write_snd_be_o   (s``N``_mem_write_snd_be), \
    .mem_write_tag_o      (s``N``_mem_write_tag), \
    .mem_write_cap_o      (s``N``_mem_write_cap) \
  );

`KSPEC_INST(0, s0_pre)
`KSPEC_INST(1, s0_post)

`undef KSPEC_DECL
`undef KSPEC_INST

// Harness restriction (Kudu divergence G, README 1.1): Kudu's PCC keeps only
// decoded bounds, so a trap from an untagged PCC with E>24 leaves a lossy
// MEPCC. A CSpecialRW read of it would expose the lost raw B/T/E in rd and
// propagate it; such reads are excluded.
function automatic logic f_mepc_rd(logic [31:0] insn);
  return (insn[6:0] == 7'h5b) && (insn[14:12] == 3'd0) && (insn[31:25] == 7'h01) &&
         (insn[24:20] == cheri_pkg::CHERI_SCR_MEPCC) && (insn[11:7] != 5'd0);
endfunction
function automatic logic f_divg(t_Capability c);
  return !c.tag && (c.E > 5'd24);
endfunction
// Also excluded: an E = 24 MEPCC whose T[8] is not the canonical B[8] ^ carry ^ 1.
// The spec's main_inner (cheriot-ibex issue #11) clears PCC.B[8] at E = 24, and
// a trap copies that PCC into MEPCC; wC's encode/decode then recomputes T[8]
// from the cleared B[8], changing the top bound. Kudu returns the raw T, which
// gives the same bounds as unmodified Sail (s2tmo1 Cmt_Wr cex).
function automatic logic f_mepc_lossy(t_Capability c);
  return f_divg(c) ||
         ((c.E == 5'd24) && (c.T[8] != (c.B[8] ^ (c.T[7:0] < c.B[7:0]) ^ 1'b1)));
endfunction
Env_NoDivGRd0: assume property (s0_upd && !s0_irq && !s0_trap && f_mepc_rd(s0_dec.insn)
                                |-> !f_mepc_lossy(s0_pre_mepc));
Env_NoDivGRd1: assume property (s1_upd && !s1_trap && f_mepc_rd(s1_dec.insn)
                                |-> !f_mepc_lossy(s0_post_mepc));

////////////////////// Divide lemma (Env_DivLemma) //////////////////////
// Sail's DIV/REM and Kudu's iterative multdiv32 are not compared inside this
// proof (as in the Ibex proof, an inductive divider argument is out of reach).
// When multdiv32 starts a divide, the harness records the Sail operands,
// instruction and result of that divide. Env_DivLemma assumes that when
// multdiv32 reaches MD_FINISH with its latched operands, operator and signed
// mode equal to the recorded ones, its result is the recorded Sail result.
// This is the composition of two lemmas proven outside the e2e harness
// (README 4.4): multdiv32 computes the RISC-V div/rem reference on its
// latched inputs, and Sail's execute_DIV / execute_REM compute that reference.
// Everything else (operand delivery, operator and sign, rd, timing, flush,
// result write-back) stays proven here (Inv_H_Div*, Cmt_Wr).
`define KMD `KDUT.mult_pipeline_i.genblk3.multdiv32_i
function automatic logic f_is_divrem(logic [31:0] insn);
  return (insn[6:0] == 7'h33) && (insn[31:25] == 7'h01) && insn[14];
endfunction
function automatic super_pkg::md_op_e f_div_op(logic [31:0] insn);
  return insn[13] ? super_pkg::MD_OP_REM : super_pkg::MD_OP_DIV;
endfunction
function automatic logic [1:0] f_div_sm(logic [31:0] insn);
  return insn[12] ? 2'b00 : 2'b11;
endfunction
logic        div_start, div_in_s0, div_rec_v, div_rec_ok;
logic [31:0] div_rec_a, div_rec_b, div_rec_res, div_rec_insn;
logic [1:0]  kdiv_sm_q;
assign div_start = `KDUT.mult_pipeline_i.md_div_en && !`KDUT.cmt_flush;
assign div_in_s0 = (`KDUT.multpl_sel_ira == `KDUT.ira_is0);
always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    div_rec_v    <= 1'b0;
    div_rec_ok   <= 1'b0;
    div_rec_a    <= '0;
    div_rec_b    <= '0;
    div_rec_res  <= '0;
    div_rec_insn <= '0;
  end else if (div_start) begin
    div_rec_v <= 1'b1;
    if (div_in_s0) begin
      div_rec_ok   <= s0_upd && !s0_irq && !s0_trap && s0_wx_en && f_is_divrem(s0_dec.insn);
      div_rec_a    <= (s0_dec.rs1 == 5'd0) ? 32'h0 : s0_regs[s0_dec.rs1].address;
      div_rec_b    <= (s0_dec.rs2 == 5'd0) ? 32'h0 : s0_regs[s0_dec.rs2].address;
      div_rec_res  <= s0_wx.address;
      div_rec_insn <= s0_dec.insn;
    end else begin
      div_rec_ok   <= s1_upd && !s1_trap && s1_wx_en && f_is_divrem(s1_dec.insn);
      div_rec_a    <= (s1_dec.rs1 == 5'd0) ? 32'h0 : s1_regs[s1_dec.rs1].address;
      div_rec_b    <= (s1_dec.rs2 == 5'd0) ? 32'h0 : s1_regs[s1_dec.rs2].address;
      div_rec_res  <= s1_wx.address;
      div_rec_insn <= s1_dec.insn;
    end
  end else if (`KDUT.cmt_flush) begin
    div_rec_v  <= 1'b0;
    div_rec_ok <= 1'b0;
  end
end
// Mirrors multdiv32's own latch of signed_mode_i (taken while MD_IDLE), which
// the RTL keeps only as div_sign_a/b.
always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni)                              kdiv_sm_q <= 2'b00;
  else if (`KMD.md_state_q == 3'd0)         kdiv_sm_q <= `KDUT.mult_pipeline_i.md_signed_mode;
end
logic div_lemma_pre;
assign div_lemma_pre = div_rec_ok && (`KMD.md_state_q == 3'd6) &&
                       (`KMD.op_a_q == div_rec_a) && (`KMD.op_b_q == div_rec_b) &&
                       (`KMD.operator_q == f_div_op(div_rec_insn)) &&
                       (kdiv_sm_q == f_div_sm(div_rec_insn));
Env_DivLemma: assume property (div_lemma_pre |-> `KMD.imd_val_q[0][31:0] == div_rec_res);

////////////////////// Multiply lemma (Env_MulLemma) //////////////////////
// Same scheme as Env_DivLemma, for MUL/MULH/MULHSU/MULHU. When multdiv32's
// multiplier is enabled, the harness records the Sail operands, instruction
// and wX result of the issuing step, and mirrors the multiplier's inputs.
// Until the next enable, mult_result_o equals the recorded Sail result if the
// mirrored inputs, operator and signed mode match the recorded ones. This
// composes (K) mult_result_o == RISC-V M result of the inputs at the last
// enable (Conformal LEC kudu_e2e/mullec2_*: Wallace tree == a*b; Jasper
// kudu_e2e/mulpipe_*: pipelined product == $past(a*b), held while !en; the
// MULL/MULH select is mult_op, latched on en), and (S) Sail execute_MUL's wX
// is that result (kudu_e2e/mulnarrow_*: the 256-bit product equals the
// 66-bit signed product of the 33-bit sign/zero-extended operands; wX takes
// bits [31:0] or [63:32]). Without it the solver must equate two different
// multipliers fed through different muxes (MulIss_C[1-4] timed out).
`ifndef E2E_NO_MULLEMMA
function automatic logic f_is_mul(logic [31:0] insn);
  return (insn[6:0] == 7'h33) && (insn[31:25] == 7'h01) && !insn[14];
endfunction
function automatic super_pkg::md_op_e f_mul_op(logic [31:0] insn);
  return (insn[13:12] == 2'd0) ? super_pkg::MD_OP_MULL : super_pkg::MD_OP_MULH;
endfunction
function automatic logic [1:0] f_mul_sm(logic [31:0] insn);
  return (insn[13:12] == 2'd1) ? 2'b11 : (insn[13:12] == 2'd2) ? 2'b01 : 2'b00;
endfunction
logic                mul_rec_ok;
logic [31:0]         mul_rec_a, mul_rec_b, mul_rec_res, mul_rec_insn;
logic [31:0]         kmul_a_q, kmul_b_q;
logic [1:0]          kmul_sm_q;
super_pkg::md_op_e   kmul_op_q;
always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    mul_rec_ok   <= 1'b0;
    mul_rec_a    <= '0;
    mul_rec_b    <= '0;
    mul_rec_res  <= '0;
    mul_rec_insn <= '0;
    kmul_a_q     <= '0;
    kmul_b_q     <= '0;
    kmul_sm_q    <= 2'b00;
    kmul_op_q    <= super_pkg::MD_OP_MULL;
  end else if (`KMD.mult_en_i) begin
    kmul_a_q  <= `KMD.op_a_i;
    kmul_b_q  <= `KMD.op_b_i;
    kmul_sm_q <= `KMD.signed_mode_i;
    kmul_op_q <= `KMD.operator_i;
    if (div_in_s0) begin
      mul_rec_ok   <= s0_upd && !s0_irq && !s0_trap && s0_wx_en && f_is_mul(s0_dec.insn);
      mul_rec_a    <= (s0_dec.rs1 == 5'd0) ? 32'h0 : s0_regs[s0_dec.rs1].address;
      mul_rec_b    <= (s0_dec.rs2 == 5'd0) ? 32'h0 : s0_regs[s0_dec.rs2].address;
      mul_rec_res  <= s0_wx.address;
      mul_rec_insn <= s0_dec.insn;
    end else begin
      mul_rec_ok   <= s1_upd && !s1_trap && s1_wx_en && f_is_mul(s1_dec.insn);
      mul_rec_a    <= (s1_dec.rs1 == 5'd0) ? 32'h0 : s1_regs[s1_dec.rs1].address;
      mul_rec_b    <= (s1_dec.rs2 == 5'd0) ? 32'h0 : s1_regs[s1_dec.rs2].address;
      mul_rec_res  <= s1_wx.address;
      mul_rec_insn <= s1_dec.insn;
    end
  end
end
Env_MulLemma: assume property (mul_rec_ok && (kmul_a_q == mul_rec_a) && (kmul_b_q == mul_rec_b) &&
                               (kmul_op_q == f_mul_op(mul_rec_insn)) &&
                               (kmul_sm_q == f_mul_sm(mul_rec_insn))
                               |-> `KMD.mult_result_o == mul_rec_res);
`endif

////////////////////// spec_past_* update //////////////////////

always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    past_valid     <= 1'b0;
    past_pc        <= '0;
    past_pcc       <= nullCap();
    past_priv      <= Machine;
    past_mstatus   <= '0;
    past_mie       <= '0;
    past_mcause    <= '0;
    past_mtval     <= '0;
    past_mscratch  <= '0;
    past_mshwm     <= '0;
    past_mshwmb    <= '0;
    past_mtvec     <= nullCap();
    past_mepc      <= nullCap();
    past_mscratchc <= nullCap();
    past_mtdc      <= nullCap();
  end else if (s0_upd) begin
    past_valid     <= 1'b1;
    past_pc        <= s1_upd ? s1_post_pc        : s0_post_pc;
    past_pcc       <= s1_upd ? s1_post_pcc       : s0_post_pcc;
    past_priv      <= s1_upd ? s1_post_priv      : s0_post_priv;
    past_mstatus   <= s1_upd ? s1_post_mstatus   : s0_post_mstatus;
    past_mie       <= s1_upd ? s1_post_mie       : s0_post_mie;
    past_mcause    <= s1_upd ? s1_post_mcause    : s0_post_mcause;
    past_mtval     <= s1_upd ? s1_post_mtval     : s0_post_mtval;
    past_mscratch  <= s1_upd ? s1_post_mscratch  : s0_post_mscratch;
    past_mshwm     <= s1_upd ? s1_post_mshwm     : s0_post_mshwm;
    past_mshwmb    <= s1_upd ? s1_post_mshwmb    : s0_post_mshwmb;
    past_mtvec     <= s1_upd ? s1_post_mtvec     : s0_post_mtvec;
    past_mepc      <= s1_upd ? s1_post_mepc      : s0_post_mepc;
    past_mscratchc <= s1_upd ? s1_post_mscratchc : s0_post_mscratchc;
    past_mtdc      <= s1_upd ? s1_post_mtdc      : s0_post_mtdc;
  end
end

// GPR continuity state: the latest spec value written to each register.
// past_has_reg marks registers written by a non-shadow step; others are
// unconstrained.
for (genvar i = 1; i < 32; i++) begin : g_past_regs
  logic s0_wr, s1_wr;
  assign s0_wr = s0_upd & s0_wx_en & (s0_wx_addr == i);
  assign s1_wr = s1_upd & s1_wx_en & (s1_wx_addr == i);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      past_has_reg[i] <= 1'b0;
      past_regs[i]    <= nullCap();
    end else if (s1_wr) begin
      past_has_reg[i] <= 1'b1;
      past_regs[i]    <= s1_wx;
    end else if (s0_wr) begin
      past_has_reg[i] <= 1'b1;
      past_regs[i]    <= s0_wx;
    end
  end
end

// The pre-state of spec1's registers, as seen by the continuity check:
// spec0's write in the same pair, else spec_past_regs.
t_Capability s1_chain_regs[31:1];
logic [31:1] s1_chain_has;

for (genvar i = 1; i < 32; i++) begin : g_chain_regs
  logic s0_wr;
  assign s0_wr            = s0_wx_en & (s0_wx_addr == i);
  assign s1_chain_regs[i] = s0_wr ? s0_wx : past_regs[i];
  assign s1_chain_has[i]  = s0_wr | past_has_reg[i];
end
