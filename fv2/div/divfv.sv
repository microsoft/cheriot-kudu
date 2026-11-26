// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Block-level formal proof of the K half of Env_DivLemma (README 4.4):
// multdiv32 (UseDWMult = 0) at MD_FINISH holds the RISC-V M DIV/DIVU/REM/REMU
// result of the operands, operator and signed mode it latched while MD_IDLE.
// Every multdiv32 input is free (flush, enables, operator, signed mode,
// operands and data_ind_timing may change in any cycle).
//
// The reference is f_rdiv: RISC-V special cases (zero divisor, signs) around
// f_udiv, a textbook restoring divider written as a plain loop (and, for the
// proof, unrolled into the wire chain pc). That f_udiv equals unsigned / and
// % is a separate, purely mathematical lemma proved in div/udiv_z3.py. The
// helper invariants tie each FSM state to a link of the chain, so the whole
// set is inductive (joint k-induction in div/divfv.tcl).
//
// The chain is fed from frozen symbolic operands fa, fb, fsm (registers that
// never change, arbitrary initial value), and every chain property is guarded
// by "the latched operands are fa, fb, fsm". Proving that for all fa, fb, fsm
// is the same as proving it for the latched operands (instantiate fa := op_a_q
// etc.), but in the induction step both time frames then share one reference
// circuit. Fed from op_a_q directly, each frame got its own 32-step divider
// and the solver had to prove two copies equal, which does not finish.

module divfv_top (
  input  logic              clk_i,
  input  logic              rst_ni,
  input  logic              flush_i,
  input  logic              mult_en_i,
  input  logic              div_en_i,
  input  super_pkg::md_op_e operator_i,
  input  logic [1:0]        signed_mode_i,
  input  logic [31:0]       op_a_i,
  input  logic [31:0]       op_b_i,
  input  logic              data_ind_timing_i
);
  import super_pkg::*;

  logic [31:0] mult_result_o, div_result_o;
  logic        mult_valid_o, div_valid_o;

  multdiv32 #(.UseDWMult(1'b0)) dut (.*);

  // One restoring step at quotient bit i on {Q, R} (R 33 bits): subtract the
  // divisor and set Q[i] when R >= D.
  function automatic logic [64:0] f_step(logic [64:0] qr, logic [31:0] d, int i);
    logic [32:0] r;
    logic [31:0] q;
    q = qr[64:33];
    r = qr[32:0];
    if (r >= {1'b0, d}) begin
      r    = r - {1'b0, d};
      q[i] = 1'b1;
    end
    return {q, r};
  endfunction

  // {Q, R} of the restoring loop: R starts as N[31]; for each quotient bit
  // i = 31 .. 0, step, then (i > 0) shift N[i-1] into R.
  function automatic logic [63:0] f_udiv(logic [31:0] n, logic [31:0] d);
    logic [64:0] qr;
    qr = {32'h0, 32'h0, n[31]};
    for (int i = 31; i >= 0; i--) begin
      qr = f_step(qr, d, i);
      if (i > 0) qr = {qr[64:33], qr[31:0], n[i-1]};
    end
    return {qr[64:33], qr[31:0]};
  endfunction

  function automatic logic [31:0] f_abs(logic [31:0] x, logic neg);
    return neg ? 32'(-x) : x;
  endfunction

  // RISC-V M: DIV(U) by zero = all ones, REM(U) by zero = dividend; signed
  // quotient truncates toward zero, remainder takes the dividend's sign
  // (INT_MIN / -1 = INT_MIN, rem 0, falls out of the unsigned core).
  // f_rwrap takes the operand signs and the unsigned {Q, R} of |a|, |b|, so
  // Div_Result can reuse the harness's single f_udiv instance (uqr).
  function automatic logic [31:0] f_rwrap(logic [31:0] a, logic [31:0] b, logic is_rem,
                                          logic sa, logic sb, logic [63:0] qr);
    if (b == 32'h0)  return is_rem ? a : 32'hffff_ffff;
    else if (is_rem) return f_abs(qr[31:0], sa);
    else             return f_abs(qr[63:32], sa ^ sb);
  endfunction

  function automatic logic [31:0] f_rdiv(logic [31:0] a, logic [31:0] b, logic is_rem, logic sgn);
    logic sa, sb;
    sa = sgn & a[31];
    sb = sgn & b[31];
    return f_rwrap(a, b, is_rem, sa, sb, f_udiv(f_abs(a, sa), f_abs(b, sb)));
  endfunction

  // Mirror of the signed mode multdiv32 latches while MD_IDLE (it keeps only
  // div_sign_a/b); same as kdiv_sm_q in check/spec_instance.sv.
  logic [1:0] sm_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)                         sm_q <= 2'b00;
    else if (dut.md_state_q == 3'd0)     sm_q <= signed_mode_i;
  end

  // Shorthands for the latched operation.
  logic        is_div, sa, sb;
  logic [31:0] num, den;
  assign is_div = (dut.operator_q == MD_OP_DIV);
  assign sa     = dut.op_a_q[31] & sm_q[0];
  assign sb     = dut.op_b_q[31] & sm_q[1];
  assign num    = f_abs(dut.op_a_q, sa);
  assign den    = f_abs(dut.op_b_q, sb);

  // Frozen symbolic operands (see header). DIVSIM (simulation only) ties them
  // to the latched operands instead, so every guard holds.
  logic [31:0] fa, fb;
  logic [1:0]  fsm;
`ifdef DIVSIM
  assign fa  = dut.op_a_q;
  assign fb  = dut.op_b_q;
  assign fsm = sm_q;
`else
  always_ff @(posedge clk_i) begin
    fa  <= fa;
    fb  <= fb;
    fsm <= fsm;
  end
`endif
  logic        fm, fsa, fsb;
  logic [31:0] fnum, fden;
  logic [63:0] uqr;
  assign fm   = (dut.op_a_q == fa) && (dut.op_b_q == fb) && (sm_q == fsm);
  assign fsa  = fa[31] & fsm[0];
  assign fsb  = fb[31] & fsm[1];
  assign fnum = f_abs(fa, fsa);
  assign fden = f_abs(fb, fsb);

  // f_udiv(fnum, fden) unrolled into a chain of wires: pc[k] is {Q, R} on entry
  // to MD_COMP (k = 31..1) or MD_LAST (k = 0), i.e. after quotient bits
  // 31 .. k+1 with N[k] shifted into R. Each link is one step of the previous
  // one, so every per-counter step check below is local (Ref_Chain checks the
  // chain against the loop).
  logic [64:0] pc [32];
  logic [64:0] plast;
  assign pc[31] = {32'h0, 32'h0, fnum[31]};
  for (genvar k = 30; k >= 0; k--) begin : g_pc
    logic [64:0] t;
    assign t     = f_step(pc[k+1], fden, k + 1);
    assign pc[k] = {t[64:33], t[31:0], fnum[k]};
  end
  assign plast = f_step(pc[0], fden, 0);
  assign uqr   = {plast[64:33], plast[31:0]};

  logic [2:0] st;
  assign st = dut.md_state_q;

  ////////////////////////////// Target //////////////////////////////
  // Exactly the K half of Env_DivLemma: the E2E premise fixes operator_q to
  // DIV/REM and the signed mode to 00/11. With fsm[0] == fsm[1], fsa/fsb/uqr
  // are f_rdiv's own signs and divide, so the right-hand side is
  // f_rdiv(op_a_q, op_b_q, operator_q == REM, sm_q[0]) once fa, fb, fsm are
  // instantiated to op_a_q, op_b_q, sm_q.
  Div_Result: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (st == 3'd6) && fm && (dut.operator_q inside {MD_OP_DIV, MD_OP_REM}) && (fsm inside {2'b00, 2'b11})
    |-> dut.imd_val_q[0][31:0] == f_rwrap(fa, fb, !is_div, fsa, fsb, uqr));

  Div_Valid: assert property (@(posedge clk_i) disable iff (!rst_ni)
    div_valid_o == ((st == 3'd6) && !flush_i));

  Ref_Chain: assert property (@(posedge clk_i) uqr == f_udiv(fnum, fden));

  ////////////////////////////// Helpers //////////////////////////////
  `define DIVH(name, expr) name: assert property (@(posedge clk_i) disable iff (!rst_ni) expr);

  `DIVH(H_State,    st <= 3'd6)
  `DIVH(H_SignA,    dut.div_sign_a == sa)
  `DIVH(H_SignB,    dut.div_sign_b == sb)
  `DIVH(H_DenHi,    dut.imd_val_q[1][33:32] == 2'b00)
  `DIVH(H_ByZero,   (st != 3'd0) && is_div |-> dut.div_by_zero_q == (dut.op_b_q == 32'h0))
  `DIVH(H_AbsA,     (st == 3'd1) && is_div  |-> dut.imd_val_q[0] == '1)
  `DIVH(H_AbsARem,  (st == 3'd1) && !is_div |-> dut.imd_val_q[0] == {2'b00, dut.op_a_q})
  `DIVH(H_Num,      (st inside {3'd2, 3'd3, 3'd4}) |-> dut.op_numerator_q == num)
  `DIVH(H_Den,      (st inside {3'd3, 3'd4}) |-> dut.op_denominator_q == den)
  `DIVH(H_CntComp,  (st == 3'd3) |-> dut.div_counter_q != 5'd0)
  `DIVH(H_CntLast,  (st == 3'd4) |-> dut.div_counter_q == 5'd0)
  // Remainder before the shift is below the divisor, so the shifted 33-bit
  // remainder only loses bit 32 when it is >= the divisor anyway, and
  // multdiv32's 32-bit compare agrees with the reference's 33-bit one.
  `DIVH(H_RemLtD,   (st inside {3'd3, 3'd4}) && (den != 32'h0) |-> dut.imd_val_q[0][32:1] < den)
  `DIVH(H_Chg,      (st == 3'd5) && fm |-> dut.imd_val_q[0] == {2'b00, is_div ? uqr[63:32] : uqr[31:0]})
  // At MD_FINISH for any latched operator/mode (not only DIV/REM, 00/11), so
  // the step does not depend on the target's premise.
  `DIVH(H_Fin,      (st == 3'd6) && fm && is_div && (dut.op_b_q == 32'h0) |-> dut.imd_val_q[0][31:0] == '1)
  `DIVH(H_FinRem,   (st == 3'd6) && fm && !is_div && (dut.op_b_q == 32'h0) |-> dut.imd_val_q[0][31:0] == dut.op_a_q)
  `DIVH(H_FinQ,     (st == 3'd6) && fm && is_div && (dut.op_b_q != 32'h0) |->
                    dut.imd_val_q[0][31:0] == f_abs(uqr[63:32], fsa ^ fsb))
  `DIVH(H_FinR,     (st == 3'd6) && fm && !is_div && (dut.op_b_q != 32'h0) |->
                    dut.imd_val_q[0][31:0] == f_abs(uqr[31:0], fsa))

  // Quotient and remainder in MD_COMP/MD_LAST, split per counter value so each
  // step instance has a constant loop prefix (one check over a variable
  // counter does not finish).
  for (genvar k = 0; k < 32; k++) begin : g_k
    logic [64:0] pk;
    assign pk = pc[k];
    `DIVH(H_QuotK, (st inside {3'd3, 3'd4}) && fm && (dut.div_counter_q == 5'(k)) |->
                   dut.op_quotient_q == pk[64:33])
    `DIVH(H_RemK,  (st inside {3'd3, 3'd4}) && fm && (dut.div_counter_q == 5'(k)) |->
                   dut.imd_val_q[0] == {1'b0, pk[32:0]})
  end

  // Reachability.
  C_FinDiv:  cover property (@(posedge clk_i) disable iff (!rst_ni) st == 3'd6 && fm && is_div && dut.op_b_q != 0 && sm_q == 2'b11);
  C_FinRemU: cover property (@(posedge clk_i) disable iff (!rst_ni) st == 3'd6 && fm && !is_div && dut.op_b_q != 0 && sm_q == 2'b00);
`ifndef DIVSIM
  // Second division in a trace still matches the frozen operands (fa is not
  // pinned to the first one).
  C_FinTwo:  cover property (@(posedge clk_i) disable iff (!rst_ni)
    (st == 3'd6) && !fm ##[1:$] (st == 3'd6) && fm && is_div && dut.op_b_q != 0);
`endif
endmodule
