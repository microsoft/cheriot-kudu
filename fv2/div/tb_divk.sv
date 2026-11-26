// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Lemma K of Env_DivLemma (check/spec_instance.sv), checked by simulation:
// whenever multdiv32 is in MD_FINISH with operator_q in {DIV, REM} and the
// latched signed mode 00 or 11, imd_val_q[0][31:0] is the RISC-V M result of
// (op_a_q, op_b_q). Stimulus is unconstrained around the divides: random
// idle gaps, flushes (also mid-divide), input changes while busy, mult
// enables, data_ind_timing and MULL/MULH operators on div_en.

module tb_divk;
  import super_pkg::*;

  logic        clk = 1'b0, rst_n = 1'b0;
  logic        flush, mult_en, div_en, dit;
  md_op_e      op;
  logic [1:0]  sm;
  logic [31:0] a, b;
  logic [31:0] mult_res, div_res;
  logic        mult_v, div_v;

  multdiv32 #(.UseDWMult(1'b0)) dut (
    .clk_i(clk), .rst_ni(rst_n), .flush_i(flush), .mult_en_i(mult_en), .div_en_i(div_en),
    .operator_i(op), .signed_mode_i(sm), .op_a_i(a), .op_b_i(b), .data_ind_timing_i(dit),
    .mult_result_o(mult_res), .div_result_o(div_res), .mult_valid_o(mult_v), .div_valid_o(div_v));

  // Mirror of the signed-mode latch (kdiv_sm_q in spec_instance.sv), and of
  // data_ind_timing at the start of the divide (statistics only).
  logic [1:0] sm_q;
  logic       dit_q;
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) begin
      sm_q  <= 2'b00;
      dit_q <= 1'b0;
    end else if (dut.md_state_q == 3'd0) begin
      sm_q  <= sm;
      dit_q <= dit;
    end

  function automatic logic [31:0] ref_div(input md_op_e o, input logic [1:0] s,
                                          input logic [31:0] x, input logic [31:0] y);
    logic signed [31:0] sx, sy;
    sx = x; sy = y;
    if (o == MD_OP_DIV) begin
      if (y == 0) return 32'hffff_ffff;
      if (s == 2'b11 && x == 32'h8000_0000 && y == 32'hffff_ffff) return 32'h8000_0000;
      return (s == 2'b11) ? 32'(sx / sy) : x / y;
    end else begin
      if (y == 0) return x;
      if (s == 2'b11 && x == 32'h8000_0000 && y == 32'hffff_ffff) return 32'h0;
      return (s == 2'b11) ? 32'(sx % sy) : x % y;
    end
  endfunction

  function automatic logic [31:0] pick();
    unique case ($urandom_range(0, 9))
      0: return 32'h0;
      1: return 32'h1;
      2: return 32'hffff_ffff;
      3: return 32'h8000_0000;
      4: return 32'h7fff_ffff;
      5: return (32'h1 << $urandom_range(0, 31)) + 32'($urandom_range(0, 2)) - 32'h1;
      6: return 32'($urandom_range(0, 15));
      7: return -32'($urandom_range(0, 15));
      default: return $urandom;
    endcase
  endfunction

  longint unsigned n_chk = 0, n_err = 0, n_sm0 = 0, n_sm3 = 0, n_div = 0, n_rem = 0;
  longint unsigned n_dz = 0, n_dit = 0, n_ovf = 0;
  longint unsigned n_target;

  always @(posedge clk) if (rst_n) begin
    if (div_v != (dut.md_state_q == 3'd6 && !flush)) begin
      n_err++;
      $display("ERROR div_valid_o=%0b in state %0d", div_v, dut.md_state_q);
    end
    if (dut.md_state_q == 3'd6 && (dut.operator_q == MD_OP_DIV || dut.operator_q == MD_OP_REM) &&
        (sm_q == 2'b00 || sm_q == 2'b11)) begin
      logic [31:0] exp;
      exp = ref_div(dut.operator_q, sm_q, dut.op_a_q, dut.op_b_q);
      n_chk++;
      if (sm_q == 2'b00) n_sm0++; else n_sm3++;
      if (dut.operator_q == MD_OP_DIV) n_div++; else n_rem++;
      if (dut.op_b_q == 0) n_dz++;
      if (dut.op_a_q == 32'h8000_0000 && dut.op_b_q == 32'hffff_ffff) n_ovf++;
      if (dit_q) n_dit++;
      if (dut.imd_val_q[0][31:0] !== exp || div_res !== exp) begin
        n_err++;
        if (n_err < 20)
          $display("ERROR op=%0d sm=%b a=%h b=%h dut=%h exp=%h", dut.operator_q, sm_q,
                   dut.op_a_q, dut.op_b_q, dut.imd_val_q[0][31:0], exp);
      end
    end
  end

  always #5 clk = ~clk;

  initial begin
    if (!$value$plusargs("N=%d", n_target)) n_target = 200000;
    flush = 0; mult_en = 0; div_en = 0; dit = 0; op = MD_OP_MULL; sm = 0; a = 0; b = 0;
    repeat (3) @(negedge clk);
    rst_n = 1'b1;
    while (n_chk < n_target) begin
      @(negedge clk);
      // Inputs change every cycle, also while the divider is busy.
      a       = pick();
      b       = pick();
      sm      = ($urandom_range(0, 7) == 0) ? 2'($urandom) : ($urandom_range(0, 1) ? 2'b11 : 2'b00);
      op      = ($urandom_range(0, 9) == 0) ? md_op_e'($urandom_range(0, 1))
                                            : ($urandom_range(0, 1) ? MD_OP_DIV : MD_OP_REM);
      dit     = ($urandom_range(0, 3) == 0);
      mult_en = 1'($urandom_range(0, 1));
      div_en  = (dut.md_state_q == 3'd0) ? ($urandom_range(0, 2) != 0) : 1'($urandom_range(0, 1));
      flush   = ($urandom_range(0, 199) == 0);
    end
    $display("DIVK checks=%0d errors=%0d sm00=%0d sm11=%0d div=%0d rem=%0d b0=%0d ovf=%0d dit=%0d",
             n_chk, n_err, n_sm0, n_sm3, n_div, n_rem, n_dz, n_ovf, n_dit);
    if (n_err == 0) $display("DIVK_RESULT: PASS");
    else             $display("DIVK_RESULT: FAIL");
    $finish;
  end
endmodule
