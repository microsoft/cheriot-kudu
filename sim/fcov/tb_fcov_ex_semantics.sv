// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module fcov_dummy_rv32_alu;
  logic       cmp_signed = 0;
  logic       is_greater_equal = 0;
  logic [31:0] operand_a = 0;
  logic [31:0] operand_b = 0;
  logic [4:0] shift_amt = 0;
endmodule

module fcov_dummy_multdiv;
  logic div_by_zero_q = 0;
endmodule

module alu_pipeline #(
  parameter string PlName = "alu_fixture",
  parameter bit SingleStage = 1
);
  import cheri_pkg::*;
  import super_pkg::*;

`ifdef CHERIoT
  localparam bit CHERIoTEn = 1;
`else
  localparam bit CHERIoTEn = 0;
`endif

  logic       clk_i = 0;
  logic       rst_ni = 0;
  logic       us_valid_i = 0;
  logic       alupl_rdy_o = 1;
  logic       ds_rdy_i = 1;
  logic       alupl_valid_o = 0;
  logic       flush_i = 0;
  ir_dec_t    instr_i = '0;
  pl_out_t    alupl_output_o = '0;
  alu_op_e    rv32_alu_operator = ALU_ADD;
  op_a_sel_e  rv32_alu_op_a_mux_sel = OP_A_REG_A;
  op_b_sel_e  rv32_alu_op_b_mux_sel = OP_B_REG_B;
  logic       cycle2 = 0;
  logic       instr_2cycle = 0;
  logic       ex1_is_cheri = 0;
  logic       ex2_valid = 0;
  logic       ex2_rdy = 1;
  logic       wb_valid = 0;
  logic       wb_rdy = 1;
  logic       ex2_waw_match = 0;
  logic       wb_waw_match = 0;
  logic       ex2_fwd_valid_q = 0;
  logic       wb_fwd_valid_q = 0;
  logic [4:0] ex2_fwd_rd = 1;
  waw_act_t   waw_act_i = '0;
  logic       debug_mode_i = 0;
  logic       cheri_pmode_i = 0;
  pcc_cap_t   pcc_cap_i = '0;

  fcov_dummy_rv32_alu rv32_alu_i();
  kudu_fcov_alu #(.PlName(PlName), .SingleStage(SingleStage), .CHERIoTEn(CHERIoTEn)) monitor(.*);

  task automatic tick;
    #5 clk_i = 1;
    #5 clk_i = 0;
  endtask

  task automatic pcc_vector(input int n);
    mem_cap_t expected;
    pcc_cap_i = '0;
    expected = '0;
    // Deliberately disagree with the expanded permissions: the inherited
    // compressed permission bits, not a recompression of perms, are sampled.
    pcc_cap_i.perms = '1;
    pcc_cap_i.valid = n[0];
    pcc_cap_i.rsvd = n[1];
    pcc_cap_i.cperms = 6'(n);
    pcc_cap_i.otype = 3'(n);
    expected.valid = n[0];
    expected.rsvd = n[1];
    expected.cperms = 6'(n);
    expected.otype = 3'(n);
    case (n % 10)
      0: begin
        pcc_cap_i.exp = 0; pcc_cap_i.base32 = 0; pcc_cap_i.top33 = 1;
        instr_i.pc = 0;
        expected.cexp = 0; expected.base9 = 0; expected.top8 = 1;
      end
      1: begin
        pcc_cap_i.exp = 0; pcc_cap_i.base32 = 1; pcc_cap_i.top33 = 257;
        instr_i.pc = 1;
        expected.cexp = 31; expected.base9 = 1; expected.top8 = 1;
      end
      2: begin
        pcc_cap_i.exp = 3; pcc_cap_i.base32 = 16; pcc_cap_i.top33 = 1008;
        instr_i.pc = 16;
        expected.cexp = 28; expected.base9 = 2; expected.top8 = 126;
      end
      3: begin
        pcc_cap_i.exp = 3; pcc_cap_i.base32 = 2040; pcc_cap_i.top33 = 3064;
        instr_i.pc = 2040;
        expected.cexp = 28; expected.base9 = 255; expected.top8 = 127;
      end
      4: begin
        pcc_cap_i.exp = 3; pcc_cap_i.base32 = 2048; pcc_cap_i.top33 = 3072;
        instr_i.pc = 2048;
        expected.cexp = 28; expected.base9 = 256; expected.top8 = 128;
      end
      5: begin
        pcc_cap_i.exp = 3; pcc_cap_i.base32 = 2056; pcc_cap_i.top33 = 4080;
        instr_i.pc = 2056;
        expected.cexp = 28; expected.base9 = 257; expected.top8 = 254;
      end
      6: begin
        // Wrapped, denormal length one needs cursor-derived correction bits.
        pcc_cap_i.exp = 0; pcc_cap_i.base32 = 511; pcc_cap_i.top33 = 512;
        instr_i.pc = 512;
        expected.cexp = 0; expected.base9 = 511; expected.top8 = 0;
      end
      7: begin
        pcc_cap_i.exp = 24; pcc_cap_i.base32 = 0; pcc_cap_i.top33 = 33'h1_0000_0000;
        instr_i.pc = 32'h8000_0000;
        expected.cexp = 7; expected.base9 = 0; expected.top8 = 0;
      end
      8: begin
        pcc_cap_i.exp = 0; pcc_cap_i.base32 = 511; pcc_cap_i.top33 = 767;
        instr_i.pc = 512;
        expected.cexp = 31; expected.base9 = 511; expected.top8 = 255;
      end
      9: begin
        // Source conversion must not clear a tag for an unrepresentable cursor.
        pcc_cap_i.exp = 0; pcc_cap_i.base32 = 0; pcc_cap_i.top33 = 1;
        instr_i.pc = 32'h1000;
        expected.cexp = 0; expected.base9 = 0; expected.top8 = 1;
      end
    endcase
    expected.addr = instr_i.pc;
    #1;
    if (monitor.auipcc_pcc !== expected)
      $fatal(1, "%s PCC conversion vector %0d: got %h expected %h",
             PlName, n, monitor.auipcc_pcc, expected);
  endtask

  task automatic exercise_auipcc;
    rv32_alu_operator = ALU_ADD;
    instr_i = '0;
    instr_i.cheri_op.auipcc = 1;
    ex1_is_cheri = 1;
    us_valid_i = 1;
    cheri_pmode_i = 1;
    for (int n = 0; n < 64; n++) begin
      pcc_vector(n);
      tick();
    end
    cheri_pmode_i = 0; tick(); cheri_pmode_i = 1;
    alupl_rdy_o = 0; tick(); alupl_rdy_o = 1;
    flush_i = 1; tick(); flush_i = 0;
    us_valid_i = 0; tick(); us_valid_i = 1;
    instr_i.cheri_op = '0; tick();  // Ordinary AUIPC decode, not AUIPCC.
    instr_i.cheri_op.auicgp = 1; tick();
    instr_i.cheri_op = '0; instr_i.is_jal = 1; tick();
    instr_i.is_jal = 0; instr_i.cheri_op.auipcc = 1;
    rst_ni = 0; tick(); rst_ni = 1;
    us_valid_i = 0;
  endtask

  task automatic sample_shift(input alu_op_e op, input bit imm, input logic [4:0] shamt,
                              input logic [31:0] operand_a);
    rv32_alu_operator = op;
    rv32_alu_op_b_mux_sel = imm ? OP_B_IMM : OP_B_REG_B;
    rv32_alu_i.shift_amt = shamt;
    rv32_alu_i.operand_a = operand_a;
    us_valid_i = 1;
    tick();
    us_valid_i = 0;
    tick();
  endtask

  task automatic exercise;
    tick();
    rst_ni = 1;
    sample_shift(ALU_SLL, 0, 5'd0, 32'h0000_0001);
    sample_shift(ALU_SRL, 1, 5'd1, 32'h8000_0000);
    sample_shift(ALU_SRA, 0, 5'd31, 32'h8000_0000);
    sample_shift(ALU_ROL, 0, 5'd7, 32'h0000_0011);
    sample_shift(ALU_ROR, 1, 5'd12, 32'h0000_0022);
    for (int n = 0; n < 8; n++) begin
      {flush_i, wb_valid, ex2_valid} = 3'(n);
      wb_fwd_valid_q = n[0];
      ex2_fwd_valid_q = n[1];
      tick();
    end
    flush_i = 0;
    wb_valid = 0;
    ex2_valid = 0;
    wb_fwd_valid_q = 0;
    ex2_fwd_valid_q = 0;
    exercise_auipcc();
  endtask
endmodule

module mult_pipeline;
  import cheri_pkg::*;
  import super_pkg::*;

`ifdef CHERIoT
  localparam bit CHERIoTEn = 1;
`else
  localparam bit CHERIoTEn = 0;
`endif

  typedef struct packed {
    logic is_cjalr;
    logic is_mult;
    logic is_div;
  } fcov_flags_t;

  typedef struct packed {
    fcov_flags_t flags;
    cheri_op_t   cheri_op;
  } fcov_ex2_reg_t;

  logic       clk_i = 0;
  logic       rst_ni = 0;
  logic       us_valid_i = 0;
  logic       multpl_rdy_o = 1;
  logic       ds_rdy_i = 1;
  logic       multpl_valid_o = 0;
  logic       flush_i = 0;
  logic       sel_ira_i = 1;
  cpu_ctrl_t  cpu_ctrl_i = '0;
  pl_out_t    multpl_output_o = '0;
  md_op_e     md_operator = MD_OP_MULL;
  logic [1:0] md_signed_mode = 2'b00;
  logic       md_mult_en = 0;
  logic       md_div_en = 0;
  logic       md_mult_valid = 0;
  logic       md_div_valid = 0;
  logic       mult_sel = 0;
  logic       div_sel = 0;
  logic       is_mult = 0;
  logic       is_div = 0;
  logic       div_done_q = 0;
  logic       op_done = 0;
  logic       ex1_is_cjalr = 0;
  logic [1:0] mis_jalr_i = 0;
  logic       cjalr_pcc_set_o = 0;
  logic       cjalr_set_mie_o = 0;
  logic       cjalr_clr_mie_o = 0;
  logic       ex2_valid = 0;
  logic       ex2_rdy = 1;
  logic       wb_valid = 0;
  logic       wb_rdy = 1;
  logic       ex2_err = 0;
  logic [5:0] ex2_err_type = 0;
  logic       ex2_waw_match = 0;
  logic       wb_waw_match = 0;
  waw_act_t   waw_act_i = '0;
  ir_dec_t    ira_dec_i = '0;
  ir_dec_t    irb_dec_i = '0;
  ir_dec_t    instr_dec = '0;

  logic       cheri_pmode_i = 0;
  logic [31:0] md_op_a = 0;
  logic [31:0] md_op_b = 0;
  setbounds_req_t setbounds_req_q = '0;
  full_cap_t      ex1_tfcap_q = '0;
  logic           req_exact_q = 0;
  setbounds_out_t ex2_bounds = '0;
  fcov_ex2_reg_t  ex2_reg = '0;

  fcov_dummy_multdiv multdiv32_i();
  kudu_fcov_mult #(.CHERIoTEn(CHERIoTEn)) monitor(.*);

  task automatic tick;
    #5 clk_i = 1;
    #5 clk_i = 0;
  endtask

  function automatic full_cap_t cap(input logic valid, input logic [2:0] otype,
                                    input logic [31:0] base, input logic [32:0] top,
                                    input logic [31:0] addr);
    full_cap_t c;
    c = NULL_FULL_CAP;
    c.valid = valid;
    c.otype = otype;
    c.base32 = base;
    c.top33 = top;
    c.addr = addr;
    c.perms = '1;
    return c;
  endfunction

  task automatic accept_div(input md_op_e op, input logic [1:0] sign,
                            input logic [31:0] a, input logic [31:0] b);
    md_operator = op;
    md_signed_mode = sign;
    md_op_a = a;
    md_op_b = b;
    md_div_en = 1;
    div_sel = 1;
    tick();
    md_div_en = 0;
    div_sel = 0;
    multdiv32_i.div_by_zero_q = (b == 32'h0);
    md_div_valid = 1;
    div_done_q = 1;
    tick();
    md_div_valid = 0;
    div_done_q = 0;
    multdiv32_i.div_by_zero_q = 0;
  endtask

  task automatic accept_mulh(input logic [1:0] sign, input logic [31:0] a,
                             input logic [31:0] b);
    md_operator = MD_OP_MULH;
    md_signed_mode = sign;
    md_op_a = a;
    md_op_b = b;
    md_mult_en = 1;
    mult_sel = 1;
    tick();
    md_mult_en = 0;
    mult_sel = 0;
    md_mult_valid = 1;
    tick();
    md_mult_valid = 0;
    repeat (2) tick();
  endtask

  task automatic save_cheri_mode(input bit mode);
    cheri_pmode_i = mode;
    ex2_rdy = 1;
    tick();
    ex2_rdy = 0;
  endtask

  task automatic sample_setbounds(input cheri_op_t op, input full_cap_t c,
                                  input setbounds_req_t req, input bit exact,
                                  input bit rndn);
    ex1_tfcap_q = c;
    setbounds_req_q = req;
    req_exact_q = exact;
    ex2_bounds = rndn ? set_bounds_rndn(c, req) : set_bounds(c, req, exact);
    ex2_reg.cheri_op = op;
    ex2_valid = 1;
    op_done = 1;
    tick();
    ex2_valid = 0;
    op_done = 0;
    ex2_reg = '0;
    tick();
  endtask

  task automatic exercise_setbounds;
    cheri_op_t op;
    full_cap_t c;
    setbounds_req_t req;

    op = '0;
    op.csetbounds = 1;
    c = cap(1, OTYPE_UNSEALED, 32'h0, 33'h1_0000_0000, 32'h1000);
    req = prep_bound_req(c, 32'h40);
    save_cheri_mode(0);
    sample_setbounds(op, c, req, 0, 0);

    if (CHERIoTEn) begin
      save_cheri_mode(1);
      sample_setbounds(op, c, req, 0, 0);

      op = '0;
      op.csetboundsex = 1;
      c = cap(1, OTYPE_UNSEALED, 32'h0, 33'h1_0000_0000, 32'h1003);
      req = prep_bound_req(c, 32'h400);
      sample_setbounds(op, c, req, 1, 0);

      op = '0;
      op.csetboundsimm = 1;
      c = cap(1, OTYPE_UNSEALED, 32'h0, 33'h100, 32'h80);
      req = prep_bound_req(c, 32'h200);
      sample_setbounds(op, c, req, 0, 0);

      op = '0;
      op.csetboundsrndn = 1;
      c = cap(1, OTYPE_UNSEALED, 32'h0, 33'h1_0000_0000, 32'h4);
      req = prep_bound_req(c, 32'h10000);
      sample_setbounds(op, c, req, 0, 1);

      op = '0;
      op.csetbounds = 1;
      c = cap(0, OTYPE_UNSEALED, 32'h0, 33'h1_0000_0000, 32'h0);
      req = prep_bound_req(c, 32'h10);
      sample_setbounds(op, c, req, 0, 0);

      c = cap(1, OTYPE_SENTRY, 32'h0, 33'h1_0000_0000, 32'h0);
      req = prep_bound_req(c, 32'h10);
      sample_setbounds(op, c, req, 0, 0);

      c = cap(1, OTYPE_UNSEALED, 32'h0, 33'h1_0000_0000, 32'h0);
      req = prep_bound_req(c, 32'h10);
      req.exp1 = 5'd0;
      req.exp2 = 5'd1;
      req.top33req = 33'd600;
      sample_setbounds(op, c, req, 0, 0);
    end
  endtask

  // Sets the EX2 occupant (ex2_reg) or the EX1 candidate (us side) class.
  task automatic set_ex2_class(input int cls);
    ex2_reg = '0;
    case (cls)
      0: ex2_reg.flags.is_mult = 1;
      1: ex2_reg.flags.is_div = 1;
      2: ex2_reg.cheri_op.csetbounds = 1;
      3: ex2_reg.flags.is_cjalr = 1;
    endcase
  endtask

  task automatic set_us_class(input int cls);
    mult_sel = 0; div_sel = 0; ex1_is_cjalr = 0; instr_dec = '0;
    case (cls)
      0: mult_sel = 1;
      1: div_sel = 1;
      2: instr_dec.cheri_op.csetboundsimm = 1;
      3: ex1_is_cjalr = 1;
    endcase
  endtask

  // Every EX2-busy class against every upstream class.
  task automatic exercise_occupancy;
    int n;
    n = CHERIoTEn ? 4 : 2;
    for (int e = 0; e < n; e++) begin
      for (int u = 0; u < n; u++) begin
        set_ex2_class(e);
        set_us_class(u);
        ex2_valid = 1; ex2_rdy = 0; us_valid_i = 1;
        tick();
      end
    end
    ex2_valid = 0; ex2_rdy = 1; us_valid_i = 0;
    ex2_reg = '0; set_us_class(-1);
    tick();
  endtask

  task automatic exercise;
    tick();
    rst_ni = 1;
    accept_div(MD_OP_DIV, 2'b11, 32'h8000_0000, 32'hffff_ffff);
    accept_div(MD_OP_DIV, 2'b00, 32'h0000_0005, 32'h0000_0000);
    accept_div(MD_OP_REM, 2'b11, 32'hffff_fffe, 32'h0000_0001);
    accept_div(MD_OP_REM, 2'b00, 32'h0000_0000, 32'h0000_0007);
    accept_mulh(2'b11, 32'h8000_0000, 32'hffff_ffff);
    accept_mulh(2'b01, 32'h0000_0001, 32'h8000_0000);
    accept_mulh(2'b00, 32'h0000_0000, 32'h0000_0001);
    exercise_setbounds();
    exercise_occupancy();
  endtask
endmodule

module kudu_top;
  alu_pipeline alu_pipeline0_i();
  alu_pipeline #(.PlName("alu_fixture1"), .SingleStage(0)) alu_pipeline1_i();
  mult_pipeline mult_pipeline_i();

  initial begin
    fork
      alu_pipeline0_i.exercise();
      alu_pipeline1_i.exercise();
      mult_pipeline_i.exercise();
    join
    $display("PASS EX semantics CHERIoTEn=%0d", mult_pipeline_i.CHERIoTEn);
    $finish;
  end
endmodule
