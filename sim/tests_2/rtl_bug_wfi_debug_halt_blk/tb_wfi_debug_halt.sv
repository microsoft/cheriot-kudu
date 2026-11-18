// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps
module tb_wfi_debug_halt;
  import cheri_pkg::*;
  import csr_pkg::*;
  import super_pkg::*;

  logic clk = 0;
  always #5 clk = ~clk;
  logic rst_n = 0;
  logic [1:0] ir_valid = 0;
  ir_reg_t ir_reg;
  ir_dec_t ir_dec;
  logic [1:0] issuer_rdy;
  logic debug_req = 0;
  logic irq_pending = 0;
  logic debug_mode, fetch_req, pc_set;
  logic [31:0] pc_target;
  logic debug_csr_save;
  dbg_cause_e debug_cause;
  irqs_t irqs;

  always_comb begin
    irqs = '0;
    irqs.irq_software = irq_pending;
  end

  ir_decoder #(.CHERIoTEn(1)) decoder (
    .clk_i(clk), .rst_ni(rst_n), .cheri_pmode_i(1'b0),
    .debug_mode_i(debug_mode), .pcc_cap_i(NULL_PCC_CAP),
    .ir_reg_i(ir_reg), .brkpt_match_i(1'b0), .ir_dec_o(ir_dec)
  );

  issuer #(.CHERIoTEn(1), .DmHaltAddr(32'h84000000)) dut (
    .clk_i(clk), .rst_ni(rst_n),
    .cheri_pmode_i(1'b0), .tsafe_en_i(1'b0),
    .boot_addr_i(32'h80000000),
    .ira_dec_i(ir_dec), .irb_dec_i(ir_dec_t'('0)), .ira_is0_i(1'b1),
    .ir_valid_i(ir_valid), .issuer_rdy_o(issuer_rdy),
    .ir_hold_o(), .ir_flush_o(),
    .ira_op_rdata2_i(op_data2_t'('0)), .irb_op_rdata2_i(op_data2_t'('0)),
    .alupl0_rdy_i(1'b1), .alupl0_fwd_info_i(pl_fwd_t'('0)), .alupl0_fwd_act_i(32'b0),
    .alupl1_rdy_i(1'b1), .alupl1_fwd_info_i(pl_fwd_t'('0)), .alupl1_fwd_act_i(32'b0),
    .lspl_rdy_i(1'b1), .lspl_fwd_info_i(pl_fwd_t'('0)), .lspl_fwd_act_i(32'b0),
    .multpl_rdy_i(1'b1), .multpl_fwd_info_i(pl_fwd_t'('0)), .multpl_fwd_act_i(32'b0),
    .ex_valid_o(), .lspl_sel_ira_o(), .multpl_sel_ira_o(), .cmplx_sel_ira_o(),
    .waw_act_o(),
    .cmt_err_i(1'b0), .cmt_err_info_i(exc_info_t'('0)), .cmt_regwr_i(32'b0),
    .cmt_flush_o(), .sbdfifo_rd_valid_i(2'b00), .sbdfifo_wr_rdy_i(2'b11),
    .sbdfifo_wr_valid_o(), .sbdfifo_wdata0_o(), .sbdfifo_wdata1_o(),
    .branch_info_i(branch_info_t'('0)),
    .ir0_jalr_target_i(32'b0), .ir1_jalr_target_i(32'b0),
    .ir0_cjalr_err_i(3'b0), .ir1_cjalr_err_i(3'b0),
    .ira_full_data2_fwd_o(), .irb_full_data2_fwd_o(),
    .fetch_req_o(fetch_req), .pc_set_o(pc_set), .pc_target_o(pc_target),
    .ex_bp_init_o(), .ex_bp_info_o(), .ex_alt_ctrl_o(),
    .priv_mode_i(PRIV_LVL_M), .irq_pending_i(irq_pending), .irqs_i(irqs),
    .csr_mstatus_mie_i(1'b0), .csr_mstatus_tw_i(1'b0), .csr_mtvec_i(32'h80000100), .csr_mepc_i(32'b0),
    .csr_mtvec_init_o(), .csr_save_cause_o(), .csr_exc_info_o(),
    .csr_restore_mret_o(), .csr_restore_dret_o(), .csr_mispredict_o(),
    .debug_req_i(debug_req), .csr_depc_i(32'b0), .debug_step_i(1'b0),
    .debug_ebreakm_i(1'b0), .debug_ebreaku_i(1'b0),
    .debug_mode_o(debug_mode), .debug_cause_o(debug_cause),
    .debug_csr_save_o(debug_csr_save),
    .trvk_en_i(1'b0), .trvk_addr_i(5'b0), .trvk_clrtag_i(1'b0),
    .trvk_outstanding_i(1'b0),
    .cmplx_instr_done_i(1'b0), .cmplx_sbd_wr_i(1'b0),
    .cmplx_sbd_wdata_i(sbd_fifo_t'('0)), .cmplx_instr_start_o()
  );

  task automatic reset_core;
    @(negedge clk);
    rst_n = 0;
    ir_valid = 0;
    debug_req = 0;
    irq_pending = 0;
    ir_reg = '0;
    ir_reg.insn = 32'h00000013;
    ir_reg.pc = 32'h80000080;
    repeat (3) @(negedge clk);
    rst_n = 1;
    repeat (3) @(negedge clk);
    if (debug_mode !== 0 || fetch_req !== 1)
      $fatal(1, "SETUP: reset must reach normal fetching");
  endtask

  task automatic enter_wfi;
    ir_reg.insn = 32'h10500073;
    ir_valid = 2'b01;
    #1;
    if (ir_dec.any_err !== 0 || ir_dec.sysctl.wfi !== 1 ||
        ir_dec.pl_type != PL_LOCAL)
      $fatal(1, "SETUP: production decoder did not accept legal WFI");
    for (int cycle = 0; cycle < 12; cycle++) begin
      @(negedge clk);
      if (issuer_rdy[0]) begin
        @(posedge clk);
        @(negedge clk);
        ir_valid = 0;
        ir_reg.insn = 32'h00000013;
        ir_reg.pc = 32'h80000084;
        if (fetch_req !== 0 || debug_mode !== 0)
          $fatal(1, "SETUP: accepted WFI must stop fetching outside debug mode");
        $display("SETUP PASS: decoded WFI accepted; fetch_req=0, debug_mode=0");
        return;
      end
    end
    $fatal(1, "SETUP: WFI was not accepted");
  endtask

  task automatic check_halt(input string label);
    bit saw_debug_redirect;
    saw_debug_redirect = 0;
    debug_req = 1;
    for (int cycle = 0; cycle < 32; cycle++) begin
      @(negedge clk);
      if (debug_csr_save && pc_set && pc_target == 32'h84000000 &&
          debug_cause == DBG_CAUSE_HALTREQ)
        saw_debug_redirect = 1;
      if (debug_mode) begin
        if (!saw_debug_redirect)
          $fatal(1, "%s: debug mode without halt-request redirect", label);
        $display("%s PASS: expected debug_mode=1, actual=1 after %0d cycles",
                 label, cycle + 1);
        return;
      end
    end
    $display("%s FAIL: expected debug_mode=1 after held halt request; actual debug_mode=%b fetch_req=%b irq_pending=%b",
             label, debug_mode, fetch_req, irq_pending);
    $fatal(1, "WFI must leave its stalled state and enter Debug Mode on a halt request");
  endtask

  initial begin
    reset_core();
    check_halt("CONTROL normal execution");

    reset_core();
    enter_wfi();
    irq_pending = 1;
    repeat (3) @(negedge clk);
    irq_pending = 0;
    if (fetch_req !== 1 || debug_mode !== 0)
      $fatal(1, "CONTROL: pending interrupt must resume WFI even with MIE=0");
    $display("CONTROL interrupt wake PASS: expected fetch_req=1, actual=1");
    check_halt("CONTROL after interrupt wake");

    if ($test$plusargs("CONTROL_ONLY")) begin
      $display("All nontrigger controls PASS");
      $finish;
    end

    reset_core();
    enter_wfi();
    check_halt("TRIGGER halt during WFI");
    $display("PASS: sleeping core honors debug halt");
    $finish;
  end

  initial begin
    #10000;
    $fatal(1, "Testbench watchdog expired");
  end
endmodule
