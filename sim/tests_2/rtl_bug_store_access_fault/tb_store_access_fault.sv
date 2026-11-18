// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps
module tb_store_access_fault;
  import cheri_pkg::*;
  import csr_pkg::*;
  import super_pkg::*;

  logic clk = 0;
  always #5 clk = ~clk;
  logic rst_n = 0;
  logic req = 0, req_done;
  lsu_req_info_t req_info = NULL_LSU_REQ_INFO;
  logic data_req, data_we, data_gnt = 0;
  logic [31:0] data_addr;
  logic [3:0] data_be;
  logic [MemW-1:0] data_wdata;
  logic data_rvalid = 0, data_err = 0;
  logic resp_valid, resp_err;
  pl_out_t resp_info;
  integer failures = 0;

  // A CHERIoT-capable core in its supported plain RV32 compatibility mode.
  load_store_unit #(.CHERIoTEn(1)) dut (
    .clk_i(clk), .rst_ni(rst_n), .cheri_pmode_i(1'b0), .debug_mode_i(1'b0),
    .data_req_o(data_req), .data_is_cap_o(), .data_amo_flag_o(),
    .data_gnt_i(data_gnt), .data_rvalid_i(data_rvalid), .data_err_i(data_err),
    .data_pmp_err_i(1'b0), .data_sc_fail_i(1'b0),
    .data_addr_o(data_addr), .data_we_o(data_we), .data_be_o(data_be),
    .data_wdata_o(data_wdata), .data_rdata_i(MemW'(32'h12345678)),
    .lsu_req_i(req), .lsu_req_info_i(req_info), .lsu_req_done_o(req_done),
    .lsu_resp_valid_o(resp_valid), .lsu_resp_err_o(resp_err),
    .lsu_resp_info_o(resp_info), .addr_last_o(), .ds_rdy_i(1'b1),
    .csr_access_o(), .csr_cheri_o(), .csr_op_en_o(), .csr_op_o(), .csr_addr_o(),
    .csr_wdata_o(), .csr_rdata_i(RegW'(0)), .illegal_csr_insn_i(1'b0),
    .csr_lsu_wr_req_o(), .csr_lsu_addr_o(),
    .busy_o(), .perf_load_o(), .perf_store_o()
  );

  task automatic access_word(input string label, input bit is_load,
                             input bit bus_error, input int grant_wait,
                             input int response_wait);
    logic [5:0] expected_cause;
    @(negedge clk);
    req_info = NULL_LSU_REQ_INFO;
    req_info.is_load = is_load;
    req_info.rf_we = is_load;
    req_info.data_type = 2'b00;
    req_info.addr = 32'h80001000;
    req_info.wdata = MemW'(32'hcafe1234);
    req_info.rs1 = 5'd1;
    req_info.rd = is_load ? 5'd3 : 5'd0;
    req_info.insn = is_load ? 32'h0000a183 : 32'h0020a023; // lw x3,0(x1) / sw x2,0(x1)
    req_info.pc = RegW'(32'h80000000);
    req = 1;
    repeat (grant_wait) begin
      #1;
      if (data_req !== 1'b1 || req_done !== 1'b0)
        $fatal(1, "%s: request not held while waiting for grant", label);
      @(negedge clk);
    end
    data_gnt = 1;
    #1;
    if (data_req !== 1'b1 || req_done !== 1'b1 ||
        data_we !== !is_load || data_addr !== 32'h80001000 ||
        data_be !== 4'hf || (!is_load && data_wdata[31:0] !== 32'hcafe1234))
      $fatal(1, "%s: malformed bus request", label);
    @(posedge clk);
    @(negedge clk);
    req = 0;
    data_gnt = 0;
    repeat (response_wait) begin
      #1;
      if (resp_valid !== 1'b0)
        $fatal(1, "%s: response before memory responded", label);
      @(negedge clk);
    end
    // Exactly one response to the previously granted transaction; stores also
    // receive responses on the core's data interface.
    data_rvalid = 1;
    data_err = bus_error;
    #1;
    if (resp_valid !== 1'b1 || resp_err !== bus_error || resp_info.err !== bus_error)
      $fatal(1, "%s: response valid/error mismatch", label);
    if (!bus_error && is_load && resp_info.wdata[31:0] !== 32'h12345678)
      $fatal(1, "%s: wrong load data", label);
    expected_cause = is_load ? EXC_CAUSE_LOAD_ACCESS_FAULT : EXC_CAUSE_STORE_ACCESS_FAULT;
    if (bus_error && (resp_info.mcause !== expected_cause ||
                      resp_info.mtval !== 32'h80001000)) begin
      $display("FAIL %s: observed mcause=%0d mtval=%08h; expected mcause=%0d mtval=80001000",
               label, resp_info.mcause, resp_info.mtval, expected_cause);
      failures++;
    end else begin
      $display("PASS %s: err=%0b mcause=%0d mtval=%08h",
               label, resp_err, resp_info.mcause, resp_info.mtval);
    end
    @(posedge clk);
    @(negedge clk);
    data_rvalid = 0;
    data_err = 0;
    #1;
    if (resp_valid !== 1'b0)
      $fatal(1, "%s: duplicate response", label);
  endtask

  initial begin
    repeat (3) @(negedge clk);
    rst_n = 1;
    access_word("LW success baseline", 1, 0, 0, 0);
    access_word("SW success baseline", 0, 0, 2, 2);
    access_word("LW access fault baseline", 1, 1, 0, 1);
    access_word("SW access fault immediate grant", 0, 1, 0, 0);
    access_word("SW access fault delayed grant/response", 0, 1, 2, 3);
    if (failures != 0)
      $fatal(1, "STORE_ACCESS_FAULT_REPRO: %0d checks failed", failures);
    $display("PASS: all access-fault checks");
    $finish;
  end

  initial begin
    #5000;
    $fatal(1, "Timeout waiting for LSU transactions");
  end
endmodule
