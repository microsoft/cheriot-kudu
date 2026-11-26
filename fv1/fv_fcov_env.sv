// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Environment assumptions for FPV of the fcov SVAs (fv_kudu_fcov.tcl). The
// CHERIoT mode (cheri_pmode_i) is set by fv_kudu_fcov.tcl.

module fv_fcov_env (
  input logic        clk_i,
  input logic        rst_ni,
  input logic [31:0] boot_addr_i,
  input logic        instr_req_o,
  input logic        instr_gnt_i,
  input logic        instr_rvalid_i,
  input logic        instr_err_i,
  input logic        data_req_o,
  input logic        data_gnt_i,
  input logic        data_rvalid_i,
  input logic        data_err_i,
  input logic        irq_software_i,
  input logic        irq_timer_i,
  input logic        irq_external_i,
  input logic [14:0] irq_fast_i,
  input logic        debug_req_i,
  input logic        debug_mode,
  input logic        csr_save_cause
);

  AssumeBootAddr: assume property (@(posedge clk_i) boot_addr_i == 32'h8000_0000);

  // Bus protocol: a grant only answers a pending request, a request is granted
  // within 4 (fetch) or 2 (data) cycles, and each grant gets exactly one
  // response in the next cycle.
  logic instr_rsp_due, data_rsp_due;
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      instr_rsp_due <= 1'b0;
      data_rsp_due  <= 1'b0;
    end else begin
      instr_rsp_due <= instr_req_o && instr_gnt_i;
      data_rsp_due  <= data_req_o && data_gnt_i;
    end
  end

  AssumeInstrGntReq:    assume property (@(posedge clk_i) instr_gnt_i |-> rst_ni && instr_req_o);
  AssumeInstrGntWithin: assume property (@(posedge clk_i) instr_req_o |-> ##[0:3] instr_gnt_i);
  AssumeInstrRsp:       assume property (@(posedge clk_i) instr_rvalid_i == instr_rsp_due);
  AssumeDataGntReq:     assume property (@(posedge clk_i) data_gnt_i |-> rst_ni && data_req_o);
  AssumeDataGntWithin:  assume property (@(posedge clk_i) data_req_o |-> ##[0:1] data_gnt_i);
  AssumeDataRsp:        assume property (@(posedge clk_i) data_rvalid_i == data_rsp_due);

  // A bus error is part of a response: it is only valid with rvalid. The LSU
  // and the fetch unit sample *_err_i unqualified, so an error without
  // rvalid would inject faults into idle cycles.
  AssumeDataErrQual:  assume property (@(posedge clk_i) data_err_i  |-> data_rvalid_i);
  AssumeInstrErrQual: assume property (@(posedge clk_i) instr_err_i |-> instr_rvalid_i);

`ifndef FCOV_FV_FREE_REQ
  // Integration requirement from the KUDU-072/KUDU-073 waivers: an interrupt
  // line stays asserted until the core has taken a trap (csr_save_cause), and
  // debug_req stays asserted until the core is in debug mode. Define
  // FCOV_FV_FREE_REQ to let them withdraw at any time.
  logic [17:0] irq;
  assign irq = {irq_fast_i, irq_external_i, irq_timer_i, irq_software_i};

  AssumeIrqHeld: assume property (@(posedge clk_i) disable iff (!rst_ni)
    !csr_save_cause |=> ((irq & $past(irq)) == $past(irq)));
  AssumeDbgReqHeld: assume property (@(posedge clk_i) disable iff (!rst_ni)
    debug_req_i && !debug_mode |=> debug_req_i);
`endif

endmodule

bind kudu_top fv_fcov_env u_fv_fcov_env (.*);
