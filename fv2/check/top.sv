// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Stage-1 end-to-end formal harness: kudu_top against the cheriot-sail spec
// (README.md). Structure follows cheriot-ibex dv/formal/check/top.sv.
//
// This wrapper instantiates the DUT, constrains its environment and then
// includes the harness proper:
//   abs.sv           DUT state -> Sail types
//   spec_instance.sv two chained spec instances evaluated at issue
//   follower.sv      per-scoreboard-entry and per-LS-request spec results
//   checks.sv        assertions and covers

`define KDUT dut
`define KISS dut.issuer_i
`define KCMT dut.committer_i
`define KCSR dut.cs_registers_i
`define KSBD dut.sbd_fifo_i
`define KLSU dut.ls_pipeline_i.load_store_unit_i

module kudu_e2e_top (
  input  logic                         clk_i,
  input  logic                         rst_ni,

  input  logic                         cheri_pmode_i,
  input  logic [31:0]                  hart_id_i,
  input  logic [31:0]                  boot_addr_i,

  // Instruction memory interface
  input  logic                         instr_gnt_i,
  input  logic                         instr_rvalid_i,
  input  logic [63:0]                  instr_rdata_i,
  input  logic                         instr_err_i,

  // Data memory interface
  input  logic                         data_gnt_i,
  input  logic                         data_rvalid_i,
  input  logic [super_pkg::MemW-1:0]   data_rdata_i,
  input  logic                         data_err_i,
  input  logic                         data_sc_fail_i,

  input  logic [31:0]                  tsmap_rdata_i,

  // Interrupt inputs
  input  logic                         irq_software_i,
  input  logic                         irq_timer_i,
  input  logic                         irq_external_i,
  input  logic [14:0]                  irq_fast_i,

  // Debug inputs
  input  logic                         debug_req_i,

  // Free spec inputs, one set per spec instance (slot 0 / slot 1):
  //  - register values the DUT does not read at that issue ({tag, 64 bits},
  //    decoded with capBitsToCapability)
  //  - read data returned to the spec's ReadRAM calls
  //  - the SC.W reservation outcome (match_reservation)
  input  logic [31:1][64:0]            spec0_free_regs_i,
  input  logic [31:1][64:0]            spec1_free_regs_i,
  input  logic [31:0]                  spec0_rd_fst_i,
  input  logic [31:0]                  spec0_rd_snd_i,
  input  logic                         spec0_rd_tag_i,
  input  logic                         spec0_sc_ok_i,
  input  logic [31:0]                  spec1_rd_fst_i,
  input  logic [31:0]                  spec1_rd_snd_i,
  input  logic                         spec1_rd_tag_i,
  input  logic                         spec1_sc_ok_i
);

  ////////////////////// Configuration //////////////////////

  // KuduCfg1 with the data cache disabled (rtl/kudu_cfg_pkg.sv is not edited).
  function automatic kudu_cfg_pkg::kudu_cfg_t kudu_e2e_cfg();
    kudu_cfg_pkg::kudu_cfg_t c;
    c          = kudu_cfg_pkg::KuduCfg1;
    c.DCacheEn = 1'b0;
    return c;
  endfunction

  localparam kudu_cfg_pkg::kudu_cfg_t KuduE2eCfg = kudu_e2e_cfg();

  localparam logic [31:0] BootAddr = 32'h8000_0000;
  localparam int unsigned MemW     = super_pkg::MemW;

  ////////////////////// DUT //////////////////////

  logic                instr_req_o;
  logic [31:0]         instr_addr_o;
  logic                data_req_o;
  logic                data_is_cap_o;
  logic [3:0]          data_amo_flag_o;
  logic                data_we_o;
  logic [3:0]          data_be_o;
  logic [31:0]         data_addr_o;
  logic [MemW-1:0]     data_wdata_o;
  logic                tsmap_cs_o;
  logic [15:0]         tsmap_addr_o;
  logic                cheri_fatal_err_o;

  kudu_top #(
    .CHERIoTEn  (1'b1),
    .UseDWMult  (1'b0),
    .RvfiDumpEn (1'b0),
    .CFG        (KuduE2eCfg)
  ) dut (
    .clk_i             (clk_i),
    .rst_ni            (rst_ni),
    .cheri_pmode_i     (cheri_pmode_i),
    .hart_id_i         (hart_id_i),
    .boot_addr_i       (boot_addr_i),
    .instr_req_o       (instr_req_o),
    .instr_gnt_i       (instr_gnt_i),
    .instr_rvalid_i    (instr_rvalid_i),
    .instr_addr_o      (instr_addr_o),
    .instr_rdata_i     (instr_rdata_i),
    .instr_err_i       (instr_err_i),
    .data_req_o        (data_req_o),
    .data_is_cap_o     (data_is_cap_o),
    .data_amo_flag_o   (data_amo_flag_o),
    .data_gnt_i        (data_gnt_i),
    .data_rvalid_i     (data_rvalid_i),
    .data_we_o         (data_we_o),
    .data_be_o         (data_be_o),
    .data_addr_o       (data_addr_o),
    .data_wdata_o      (data_wdata_o),
    .data_rdata_i      (data_rdata_i),
    .data_err_i        (data_err_i),
    .data_sc_fail_i    (data_sc_fail_i),
    .tsmap_cs_o        (tsmap_cs_o),
    .tsmap_addr_o      (tsmap_addr_o),
    .tsmap_rdata_i     (tsmap_rdata_i),
    .cheri_fatal_err_o (cheri_fatal_err_o),
    .irq_software_i    (irq_software_i),
    .irq_timer_i       (irq_timer_i),
    .irq_external_i    (irq_external_i),
    .irq_fast_i        (irq_fast_i),
    .debug_req_i       (debug_req_i)
  );

  default clocking @(posedge clk_i); endclocking
  default disable iff (!rst_ni);

  ////////////////////// Environment //////////////////////

  // Static configuration: CHERIoT mode, fixed boot address and hart ID.
  Env_Pmode:    assume property (@(posedge clk_i) cheri_pmode_i);
  Env_BootAddr: assume property (@(posedge clk_i) boot_addr_i == BootAddr);
  Env_HartId:   assume property (@(posedge clk_i) ##1 $stable(hart_id_i));

  // No debug, no bus errors, no revocation. data_sc_fail_i is free; the SC
  // response is tied to the spec's reservation outcome (Mem_ScFail).
  Env_NoDebugReq: assume property (@(posedge clk_i) !debug_req_i);
  Env_NoInstrErr: assume property (@(posedge clk_i) !instr_err_i);
  Env_NoDataErr:  assume property (@(posedge clk_i) !data_err_i);
  Env_NoRevoke:   assume property (@(posedge clk_i) tsmap_rdata_i == '0);

  // Bus protocol (as fv/fv_fcov_env.sv): a grant only answers a pending
  // request, a request is granted within 4 (fetch) or 2 (data) cycles, and
  // each grant gets exactly one response in the next cycle.
  logic instr_rsp_due, data_rsp_due;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_rsp_due <= 1'b0;
      data_rsp_due  <= 1'b0;
    end else begin
      instr_rsp_due <= instr_req_o && instr_gnt_i;
      data_rsp_due  <= data_req_o && data_gnt_i;
    end
  end

  Env_InstrGntReq:    assume property (@(posedge clk_i) instr_gnt_i |-> rst_ni && instr_req_o);
  Env_InstrGntWithin: assume property (@(posedge clk_i) instr_req_o |-> ##[0:3] instr_gnt_i);
  Env_InstrRsp:       assume property (@(posedge clk_i) instr_rvalid_i == instr_rsp_due);
  Env_DataGntReq:     assume property (@(posedge clk_i) data_gnt_i |-> rst_ni && data_req_o);
  Env_DataGntWithin:  assume property (@(posedge clk_i) data_req_o |-> ##[0:1] data_gnt_i);
  Env_DataRsp:        assume property (@(posedge clk_i) data_rvalid_i == data_rsp_due);

`ifdef E2E_ZERO_WAIT
  // Optional deep-BMC variant (not the default): every request is granted in
  // the cycle it is made, so a given depth covers more instructions.
  Env_InstrGntNow: assume property (@(posedge clk_i) instr_req_o |-> instr_gnt_i);
  Env_DataGntNow:  assume property (@(posedge clk_i) data_req_o |-> data_gnt_i);
`endif

  // An interrupt line stays asserted until the core has taken a trap.
  logic [17:0] irq_vec;
  assign irq_vec = {irq_fast_i, irq_external_i, irq_timer_i, irq_software_i};

  Env_IrqHeld: assume property (!`KDUT.csr_save_cause |=> ((irq_vec & $past(irq_vec)) == $past(irq_vec)));

  ////////////////////// Instruction restrictions //////////////////////

  // Scope (README section 4.4): CSR instructions only touch CSRs modelled by
  // both sides; no hardware breakpoints. Since 2026-11-26 the whole OP,
  // OP-IMM and AMO opcode spaces are in scope (B = Zba/Zbb/Zbc/Zbs and A =
  // LR/SC/AMO*.W, plus every unimplemented encoding there, which both sides
  // must treat as illegal; the spec has Zbkb/Zbkx disabled, README 1.1).
  function automatic logic insn_in_scope(logic [31:0] insn, logic is_comp, logic [15:0] c_insn);
    logic [6:0]  opc, f7;
    logic [2:0]  f3;
    logic [11:0] csr;
    logic        ok;
    opc = insn[6:0];
    f3  = insn[14:12];
    f7  = insn[31:25];
    csr = insn[31:20];
    ok  = 1'b1;
    if (is_comp) return 1'b1;                                    // raw 16-bit parcel
    if ((opc == 7'h73) && (f3 != 3'd0))                          // Zicsr
      ok = (csr == 12'h300) || (csr == 12'h301) || (csr == 12'h304) ||
           (csr == 12'h340) ||
           (csr == 12'h342) || (csr == 12'h343) || (csr == 12'hf11) ||
           (csr == 12'hf12) || (csr == 12'hf13) || (csr == 12'hf14) ||
           (csr == 12'hbc1) || (csr == 12'hbc2);
    // Known Kudu/Sail divergences, excluded until resolved (README section 6):
    // - CSR access to mtvec (0x305) / mepc (0x341): Kudu illegal in pmode
    //   (cs_registers.sv); the Sail spec raises a CHERI AccessSystemRegs
    //   exception without ASR and an internal error (upstream internal_error)
    //   on a write with ASR.
    return ok;
  endfunction

  for (genvar k = 0; k < 2; k++) begin : g_ir_scope
    super_pkg::ir_dec_t ir_dec;
    // ir_valid is in program order (ir0/ir1), not physical slot order.
    assign ir_dec = ((k == 0) == `KDUT.ira_is0) ? `KDUT.ira_dec : `KDUT.irb_dec;

    // Scope is decided on the raw fetched bits, not on Kudu's decode: a
    // 32-bit insn is the memory word (Fetch_Iss*), and every 16-bit encoding
    // is in scope (no RV32C form expands into an excluded instruction), so a
    // mis-expansion reaches the spec instead of being assumed away.
    Env_InsnScope: assume property (`KDUT.ir_valid[k] |-> insn_in_scope(ir_dec.insn, ir_dec.is_comp, ir_dec.c_insn));
    // Kudu's length decode agrees with the raw low bits the spec decodes.
    Scope_IsComp:  assert property (`KDUT.ir_valid[k] |->
                                    (ir_dec.is_comp ? (ir_dec.c_insn[1:0] != 2'b11) : (ir_dec.insn[1:0] == 2'b11)));
    // Breakpoints cannot be armed (no debug, trigger CSRs out of scope), so
    // Kudu must never flag an in-scope instruction as one.
    Scope_NoBrkpt: assert property (`KDUT.ir_valid[k] |-> !ir_dec.is_brkpt);
    // No instruction ends at 2^32 (PC + length wraps to 0). Sail's CJAL/CJALR
    // assert that the link cap at nextPC is representable, which fails on the
    // wrap; sail_assert is a no-op in the SV build, so the spec is undefined.
    Env_NoPcWrap:  assume property (`KDUT.ir_valid[k] |->
                                    (33'(ir_dec.pc) + (ir_dec.is_comp ? 33'd2 : 33'd4)) < 33'h1_0000_0000);
  end

  ////////////////////// Harness //////////////////////

`include "abs.sv"
`include "spec_instance.sv"
`include "follower.sv"
`include "checks.sv"
`include "inv.sv"
`include "fetch.sv"

endmodule

`undef KDUT
`undef KISS
`undef KCMT
`undef KCSR
`undef KSBD
`undef KLSU
