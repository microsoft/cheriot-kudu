// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// FC_MA_TOP -- scoreboard occupancy, top-level I/O and transaction timing for both
// instruction and data interfaces. Revocation handshakes live in FC_MA_LSU.trvk.
//
// Bound to rtl/kudu_top.sv.  See doc/functional_coverage_plan.md section 14.

// Standalone timing tests exclude the covergroup owner and its package imports.
`ifndef KUDU_FCOV_BUS_TIMING_ONLY
module kudu_fcov_top
  import super_pkg::*;
  import csr_pkg::*;
  import kudu_fcov_pkg::*;
#(
  parameter int unsigned MemW = 33,
  parameter bit CHERIoTEn = 1'b0,
  parameter bit UnalignedFetch = 1'b0
) (
  input logic             clk_i,
  input logic             rst_ni,

  // --- static configuration --------------------------------------------------
  input logic             cheri_pmode_i,
  input logic [31:0]      hart_id_i,
  input logic [31:0]      boot_addr_i,

  // --- instruction bus -------------------------------------------------------
  input logic             instr_req_o,
  input logic             instr_gnt_i,
  input logic             instr_rvalid_i,
  input logic [31:0]      instr_addr_o,
  input logic [63:0]      instr_rdata_i,
  input logic             instr_err_i,

  // --- data bus --------------------------------------------------------------
  input logic             data_req_o,
  input logic             data_is_cap_o,
  input logic [3:0]       data_amo_flag_o,
  input logic             data_gnt_i,
  input logic             data_rvalid_i,
  input logic             data_we_o,
  input logic [3:0]       data_be_o,
  input logic [31:0]      data_addr_o,
  input logic [MemW-1:0]  data_wdata_o,
  input logic [MemW-1:0]  data_rdata_i,
  input logic             data_err_i,
  input logic             data_sc_fail_i,

  // --- temporal safety map ---------------------------------------------------
  input logic             tsmap_cs_o,
  input logic [15:0]      tsmap_addr_o,
  input logic [31:0]      tsmap_rdata_i,

  // --- CHERI fatal error -----------------------------------------------------
  input logic             cheri_fatal_err_o,

  // --- interrupts and debug --------------------------------------------------
  input logic             irq_software_i,
  input logic             irq_timer_i,
  input logic             irq_external_i,
  input logic [14:0]      irq_fast_i,
  input logic             debug_req_i
);

`ifndef KUDU_FCOV_OFF

  logic cheri_active;
  assign cheri_active = CHERIoTEn && cheri_pmode_i;

  // --------------------------------------------------------------------------
  // Both interfaces own their scalar bus/timing coverage here, not in LSU.
  // Queued metadata associates SC results with the accepted request, rather
  // than the LSU's live instruction decode (which can already have advanced).
  // --------------------------------------------------------------------------
  logic [63:0] igw_obs, irw_obs, dgw_obs, drw_obs;
  logic igw_ev, irw_ev, dgw_ev, drw_ev, irw_same_cycle, drw_same_cycle;
  logic [6:0] data_resp_meta;
  logic [0:0] unused_instr_meta;
  logic data_sc_fail_q, data_rtag_q, data_resp_err_q;
  logic tsmap_resp_valid_q;

  // The map interface returns a word one clock after chip-select.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)
      tsmap_resp_valid_q <= 1'b0;
    else
      tsmap_resp_valid_q <= tsmap_cs_o && cheri_active;
  end

  kudu_fcov_bus_timing u_instr_timing (
    .clk_i, .rst_ni, .req_i(instr_req_o), .gnt_i(instr_gnt_i),
    .rvalid_i(instr_rvalid_i), .meta_i(1'b0),
    .gnt_ev_o(igw_ev), .gnt_delay_o(igw_obs),
    .resp_ev_o(irw_ev), .resp_delay_o(irw_obs),
    .resp_same_cycle_o(irw_same_cycle), .resp_meta_o(unused_instr_meta)
  );

  kudu_fcov_bus_timing #(.MetaW(7)) u_data_timing (
    .clk_i, .rst_ni, .req_i(data_req_o), .gnt_i(data_gnt_i),
    .rvalid_i(data_rvalid_i),
    .meta_i({cheri_active, data_is_cap_o, data_we_o, data_amo_flag_o}),
    .gnt_ev_o(dgw_ev), .gnt_delay_o(dgw_obs),
    .resp_ev_o(drw_ev), .resp_delay_o(drw_obs),
    .resp_same_cycle_o(drw_same_cycle), .resp_meta_o(data_resp_meta)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_sc_fail_q <= 1'b0;
      data_rtag_q <= 1'b0;
      data_resp_err_q <= 1'b0;
    end else if (data_rvalid_i) begin
      data_sc_fail_q <= data_sc_fail_i;
      data_rtag_q <= data_rdata_i[MemW-1];
      data_resp_err_q <= data_err_i;
    end
  end

  // Back-to-back accepted requests on consecutive clock edges.
  logic instr_gnt_q, data_gnt_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_gnt_q <= 1'b0;
      data_gnt_q  <= 1'b0;
    end else begin
      instr_gnt_q <= instr_req_o & instr_gnt_i;
      data_gnt_q  <= data_req_o  & data_gnt_i;
    end
  end

  // ==========================================================================
  // FC_MA_TOP - top-level queues, bus and I/O
  // ==========================================================================
  covergroup cg_ma_top with function sample(bit normal_sample);
    option.per_instance = 1;
    option.name         = "FC_MA_TOP";

    // Each hardware report covers only its applicable runtime modes.
    cp_operating_mode: coverpoint {CHERIoTEn, cheri_active} iff (normal_sample) {
      bins rv32_only = {2'b00};
      bins rv32_compatible = {2'b10};
      bins cheriot = {2'b11};
      ignore_bins other_hardware = {2'b00, 2'b10, 2'b11}
          with (CHERIoTEn ? item == 2'b00 : item != 2'b00);
    }

    cp_sbd_fifo_level: coverpoint kudu_top.sbd_fifo_i.fifo_level iff (normal_sample) {
      bins level_0 = {0};
      bins level_1 = {1};
      bins level_2 = {2};
      bins level_3 = {3};
      bins level_4 = {4};
      bins level_5 = {5};
      bins level_6_up = {[6:$]};
    }

    // ======================================================================
    // 14.1 Instruction bus
    // ======================================================================

    cp_ibus_req_gnt: coverpoint {instr_req_o, instr_gnt_i} iff (normal_sample) {
      bins idle      = {2'b00};
      bins ready_no_req = {2'b01};
      bins waiting   = {2'b10};
      bins accepted  = {2'b11};
    }
    cp_ibus_rvalid: coverpoint instr_rvalid_i iff (normal_sample) { bins hit = {1'b1}; }
    cp_ibus_err: coverpoint instr_err_i iff (normal_sample && instr_rvalid_i) {
      bins ok  = {1'b0};
      bins err = {1'b1};
    }
    // prefetch_buffer64 masks two or three low bits by UnalignedFetch.
    cp_ibus_addr_align: coverpoint instr_addr_o[2:0] iff (normal_sample && instr_req_o) {
      bins a[] = {3'd0, 3'd4} with (UnalignedFetch || item == 0);
    }
    // instr_rdata_i is 64 bits; covering every value is meaningless, so the
    // useful property is whether either half decodes as compressed.
    cp_rdata_comp: coverpoint {instr_rdata_i[33:32] == 2'b11, instr_rdata_i[1:0] == 2'b11}
                   iff (normal_sample && instr_rvalid_i) {
      bins both_comp   = {2'b00};
      bins hi_comp     = {2'b01};
      bins lo_comp     = {2'b10};
      bins neither     = {2'b11};
    }

    cp_gnt_delay: coverpoint igw_obs iff (normal_sample && igw_ev) {
      bins d0   = {0};
      bins d1   = {1};
      bins d2   = {2};
      bins d3_7 = {[3:7]};
      bins d8up = {[64'd8:64'hffff_ffff_ffff_ffff]};
    }
    cp_rvalid_delay: coverpoint irw_obs iff (normal_sample && irw_ev) {
      bins d0   = {0};
      bins d1   = {1};
      bins d2   = {2};
      bins d3_7 = {[3:7]};
      bins d8up = {[64'd8:64'hffff_ffff_ffff_ffff]};
    }
    cp_ibus_same_cycle_resp: coverpoint irw_same_cycle iff (normal_sample && irw_ev);
    cp_ibus_back_to_back: coverpoint (instr_gnt_q & instr_req_o & instr_gnt_i)
        iff (normal_sample) {
      bins hit = {1'b1};
    }

    // ======================================================================
    // 14.2 Data bus
    // ======================================================================
    cp_dbus_req_gnt: coverpoint {data_req_o, data_gnt_i} iff (normal_sample) {
      bins idle      = {2'b00};
      bins ready_no_req = {2'b01};
      bins waiting   = {2'b10};
      bins accepted  = {2'b11};
    }
    cp_dbus_rvalid: coverpoint data_rvalid_i iff (normal_sample) { bins hit = {1'b1}; }
    cp_we:     coverpoint data_we_o iff (normal_sample && data_req_o);
    cp_is_cap: coverpoint data_is_cap_o iff (normal_sample && cheri_active && data_req_o) {
      option.weight = CHERIoTEn ? 1 : 0;
    }
    cp_be: coverpoint data_be_o iff (normal_sample && data_req_o) {
      bins byte_[] = {4'b0001, 4'b0010, 4'b0100, 4'b1000};
      bins half_[] = {4'b0011, 4'b1100};
      bins word_   = {4'b1111};
      // Split word and halfword accesses (load_store_unit byte-enable mux).
      bins split[] = {4'b0110, 4'b0111, 4'b1110};
    }
    cp_amo: coverpoint data_amo_flag_o iff (normal_sample && data_req_o) {
      bins none  = {4'b0000};
      bins lr    = {4'b0001};
      bins sc    = {4'b0010};
      bins amo_r = {4'b0100};
      bins amo_w = {4'b1000};
    }
    cp_dbus_addr_align: coverpoint data_addr_o[2:0] iff (normal_sample && data_req_o) {
      // load_store_unit drives {data_addr[31:2], 2'b00}.
      bins a[] = {3'd0, 3'd4};
    }
    cp_dbus_err: coverpoint data_err_i iff (normal_sample && data_rvalid_i) {
      bins ok  = {1'b0};
      bins err = {1'b1};
    }
    cp_sc_resp: coverpoint data_sc_fail_q
        iff (normal_sample && drw_ev && data_resp_meta[1] && !data_resp_err_q) {
      bins succeeded = {1'b0};
      bins failed = {1'b1};
    }

    // The capability tag bit is the top bit of the memory word; a capability
    // must be seen crossing the bus in both directions with the tag set.
    cp_wdata_tag: coverpoint data_wdata_o[MemW-1]
        iff (normal_sample && cheri_active && data_req_o && data_we_o && data_is_cap_o) {
      option.weight = CHERIoTEn ? 1 : 0;
    }
    cp_rdata_tag: coverpoint data_rtag_q
        iff (normal_sample && cheri_active && drw_ev && data_resp_meta[6] &&
             data_resp_meta[5] && !data_resp_meta[4] && !data_resp_err_q) {
      option.weight = CHERIoTEn ? 1 : 0;
    }

    cp_dbus_gnt_delay: coverpoint dgw_obs iff (normal_sample && dgw_ev) {
      bins d0 = {0};
      bins d1 = {1};
      bins d2 = {2};
      bins d3_7 = {[3:7]};
      bins d8up = {[64'd8:64'hffff_ffff_ffff_ffff]};
    }
    cp_dbus_rvalid_delay: coverpoint drw_obs iff (normal_sample && drw_ev) {
      bins d0 = {0};
      bins d1 = {1};
      bins d2 = {2};
      bins d3_7 = {[3:7]};
      bins d8up = {[64'd8:64'hffff_ffff_ffff_ffff]};
    }
    cp_dbus_back_to_back: coverpoint (data_gnt_q & data_req_o & data_gnt_i)
        iff (normal_sample) {
      bins hit = {1'b1};
    }
    // Both buses busy in the same cycle: the case a single-port memory model
    // in the testbench would never produce.
    cp_both_buses: coverpoint (instr_req_o & data_req_o) iff (normal_sample) {
      bins hit = {1'b1};
    }

    // ======================================================================
    // 14.3 Temporal safety map, configuration and the fatal error output
    // ======================================================================
    // The scalar tsmap_cs hit is owned by FC_MA_LSU.trvk.
    cp_tsmap_addr: coverpoint tsmap_addr_o iff (normal_sample && cheri_active && tsmap_cs_o) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins zero  = {16'h0};
      bins low   = {[16'h1:16'hff]};
      bins mid   = {[16'h100:16'h3fff]};
      bins high  = {[16'h4000:16'hffff]};
    }
    cp_tsmap_addr_bits: coverpoint tsmap_addr_o[9:0]
        iff (normal_sample && cheri_active && tsmap_cs_o) {
      option.weight = CHERIoTEn ? 1 : 0;
      // Overlapping wildcard bins track each bit independently.
      wildcard bins bit0_zero = {10'b?????????0};
      wildcard bins bit0_one  = {10'b?????????1};
      wildcard bins bit1_zero = {10'b????????0?};
      wildcard bins bit1_one  = {10'b????????1?};
      wildcard bins bit2_zero = {10'b???????0??};
      wildcard bins bit2_one  = {10'b???????1??};
      wildcard bins bit3_zero = {10'b??????0???};
      wildcard bins bit3_one  = {10'b??????1???};
      wildcard bins bit4_zero = {10'b?????0????};
      wildcard bins bit4_one  = {10'b?????1????};
      wildcard bins bit5_zero = {10'b????0?????};
      wildcard bins bit5_one  = {10'b????1?????};
      wildcard bins bit6_zero = {10'b???0??????};
      wildcard bins bit6_one  = {10'b???1??????};
      wildcard bins bit7_zero = {10'b??0???????};
      wildcard bins bit7_one  = {10'b??1???????};
      wildcard bins bit8_zero = {10'b?0????????};
      wildcard bins bit8_one  = {10'b?1????????};
      wildcard bins bit9_zero = {10'b0?????????};
      wildcard bins bit9_one  = {10'b1?????????};
    }
    // The map word carries one revocation bit per granule; both an
    // all-clear word and a word with bits set must be returned or half the
    // trvk stage is untested from the outside.
    cp_tsmap_rdata: coverpoint $countones(tsmap_rdata_i)
        iff (normal_sample && cheri_active && tsmap_resp_valid_q) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins none = {0};
      bins few  = {[1:4]};
      bins many = {[5:31]};
      bins all_ = {32};
    }

    // PMODE is ignored by RV32-only hardware; both values matter on CHERI hardware.
    cp_pmode: coverpoint cheri_pmode_i iff (normal_sample && CHERIoTEn) {
      option.weight = CHERIoTEn ? 1 : 0;
    }
    cp_boot_addr: coverpoint boot_addr_i[15:0] iff (normal_sample) {
      bins aligned_256 = {16'h0000};
      bins other       = {[16'h0001:16'hffff]};
    }

    // ======================================================================
    // 14.4 Interrupts and debug request
    // ======================================================================
    cp_irq_software: coverpoint irq_software_i iff (normal_sample);
    cp_irq_timer:    coverpoint irq_timer_i iff (normal_sample);
    cp_irq_external: coverpoint irq_external_i iff (normal_sample);

    // Each of the fifteen fast interrupt lines has its own vector, so each
    // must be asserted individually; the count bin catches simultaneous
    // arrivals, which is where the priority encoder matters.
    cp_irq_fast_id: coverpoint irq_fast_i iff (normal_sample) {
      wildcard bins f0  = {15'b??????????????1};
      wildcard bins f1  = {15'b?????????????1?};
      wildcard bins f2  = {15'b????????????1??};
      wildcard bins f3  = {15'b???????????1???};
      wildcard bins f4  = {15'b??????????1????};
      wildcard bins f5  = {15'b?????????1?????};
      wildcard bins f6  = {15'b????????1??????};
      wildcard bins f7  = {15'b???????1???????};
      wildcard bins f8  = {15'b??????1????????};
      wildcard bins f9  = {15'b?????1?????????};
      wildcard bins f10 = {15'b????1??????????};
      wildcard bins f11 = {15'b???1???????????};
      wildcard bins f12 = {15'b??1????????????};
      wildcard bins f13 = {15'b?1?????????????};
      wildcard bins f14 = {15'b1??????????????};
      bins none = {15'h0};
    }
    cp_irq_fast_count: coverpoint $countones(irq_fast_i) iff (normal_sample) {
      bins none  = {0};
      bins one   = {1};
      bins two   = {2};
      bins many  = {[3:15]};
    }
    // Several interrupt classes pending at once exercises the m-mode
    // priority order (external > software > timer > fast).
    cp_irq_class_count: coverpoint $countones({irq_external_i, irq_software_i,
                                               irq_timer_i, |irq_fast_i})
        iff (normal_sample) {
      bins none = {0};
      bins one  = {1};
      bins two  = {2};
      bins many = {[3:4]};
    }

    cp_debug_req: coverpoint debug_req_i iff (normal_sample);
    // A debug request arriving at the same time as an interrupt is the
    // arbitration case in issuer.sv:719-744.
    cp_dbg_and_irq: coverpoint (debug_req_i &
                                (irq_external_i | irq_software_i |
                                 irq_timer_i | (|irq_fast_i))) iff (normal_sample) {
      bins hit = {1'b1};
    }

    cp_fatal_err: coverpoint {rst_ni, cheri_fatal_err_o}
        iff (!normal_sample && cheri_active) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins reset_clear = {2'b00};
      bins quiet = {2'b10};
      bins fatal = {2'b11};
      bins raised = (2'b10 => 2'b11);
      bins sticky = (2'b11 => 2'b11);
      bins reset_after_fatal = (2'b11 => 2'b00);
    }
  endgroup

  cg_ma_top u_cg_ma_top = new();

  always @(posedge clk_i)
    if (rst_ni) u_cg_ma_top.sample(1'b1);

  // cs_registers.gen_scr latches invalid-MTCC trap entry until external reset;
  // gen_no_scr ties the output low. No assertions infer unavailable CSR inputs.
  // Sample fatal/reset after NBA updates without resampling the rising-edge points.
  always @(negedge clk_i)
    if (CHERIoTEn) u_cg_ma_top.sample(1'b0);

`endif  // KUDU_FCOV_OFF

endmodule
`endif  // KUDU_FCOV_BUS_TIMING_ONLY

// In-order response monitor. A grant is accepted only with req_i. Responses
// consume the oldest accepted request, including during simultaneous grants.
// Delay is EXTRA wait: a next-cycle response has delay 0. A response on its
// own grant cycle also has delay 0, distinguished by resp_same_cycle_o.
// Outputs are registered together for sampling at the following clock edge.
module kudu_fcov_bus_timing #(
  parameter int unsigned MaxPending = 64,
  parameter int unsigned MetaW = 1
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             req_i,
  input  logic             gnt_i,
  input  logic             rvalid_i,
  input  logic [MetaW-1:0] meta_i,
  output logic             gnt_ev_o,
  output logic [63:0]      gnt_delay_o,
  output logic             resp_ev_o,
  output logic [63:0]      resp_delay_o,
  output logic             resp_same_cycle_o,
  output logic [MetaW-1:0] resp_meta_o
);

`ifndef KUDU_FCOV_OFF
  logic [63:0] timestamps [MaxPending];
  logic [MetaW-1:0] metadata [MaxPending];
  logic [63:0] cycle_q, grant_wait_q;
  int unsigned head_q, tail_q, count_q;
  logic accept, pop, push, bypass;

  assign accept = req_i && gnt_i;
  assign pop = rvalid_i && (count_q != 0);
  assign bypass = rvalid_i && (count_q == 0) && accept;
  assign push = accept && !bypass;

  initial begin
    if (MaxPending == 0 || MetaW == 0)
      $fatal(1, "FCOV timing: queue depth and metadata width must be positive");
  end

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cycle_q <= '0;
      grant_wait_q <= '0;
      head_q <= 0;
      tail_q <= 0;
      count_q <= 0;
      gnt_ev_o <= 1'b0;
      gnt_delay_o <= '0;
      resp_ev_o <= 1'b0;
      resp_delay_o <= '0;
      resp_same_cycle_o <= 1'b0;
      resp_meta_o <= '0;
    end else begin
      // Never silently wrap a timestamp, truncate a delay, drop a response,
      // or discard an accepted request when the monitor's capacity is exceeded.
      if (&cycle_q)
        $fatal(1, "FCOV timing: timestamp overflow");
      if (req_i && !gnt_i && (&grant_wait_q))
        $fatal(1, "FCOV timing: grant delay overflow");
      if (rvalid_i && count_q == 0 && !accept)
        $fatal(1, "FCOV timing: response without accepted request");
      if (push && !pop && count_q == MaxPending)
        $fatal(1, "FCOV timing: pending queue overflow (%0d)", MaxPending);

      cycle_q <= cycle_q + 64'd1;
      gnt_ev_o <= accept;
      resp_ev_o <= rvalid_i;
      resp_same_cycle_o <= bypass;
      // A cancelled request must not add wait to the next transaction.
      if (!req_i || accept)
        grant_wait_q <= '0;
      else
        grant_wait_q <= grant_wait_q + 64'd1;
      if (accept)
        gnt_delay_o <= grant_wait_q;

      if (pop) begin
        resp_delay_o <= cycle_q - timestamps[head_q] - 64'd1;
        resp_meta_o <= metadata[head_q];
        head_q <= (head_q == MaxPending - 1) ? 0 : head_q + 1;
      end else if (bypass) begin
        resp_delay_o <= '0;
        resp_meta_o <= meta_i;
      end
      if (push) begin
        timestamps[tail_q] <= cycle_q;
        metadata[tail_q] <= meta_i;
        tail_q <= (tail_q == MaxPending - 1) ? 0 : tail_q + 1;
      end
      case ({push, pop})
        2'b10: count_q <= count_q + 1;
        2'b01: count_q <= count_q - 1;
        default: ;
      endcase
    end
  end
`endif
endmodule

`ifndef KUDU_FCOV_BUS_TIMING_ONLY
// ============================================================================
// kudu_sva_top -- SVA properties for the scoreboard, register-file write-back
// and commit-flush wiring in rtl/kudu_top.sv. Bound to kudu_top as
// u_fcov_sva_top. Ports are kudu_top nets connected through .*; the scoreboard
// FIFO, issuer FSM and register array are read through hierarchical references
// to fixed (non-generate) instances.
// ============================================================================
module kudu_sva_top
  import super_pkg::*;
#(
  parameter bit CHERIoTEn = 1'b0
) (
  input logic             clk_i,
  input logic             rst_ni,
  input logic             cheri_pmode_i,

  input logic             cmt_flush,
  input logic             cmt_err,

  input logic [1:0]       sbdfifo_wr_valid,
  input logic [1:0]       sbdfifo_wr_rdy,
  input logic [1:0]       sbdfifo_rd_valid,

  input logic             alupl0_valid,
  input logic             alupl1_valid,
  input logic             lspl_valid,
  input logic             multpl_valid,

  input logic             rf_we0,
  input logic             rf_we1,
  input logic             rf_we2,
  input logic [4:0]       rf_waddr0,
  input logic [4:0]       rf_waddr1,
  input logic [4:0]       rf_waddr2,
  input logic [RegW-1:0]  rf_wdata0,
  input logic [RegW-1:0]  rf_wdata1,
  input logic [RegW-1:0]  rf_wdata2,
  input rf_raddr2_t       rf_raddr2_p0,
  input rf_raddr2_t       rf_raddr2_p1,
  input rf_rdata2_t       rf_rdata2_p0,
  input rf_rdata2_t       rf_rdata2_p1,

  input logic             trvk_en,
  input logic             trvk_clrtag,
  input logic [4:0]       trvk_addr
);

`ifndef KUDU_FCOV_OFF

  localparam int unsigned SbdDepth = 8;     // kudu_top.sv:392
  localparam int unsigned SbdW     = $bits(sbd_fifo_t);

  // ---- scoreboard contents: which pipelines have an outstanding entry -------
  logic [SbdW-1:0] sbd_mem [SbdDepth];
  logic [3:0]      sbd_wr_ptr, sbd_rd_ptr, sbd_cnt;
  logic [4:0]      sbd_has_pl;

  for (genvar i = 0; i < SbdDepth; i++) begin : g_sbd_mem
    assign sbd_mem[i] = kudu_top.sbd_fifo_i.fifo_mem[i];
  end
  assign sbd_wr_ptr = kudu_top.sbd_fifo_i.wr_ptr_q;
  assign sbd_rd_ptr = kudu_top.sbd_fifo_i.rd_ptr_q;
  assign sbd_cnt    = sbd_wr_ptr - sbd_rd_ptr;

  always_comb begin
    sbd_fifo_t e;
    logic [2:0] idx;
    sbd_has_pl = 5'h0;
    for (int unsigned k = 0; k < SbdDepth; k++) begin
      idx = sbd_rd_ptr[2:0] + k[2:0];
      e   = sbd_fifo_t'(sbd_mem[idx]);
      if (k < 32'(sbd_cnt)) sbd_has_pl = sbd_has_pl | e.pl;
    end
  end

  // ---- register file write check (one pending check per port) --------------
  // regfile.sv:55-63: highest-priority port (2 > 1 > 0) wins; trvk may clear the tag.
  logic [2:0]            rfw_vld_d, rfw_vld_q;
  logic [4:0]            rfw_addr_q [3];
  logic [RegW-1:0]       rfw_data_q [3];
  logic [2:0]            rfw_clr_q;
  logic [4:0]            rfw_addr_d [3];
  logic [RegW-1:0]       rfw_data_d [3];
  logic [RegW-1:0]       rfw_cur [3];
  logic [RegW-1:0]       rfw_mask [3];
  logic                  trvk_clr_act;

  assign trvk_clr_act = CHERIoTEn & trvk_en & trvk_clrtag;
  assign rfw_addr_d[0] = rf_waddr0;
  assign rfw_addr_d[1] = rf_waddr1;
  assign rfw_addr_d[2] = rf_waddr2;
  assign rfw_data_d[0] = rf_wdata0;
  assign rfw_data_d[1] = rf_wdata1;
  assign rfw_data_d[2] = rf_wdata2;
  assign rfw_vld_d[2]  = rf_we2 && (rf_waddr2 != 5'h0);
  assign rfw_vld_d[1]  = rf_we1 && (rf_waddr1 != 5'h0) && !(rf_we2 && (rf_waddr2 == rf_waddr1));
  assign rfw_vld_d[0]  = rf_we0 && (rf_waddr0 != 5'h0) && !(rf_we2 && (rf_waddr2 == rf_waddr0)) &&
                         !(rf_we1 && (rf_waddr1 == rf_waddr0));

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rfw_vld_q <= 3'b000;
      rfw_clr_q <= 3'b000;
      for (int p = 0; p < 3; p++) begin
        rfw_addr_q[p] <= 5'h0;
        rfw_data_q[p] <= '0;
      end
    end else begin
      rfw_vld_q <= rfw_vld_d;
      for (int p = 0; p < 3; p++) begin
        rfw_addr_q[p] <= rfw_addr_d[p];
        rfw_data_q[p] <= rfw_data_d[p];
        rfw_clr_q[p]  <= trvk_clr_act && (trvk_addr == rfw_addr_d[p]);
      end
    end
  end

  for (genvar p = 0; p < 3; p++) begin : g_rfw
    assign rfw_cur[p]  = (rfw_addr_q[p] == 5'h0) ? '0 : kudu_top.regfile_i.rf_reg_q[rfw_addr_q[p]];
    assign rfw_mask[p] = rfw_clr_q[p] ? {1'b0, {(RegW-1){1'b1}}} : {RegW{1'b1}};
  end

  // ---- assertions ----------------------------------------------------------

  // issuer.sv:349-351 + issuer.sv:749-772: the issuer only writes the scoreboard when it has room (dual_fifo would drop the entry).
  AssertSbdWrHasRoom: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ((sbdfifo_wr_valid & ~sbdfifo_wr_rdy) == 2'b00) && (sbdfifo_wr_valid != 2'b10))
    else $error("SVA: scoreboard write without room");

  // issuer.sv:350-354: a cmplx scoreboard write must not coincide with a normal issue (wdata0 mux would drop one).
  AssertSbdNoCmplxCollision: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.cmplx_sbd_wr_i |-> (kudu_top.issuer_i.ir_fifo_wr == 2'b00))
    else $error("SVA: cmplx and normal scoreboard writes in the same cycle");

  // committer.sv:84-110: every valid pipeline result has an outstanding scoreboard entry targeting that pipeline.
  AssertNoOrphanPlOutput: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (!alupl0_valid || sbd_has_pl[1]) && (!alupl1_valid || sbd_has_pl[2]) &&
    (!lspl_valid   || sbd_has_pl[3]) && (!multpl_valid || sbd_has_pl[4]))
    else $error("SVA: pipeline result without a scoreboard entry");

  // dual_fifo.sv:144-149: scoreboard occupancy never exceeds its depth.
  AssertSbdCountBound: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sbd_cnt <= SbdDepth)
    else $error("SVA: scoreboard occupancy out of range");

  // issuer.sv:546-548,749-772: cmt_flush is only asserted to service a pending commit error.
  AssertFlushNeedsErr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cmt_flush |-> cmt_err)
    else $error("SVA: commit flush without a commit error");

  // issuer.sv:546-597: a commit error is serviced in the next cycle (issuer must be in a state that checks cmt_err_i).
  AssertCmtErrFlushNext: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cmt_err && !cmt_flush |=> cmt_flush)
    else $error("SVA: pending commit error not flushed in the next cycle");

  // kudu_top.sv cmt_flush -> sbd_fifo_i / pipelines: a flush leaves no scoreboard entry and no pipeline result behind.
  AssertFlushDrains: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cmt_flush |=> (sbdfifo_rd_valid == 2'b00) && !alupl0_valid && !alupl1_valid && !lspl_valid && !multpl_valid)
    else $error("SVA: scoreboard or pipeline output survives a commit flush");

  // regfile.sv:68-85: x0 always reads as zero on every read port.
  AssertRfX0ReadsZero: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ((rf_raddr2_p0.a0 != 5'h0) || (rf_rdata2_p0.d0 == '0)) &&
    ((rf_raddr2_p0.a1 != 5'h0) || (rf_rdata2_p0.d1 == '0)) &&
    ((rf_raddr2_p1.a0 != 5'h0) || (rf_rdata2_p1.d0 == '0)) &&
    ((rf_raddr2_p1.a1 != 5'h0) || (rf_rdata2_p1.d1 == '0)))
    else $error("SVA: x0 read returned non-zero");

  // regfile.sv:55-63: the winning write (youngest, by port priority) lands in the register, tag aside if trvk cleared it.
  AssertRfWriteLands: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_fcov_pkg::sva_xok((!rfw_vld_q[0] || ((rfw_cur[0] & rfw_mask[0]) == (rfw_data_q[0] & rfw_mask[0]))) &&
    (!rfw_vld_q[1] || ((rfw_cur[1] & rfw_mask[1]) == (rfw_data_q[1] & rfw_mask[1]))) &&
    (!rfw_vld_q[2] || ((rfw_cur[2] & rfw_mask[2]) == (rfw_data_q[2] & rfw_mask[2])))))
    else $error("SVA: register file write lost or overridden by an older write");

  if (CHERIoTEn) begin : g_cheri
    // regfile.sv:52-64 (x0 excluded, it has no flop): a trvk tag clear must only hit a register whose same-cycle tagged
    // write comes from the LS port (the CLC itself); a younger ALU/mult writer would lose its tag.
    AssertTrvkClrNoYoungerTaggedWrite: assert property (@(posedge clk_i) disable iff (!rst_ni)
      trvk_clr_act && (trvk_addr != 5'd0) |->
        !(rf_we0 && (rf_waddr0 == trvk_addr) && rf_wdata0[RegW-1]) &&
        !(rf_we1 && (rf_waddr1 == trvk_addr) && rf_wdata1[RegW-1]))
      else $error("SVA: trvk tag clear hits a same-cycle tagged ALU/mult write");

    // With pmode 0 the core is a plain RV32 core: no register write carries a capability tag.
    AssertRfNoTagPmode0: assert property (@(posedge clk_i) disable iff (!rst_ni)
      !cheri_pmode_i |-> !(rf_we0 && rf_wdata0[RegW-1]) && !(rf_we1 && rf_wdata1[RegW-1]) &&
                         !(rf_we2 && rf_wdata2[RegW-1]))
      else $error("SVA: tagged register write with cheri_pmode_i = 0");
  end

`endif  // KUDU_FCOV_OFF

endmodule
`endif  // KUDU_FCOV_BUS_TIMING_ONLY

// ============================================================================
// kudu_sva_fifo_ref -- interface-level reference model shared by the FIFO
// checkers below. Accepted transfers follow the dual-port convention of
// dual_fifo/stage_fifo: two if both valid and both ready, else one if bit 0 is
// valid and ready. Single-port FIFOs tie bit 1 low. Data is XOR-folded to at
// most 16 bits to keep the shadow state small for formal.
// ============================================================================
module kudu_sva_fifo_ref #(
  parameter int unsigned Depth     = 2,
  parameter int unsigned Width     = 32,
  parameter bit          WrThrough = 1'b0,
  parameter bit          Dual      = 1'b1,
  localparam int unsigned FoldW    = (Width < 16) ? Width : 16,
  localparam int unsigned IdxW     = (Depth > 1) ? $clog2(Depth) : 1,
  localparam int unsigned CntW     = $clog2(Depth) + 2
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             flush_i,
  input  logic [1:0]       wr_valid,
  input  logic [1:0]       wr_rdy,
  input  logic [Width-1:0] wr_d0,
  input  logic [Width-1:0] wr_d1,
  input  logic [1:0]       rd_valid,
  input  logic [1:0]       rd_rdy,
  input  logic [Width-1:0] rd_d0,
  input  logic [Width-1:0] rd_d1,
  output logic [CntW-1:0]  cnt_o,
  // Simulation only: an X handshake was seen since the last flush. X in a
  // handshake (fetched debug-ROM/unloaded words) can leave the RTL pointers
  // inconsistent in simulation; the checks pause until the next flush.
  // Checks use $sampled(x_o): on the flush edge x_q is already cleared when
  // disable iff is evaluated, while the asserted values are still pre-flush.
  output logic             x_o
);

`ifndef KUDU_FCOV_OFF

  function automatic logic [FoldW-1:0] fold(logic [Width-1:0] d);
    logic [FoldW-1:0] f;
    f = '0;
    for (int unsigned b = 0; b < Width; b++) f[b % FoldW] = f[b % FoldW] ^ d[b];
    return f;
  endfunction

  localparam logic [IdxW-1:0] IdxOne = 1;
  logic [FoldW-1:0] mem_q [Depth];
  logic [IdxW-1:0]  wp_q, rp_q, wp_p1, rp_p1;
  logic [CntW-1:0]  cnt_q, vis;
  logic [1:0]       wn, rn;
  logic [FoldW-1:0] exp0, exp1;
  logic             x_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)      x_q <= 1'b0;
    else if (flush_i) x_q <= 1'b0;
    else if (x_o)     x_q <= 1'b1;
  end
  assign x_o = x_q | $isunknown({wr_valid, wr_rdy, rd_valid, rd_rdy});

  assign wn = ((wr_valid == 2'b11) && (wr_rdy == 2'b11)) ? 2'd2 : (wr_valid[0] && wr_rdy[0]) ? 2'd1 : 2'd0;
  assign rn = ((rd_valid == 2'b11) && (rd_rdy == 2'b11)) ? 2'd2 : (rd_valid[0] && rd_rdy[0]) ? 2'd1 : 2'd0;
  // Depth is a power of two, so IdxW-bit pointers wrap at Depth.
  assign wp_p1 = wp_q + IdxOne;
  assign rp_p1 = rp_q + IdxOne;
  assign cnt_o = cnt_q;
  assign vis   = cnt_q + (WrThrough ? CntW'(wr_valid[0]) + CntW'(wr_valid[1]) : CntW'(0));

  assign exp0 = (cnt_q > 0) ? mem_q[rp_q] : fold(wr_d0);
  assign exp1 = (cnt_q > 1) ? mem_q[rp_p1] : (cnt_q == 1) ? fold(wr_d0) : fold(wr_d1);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      wp_q  <= '0;
      rp_q  <= '0;
      cnt_q <= '0;
      for (int unsigned i = 0; i < Depth; i++) mem_q[i] <= '0;
    end else if (flush_i) begin
      wp_q  <= '0;
      rp_q  <= '0;
      cnt_q <= '0;
    end else begin
      cnt_q <= cnt_q + CntW'(wn) - CntW'(rn);
      wp_q  <= (wn == 2'd2) ? wp_p1 + IdxOne : (wn == 2'd1) ? wp_p1 : wp_q;
      rp_q  <= (rn == 2'd2) ? rp_p1 + IdxOne : (rn == 2'd1) ? rp_p1 : rp_q;
      if (wn != 2'd0) mem_q[wp_q]  <= fold(wr_d0);
      if (wn == 2'd2) mem_q[wp_p1] <= fold(wr_d1);
    end
  end

  // Handshake encodings: bit 1 never without bit 0 (dual_fifo.sv:191-199, stage_fifo.sv FORMAL block).
  AssertFifoIfLegal: assert property (@(posedge clk_i) disable iff (!rst_ni || $sampled(x_o))
    (wr_valid != 2'b10) && (rd_rdy != 2'b10) && (wr_rdy != 2'b10) && (rd_valid != 2'b10))
    else $error("SVA: FIFO handshake encoding 2'b10");

  // No read beyond the stored (plus written-through) entries.
  AssertFifoNoUnderflow: assert property (@(posedge clk_i) disable iff (!rst_ni || $sampled(x_o))
    kudu_fcov_pkg::sva_xok(CntW'(rn) <= cnt_q + (WrThrough ? CntW'(wn) : CntW'(0))))
    else $error("SVA: FIFO read underflow");

  // No accepted write beyond Depth entries (after this cycle's reads).
  AssertFifoNoOverflow: assert property (@(posedge clk_i) disable iff (!rst_ni || $sampled(x_o))
    kudu_fcov_pkg::sva_xok((cnt_q + CntW'(wn)) <= (CntW'(Depth) + CntW'(rn))))
    else $error("SVA: FIFO overflow");

  // rd_valid reflects exactly the visible entries (stored, plus write-through inputs).
  AssertFifoRdValid: assert property (@(posedge clk_i) disable iff (!rst_ni || $sampled(x_o))
    (rd_valid[0] == (vis > 0)) && (!Dual || (rd_valid[1] == (vis > 1))))
    else $error("SVA: FIFO rd_valid does not match occupancy");

  // Head data is the oldest accepted write (FIFO order, flush discards everything).
  AssertFifoRdData0: assert property (@(posedge clk_i) disable iff (!rst_ni || $sampled(x_o))
    rd_valid[0] |-> kudu_fcov_pkg::sva_xok((fold(rd_d0) == exp0)))
    else $error("SVA: FIFO head data is not the oldest entry");

  if (Dual) begin : g_dual
    // Second output is the second-oldest entry.
    AssertFifoRdData1: assert property (@(posedge clk_i) disable iff (!rst_ni || $sampled(x_o))
      rd_valid[1] |-> kudu_fcov_pkg::sva_xok((fold(rd_d1) == exp1)))
      else $error("SVA: FIFO second output is not the second-oldest entry");
  end

`else
  assign cnt_o = '0;
  assign x_o   = 1'b0;
`endif  // KUDU_FCOV_OFF

endmodule

// dual_fifo checker, bound by module name to every dual_fifo instance
// (kudu_top sbd_fifo_i; ir_stage s0_fifo when !StageBypass[1]).
module kudu_sva_dual_fifo #(
  parameter int unsigned Depth     = 2,
  parameter int unsigned Width     = 32,
  parameter bit          PplRead   = 1'b0,
  parameter bit          WrThrough = 1'b0,
  localparam int unsigned PtrW     = $clog2(Depth) + 1
) (
  input logic             clk_i,
  input logic             rst_ni,
  input logic             flush_i,
  input logic [1:0]       wr_valid_i,
  input logic [Width-1:0] wr_data0_i,
  input logic [Width-1:0] wr_data1_i,
  input logic [1:0]       wr_rdy_o,
  input logic [1:0]       rd_rdy_i,
  input logic [1:0]       rd_valid_o,
  input logic [Width-1:0] rd_data0_o,
  input logic [Width-1:0] rd_data1_o,
  input logic [PtrW-1:0]  wr_ptr_q,
  input logic [PtrW-1:0]  rd_ptr_q,
  input logic [1:0]       fill_status_q,
  input logic [1:0]       room_status_q
);

`ifndef KUDU_FCOV_OFF
  localparam int unsigned CntW = $clog2(Depth) + 2;
  logic [CntW-1:0] ref_cnt;
  logic ref_x;
  logic [PtrW-1:0] cnt;

  assign cnt = wr_ptr_q - rd_ptr_q;

  kudu_sva_fifo_ref #(.Depth(Depth), .Width(Width), .WrThrough(WrThrough), .Dual(1'b1)) u_ref (
    .clk_i, .rst_ni, .flush_i,
    .wr_valid (wr_valid_i), .wr_rdy (wr_rdy_o), .wr_d0 (wr_data0_i), .wr_d1 (wr_data1_i),
    .rd_valid (rd_valid_o), .rd_rdy (rd_rdy_i), .rd_d0 (rd_data0_o), .rd_d1 (rd_data1_o),
    .cnt_o    (ref_cnt), .x_o (ref_x));

  // dual_fifo.sv:144-149: the registered fill/room flags agree with the pointer difference.
  AssertDfStatus: assert property (@(posedge clk_i) disable iff (!rst_ni || $sampled(ref_x))
    (cnt <= Depth) &&
    (fill_status_q == {cnt > 1, cnt > 0}) &&
    (room_status_q == {cnt < (Depth - 1), cnt < Depth}))
    else $error("SVA: dual_fifo status flags inconsistent with pointers");

  // dual_fifo.sv:131-149: internal pointer occupancy tracks the interface-level reference count.
  AssertDfRefCount: assert property (@(posedge clk_i) disable iff (!rst_ni || $sampled(ref_x))
    CntW'(cnt) == ref_cnt)
    else $error("SVA: dual_fifo occupancy differs from accepted handshakes");
`endif
endmodule

// stage_fifo checker (2-entry), bound to every stage_fifo instance in ir_stage.
module kudu_sva_stage_fifo #(
  parameter int unsigned Width   = 32,
  parameter bit          PeekMem = 1'b0
) (
  input logic             clk_i,
  input logic             rst_ni,
  input logic             flush_i,
  input logic             wr_hold_i,
  input logic [1:0]       wr_valid_i,
  input logic [Width-1:0] wr_data0_i,
  input logic [Width-1:0] wr_data1_i,
  input logic [1:0]       wr_rdy_o,
  input logic [1:0]       rd_rdy_i,
  input logic [1:0]       rd_valid_o,
  input logic [Width-1:0] rd_data0_o,
  input logic [Width-1:0] rd_data1_o,
  input logic             wr_ptr_q,
  input logic             rd_ptr_q,
  input logic             full_stat_q
);

`ifndef KUDU_FCOV_OFF
  logic [2:0] ref_cnt;
  logic ref_x;
  logic [1:0] cnt;

  assign cnt = full_stat_q ? 2'd2 : (wr_ptr_q != rd_ptr_q) ? 2'd1 : 2'd0;

  kudu_sva_fifo_ref #(.Depth(2), .Width(Width), .WrThrough(1'b0), .Dual(1'b1)) u_ref (
    .clk_i, .rst_ni, .flush_i,
    .wr_valid (wr_valid_i & {2{~wr_hold_i}}), .wr_rdy (wr_rdy_o),
    .wr_d0 (wr_data0_i), .wr_d1 (wr_data1_i),
    .rd_valid (rd_valid_o), .rd_rdy (rd_rdy_i), .rd_d0 (rd_data0_o), .rd_d1 (rd_data1_o),
    .cnt_o    (ref_cnt), .x_o (ref_x));

  // stage_fifo.sv:83-85: full means the pointers are equal.
  AssertSfFullPtr: assert property (@(posedge clk_i) disable iff (!rst_ni || $sampled(ref_x))
    full_stat_q |-> kudu_fcov_pkg::sva_xok((wr_ptr_q == rd_ptr_q)))
    else $error("SVA: stage_fifo full with unequal pointers");

  // stage_fifo.sv:83-85,128-136: internal occupancy tracks the interface-level reference count.
  AssertSfRefCount: assert property (@(posedge clk_i) disable iff (!rst_ni || $sampled(ref_x))
    kudu_fcov_pkg::sva_xok(3'(cnt) == ref_cnt))
    else $error("SVA: stage_fifo occupancy differs from accepted handshakes");
`endif
endmodule

// wt_fifo checker (write-through, single port), bound to every wt_fifo instance
// (ls_pipeline wb_fifo_i and rvfi_fifo_i).
module kudu_sva_wt_fifo #(
  parameter int unsigned Depth = 2,
  parameter int unsigned Width = 32,
  localparam int unsigned PtrW = $clog2(Depth) + 1
) (
  input logic             clk_i,
  input logic             rst_ni,
  input logic             flush_i,
  input logic             wr_valid_i,
  input logic [Width-1:0] wr_data_i,
  input logic             wr_rdy_o,
  input logic             rd_rdy_i,
  input logic             rd_valid_o,
  input logic [Width-1:0] rd_data_o,
  input logic [PtrW-1:0]  wr_ptr_q,
  input logic [PtrW-1:0]  rd_ptr_q
`ifdef KUDU_FV_HELPERS
  ,
  // FV helpers only (AssertHelpWt* below)
  input logic [Width-1:0] fifo_mem [Depth]
`endif
);

`ifndef KUDU_FCOV_OFF
  localparam int unsigned CntW = $clog2(Depth) + 2;
  logic [CntW-1:0] ref_cnt;
  logic ref_x;
  logic [PtrW-1:0] occ;

  assign occ = wr_ptr_q - rd_ptr_q;

  kudu_sva_fifo_ref #(.Depth(Depth), .Width(Width), .WrThrough(1'b1), .Dual(1'b0)) u_ref (
    .clk_i, .rst_ni, .flush_i,
    .wr_valid ({1'b0, wr_valid_i}), .wr_rdy ({1'b0, wr_rdy_o}),
    .wr_d0 (wr_data_i), .wr_d1 ('0),
    .rd_valid ({1'b0, rd_valid_o}), .rd_rdy ({1'b0, rd_rdy_i}), .rd_d0 (rd_data_o), .rd_d1 ('0),
    .cnt_o    (ref_cnt), .x_o (ref_x));

  // ls_pipeline.sv leaves wr_rdy_o open ("should never get full"): a write is never dropped.
  AssertWtNoDropWrite: assert property (@(posedge clk_i) disable iff (!rst_ni || $sampled(ref_x))
    wr_valid_i |-> wr_rdy_o)
    else $error("SVA: wt_fifo write dropped while full");

  // wt_fifo.sv:47-48: internal occupancy tracks the interface-level reference count.
  AssertWtRefCount: assert property (@(posedge clk_i) disable iff (!rst_ni || $sampled(ref_x))
    CntW'(occ) == ref_cnt)
    else $error("SVA: wt_fifo occupancy differs from accepted handshakes");

  // ==========================================================================
  // FV helper lemmas: formal only, compiled only with +define+KUDU_FV_HELPERS.
  // Unlike the kudu_fvh_* modules these stay inside this checker: they relate
  // this checker's own u_ref (and occ) to the RTL state of the same wt_fifo
  // instance, which exists only inside this module, and keeping them here
  // keeps their names (...u_fcov_sva_wt_fifo.AssertHelpWt*) unchanged.
  // Supports the wb/rvfi wt_fifo u_ref.AssertFifoRdData0 targets (with
  // kudu_fvh_backend).
  // ==========================================================================
`ifdef KUDU_FV_HELPERS
  // ---- FV helpers (AssertHelpWt*): reference model state == RTL state ----
  localparam int unsigned HFoldW = (Width < 16) ? Width : 16;
  localparam int unsigned HIdxW  = PtrW - 1;
  function automatic logic [HFoldW-1:0] hfold(logic [Width-1:0] d);
    logic [HFoldW-1:0] f;
    f = '0;
    for (int unsigned b = 0; b < Width; b++) f[b % HFoldW] = f[b % HFoldW] ^ d[b];
    return f;
  endfunction
  // ref read pointer == RTL read pointer (memory index bits)
  AssertHelpWtRp: assert property (@(posedge clk_i) disable iff (!rst_ni)
    u_ref.rp_q == rd_ptr_q[HIdxW-1:0]);
  // ref write pointer == RTL write pointer (memory index bits)
  AssertHelpWtWp: assert property (@(posedge clk_i) disable iff (!rst_ni)
    u_ref.wp_q == wr_ptr_q[HIdxW-1:0]);
  // RTL occupancy never exceeds Depth
  AssertHelpWtOccBound: assert property (@(posedge clk_i) disable iff (!rst_ni)
    occ <= PtrW'(Depth));
  for (genvar j = 0; j < Depth; j++) begin : g_help_mem
    // every occupied slot holds the folded RTL data
    AssertHelpWtMem: assert property (@(posedge clk_i) disable iff (!rst_ni)
      (PtrW'(HIdxW'(HIdxW'(j) - rd_ptr_q[HIdxW-1:0])) < occ) |-> (u_ref.mem_q[j] == hfold(fifo_mem[j])));
  end
`endif  // KUDU_FV_HELPERS
`endif
endmodule

// waw_tracking_fifo checker, bound to every instance (ls_pipeline waw_fifo_i,
// dcache waw_fifo_i). Bit 5 is mutated in place by WAW matches, so the reference
// model checks only the register address bits [4:0].
module kudu_sva_waw_fifo #(
  parameter int unsigned Depth     = 8,
  parameter int unsigned Width     = 6,
  parameter bit          WrThrough = 1'b0,
  localparam int unsigned PtrW     = $clog2(Depth) + 1
) (
  input logic             clk_i,
  input logic             rst_ni,
  input logic             flush_i,
  input logic             wr_valid_i,
  input logic [Width-1:0] wr_data_i,
  input logic             wr_rdy_o,
  input logic             rd_rdy_i,
  input logic             rd_valid_o,
  input logic [Width-1:0] rd_data_o,
  input logic [1:0]       waw_req_i,
  input logic [4:0]       waw_addr0_i,
  input logic [4:0]       waw_addr1_i,
  input logic [PtrW-1:0]  wr_ptr_q,
  input logic [PtrW-1:0]  rd_ptr_q,
  input logic             fifo_empty,
  input logic             waw_match_head
);

`ifndef KUDU_FCOV_OFF
  localparam int unsigned CntW = $clog2(Depth) + 2;
  logic [CntW-1:0] ref_cnt;
  logic ref_x;
  logic [PtrW-1:0] occ;

  assign occ = wr_ptr_q - rd_ptr_q;

  kudu_sva_fifo_ref #(.Depth(Depth), .Width(5), .WrThrough(WrThrough), .Dual(1'b0)) u_ref (
    .clk_i, .rst_ni, .flush_i,
    .wr_valid ({1'b0, wr_valid_i}), .wr_rdy ({1'b0, wr_rdy_o}),
    .wr_d0 (wr_data_i[4:0]), .wr_d1 (5'h0),
    .rd_valid ({1'b0, rd_valid_o}), .rd_rdy ({1'b0, rd_rdy_i}), .rd_d0 (rd_data_o[4:0]), .rd_d1 (5'h0),
    .cnt_o    (ref_cnt), .x_o (ref_x));

  // ls_pipeline.sv:355-357 / dcache: callers rely on the FIFO never being full on a write.
  AssertWawNoDropWrite: assert property (@(posedge clk_i) disable iff (!rst_ni || $sampled(ref_x))
    wr_valid_i |-> wr_rdy_o)
    else $error("SVA: waw_tracking_fifo write dropped while full");

  // waw_tracking_fifo.sv:47-48: internal occupancy tracks the interface-level reference count.
  AssertWawRefCount: assert property (@(posedge clk_i) disable iff (!rst_ni || $sampled(ref_x))
    CntW'(occ) == ref_cnt)
    else $error("SVA: waw_tracking_fifo occupancy differs from accepted handshakes");

  if (Width > 5) begin : g_waw_bit
    // waw_tracking_fifo.sv:94-104: a younger writer of the same rd clears the head's
    // "still latest writer" bit, and it stays clear while the head is not popped.
    AssertWawHeadClear: assert property (@(posedge clk_i) disable iff (!rst_ni || $sampled(ref_x))
      !flush_i && !fifo_empty && waw_match_head && !(rd_valid_o && rd_rdy_i) |=> !rd_data_o[5])
      else $error("SVA: WAW match did not clear the head's reservation bit");
  end
`endif
endmodule
