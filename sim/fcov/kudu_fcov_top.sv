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
  input logic             data_sc_resp_i,

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
  logic data_sc_resp_q, data_rtag_q, data_resp_err_q;
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
      data_sc_resp_q <= 1'b0;
      data_rtag_q <= 1'b0;
      data_resp_err_q <= 1'b0;
    end else if (data_rvalid_i) begin
      data_sc_resp_q <= data_sc_resp_i;
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
    cp_sc_resp: coverpoint data_sc_resp_q
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
