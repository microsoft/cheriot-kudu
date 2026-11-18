// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Synthetic boundary fixtures instantiate the production monitors unchanged.
// WB storage is the real write-through FIFO; other hierarchy supplies controlled
// observations, including deliberately contradictory old/new transactions.
module accuracy_level;
  logic signed [7:0] fifo_level = 0;
  logic fifo_empty = 1, rd_valid = 0, rd_rdy_i = 0, waw_match_head = 0;
  logic [5:0] fifo_head_data = 0;
endmodule

module accuracy_lsif;
  localparam IDLE = 0, DLY0_WGNT = 1, DLY1 = 2, DLY1_WGNT = 3;
  logic [2:0] lsif_fsm_q = IDLE;
  logic lsif_rdy_local = 0, xfr2hold0 = 0, xfr2hold1 = 0;
  logic req_dly_valid = 0, lsu_req_o = 0, lsu_req_done_i = 0;
endmodule

module accuracy_lsu;
  import super_pkg::*;
  lsu_req_info_t lsu_req_info_q = '0;
  pl_out_t lsu_resp_info = '0;
  cheri_pkg::mem_cap_t data_rdata_i = '0;
  logic data_rvalid_i = 0, data_err_i = 0, ls_go = 0, csr_go = 0;
  logic resp_wait = 0, ds_rdy_i = 1, rdata_update = 0, csr_go_q = 0;
  logic csr_cheri_asr_err = 0;
  cheri_pkg::lschk_err_t lschk_err_final = '0;
  logic [5:0] ls_err_cause = 0;
  logic pmp_err_q = 0;
  logic [11:0] csr_addr = 0;
  logic illegal_csr_insn_i = 0, csr_cheri = 0, csr_cheri_always_ok = 0;
  logic pcc_asr_bit = 1, csr_lsu_wr_req_o = 0;
endmodule

module dcache;
  import super_pkg::*;
  logic clk_i = 0, rst_ni = 0, flush_i = 0;
  logic cache_enable_i = 0, lsu_req_i = 0;
  pl_fwd_t fwd_info_o = '0;
  logic [3:0] line_valid = 0, rd_tag_match = 0, wr_tag_match = 0;
  logic cache_rd_hit = 0, cache_rd_match_ok = 0, rd_hit_q = 0;
  logic byp_tag_match = 0, byp_data_good = 0, unaligned_access = 0;
  logic unaligned_access_q = 0;
  logic [3:0] repl_sel = 0, update_valid = 0, update_invalid = 0;
  logic resp_full_word = 0, resp_partial_word = 0, resp_invalidate = 0;
  logic waw_act_match = 0;
  accuracy_level waw_fifo_i();
  logic lsu_req_done_i = 0, lsu_req_q = 0;
  lsu_req_info_t lsu_req_info_i = '0, lsu_req_info_q = '0;
  kudu_fcov_dcache monitor(.*);
  task automatic tick;
    #5; clk_i = 1; #5; clk_i = 0;
  endtask
  task automatic exercise(input int bad);
    tick(); rst_ni = 1;
    if (bad != 0) begin
      case (bad)
        1: update_valid = 4'b0011;
        2: update_valid = 4'b0111;
        3: update_valid = 4'b1111;
        4: update_invalid = 4'b0111;
        5: rd_tag_match = 4'b0011;
        6: wr_tag_match = 4'b0111;
      endcase
      tick();
      return;
    end
    // Low and high endpoints of every automatic 32-bit range. Upper OpW
    // bits are deliberately nonzero on CHERI hardware.
    for (int i = 0; i < 64; i++) begin
      fwd_info_o.valid = 2'b10;
      fwd_info_o.data1 = '1;
      fwd_info_o.data1[31:0] = 32'(i) << 26;
      tick();
      fwd_info_o.data1[31:0] |= 32'h03ffffff;
      tick();
      fwd_info_o.valid = 2'b01;
      tick();
    end
    fwd_info_o = '0;
    // Five actual allocations, then the same selections while idle,
    // disabled, and wholly invalidated. Only the first set may count.
    for (int gate = 0; gate < 4; gate++)
      for (int way = 0; way < 5; way++) begin
        repl_sel = way == 4 ? 0 : (4'b1 << way);
        cache_enable_i = gate != 2;
        update_valid = gate == 1 ? 0 : 1;
        update_invalid = gate == 3 ? 1 : 0;
        tick();
      end
    cache_enable_i = 0; update_valid = 0;
    // All sixteen invalidation masks except the four forbidden triples.
    for (int mask = 0; mask < 16; mask++)
      if ($countones(4'(mask)) != 3) begin
        update_invalid = 4'(mask);
        tick();
      end
    update_invalid = 0;
    // Preserve legal two-write-tag matches.
    wr_tag_match = 3; tick();
    wr_tag_match = 0;
  endtask
endmodule

module ls_pipeline;
  import super_pkg::*;
  import csr_pkg::*;
  import cheri_pkg::*;
`ifdef CHERIoT
  localparam bit CHERIoTEn = 1;
`else
  localparam bit CHERIoTEn = 0;
`endif
  logic clk_i = 0, rst_ni = 0;
  logic us_valid_i = 0, lspl_rdy_o = 0, ds_rdy_i = 0, lspl_valid_o;
  logic flush_i = 0, sel_ira_i = 0, cmplx_lsu_req_valid_i = 0;
  lsu_req_info_t lsu_req_info = '0;
  logic lsu_req = 0, lsu_req_done = 0, lsu_resp_valid = 0, lsu_resp_err = 0;
  pl_out_t lspl_output_o, wb_input = '0;
  logic wb_write = 0, wb_read = 0;
  logic lsu_err_active = 0, resp_err_latched = 0, lr_insn = 0, sc_insn = 0;
  logic data_sc_fail_i = 0, data_req_o = 0, data_gnt_i = 0, data_rvalid_i = 0;
  logic data_we_o = 0, data_err_i = 0, data_is_cap_o = 0;
  logic [3:0] data_be_o = 0, data_amo_flag_o = 0;
  logic [31:0] data_addr_o = 0;
  ls_fsm_e ls_fsm_cs = IDLE;
  logic split_misaligned_access = 0, handle_misaligned_q = 0;
  logic addr_incr_req = 0, lsu_busy = 0, trvk_en_o = 0;
  logic trvk_outstanding_o = 0, tsafe_en_i = 0, debug_mode_i = 0, cheri_pmode_i = 0;
  accuracy_lsif lsu_if_i();
  accuracy_lsu load_store_unit_i();
  accuracy_level waw_fifo_i();
  wt_fifo #(.Depth(4), .Width($bits(pl_out_t))) wb_fifo_i (
    .clk_i, .rst_ni, .flush_i, .wr_valid_i(wb_write), .wr_data_i(wb_input),
    .wr_rdy_o(), .wr_rdy2_o(), .rd_rdy_i(wb_read),
    .rd_valid_o(lspl_valid_o), .rd_data_o(lspl_output_o)
  );
  kudu_fcov_lsu monitor(.*);
  task automatic tick;
    #5; clk_i = 1; #5; clk_i = 0;
  endtask
  task automatic save_mode(input bit mode);
    cheri_pmode_i = mode;
    lsu_if_i.lsif_fsm_q = lsu_if_i.IDLE;
    load_store_unit_i.ls_go = 1;
    tick();
    load_store_unit_i.ls_go = 0;
    if (monitor.resp_cheri_mode !== (CHERIoTEn && mode))
      $fatal(1, "Response provenance capture failed");
  endtask
  task automatic exercise;
    tick(); rst_ni = 1;
    // Exhaust every request guard independently, using the real monitor's
    // delayed/held request mode capture and all three saved-request mux arms.
    for (int path = 1; path <= 4; path++)
      for (int p = 0; p < 512; p++) begin
        lsu_req = 0;
        cheri_pmode_i = p[0];
        lsu_if_i.lsif_rdy_local = 1;
        lsu_if_i.xfr2hold0 = 1;
        tick();
        lsu_if_i.lsif_rdy_local = 0;
        lsu_if_i.xfr2hold0 = 0;
        if (path == 4) begin
          cheri_pmode_i = !p[0];
          lsu_if_i.xfr2hold1 = 1;
          tick();
          lsu_if_i.xfr2hold1 = 0;
        end
        lsu_if_i.lsif_fsm_q = path == 4 ? 3'd3 : 3'(path);
        cheri_pmode_i = p[1];
        lsu_req = p[2];
        lsu_req_info.is_cap = p[3];
        lsu_req_info.is_csr = p[4];
        ls_fsm_cs = p[5] ? WAIT_GNT : IDLE;
        lsu_req_info.lschk_err = '0;
        lsu_req_info.lschk_err.seal = p[6];       // vio_cause_enc -> 5'h03
        lsu_req_info.lschk_err.any_fault = p[6];
        lsu_req_info.is_load = p[7];
        lsu_req_info.cache_ok = p[8];
        #1;
        if (monitor.req_cheri_mode !== (CHERIoTEn && p[0]))
          $fatal(1, "Request provenance mux failed path=%0d pattern=%0d", path, p);
        tick();
      end
    lsu_req = 0; lsu_req_info = '0; ls_fsm_cs = IDLE;
    // Every response guard, including the tagged-only second cross.
    for (int p = 0; p < 8192; p++) begin
      lsu_resp_valid = 0;
      save_mode(p[0]);
      cheri_pmode_i = p[1];
      lsu_resp_valid = p[2];
      load_store_unit_i.data_rvalid_i = p[3];
      load_store_unit_i.data_err_i = p[4];
      lsu_resp_err = p[5];
      load_store_unit_i.lsu_req_info_q.is_load = p[6];
      load_store_unit_i.lsu_resp_info.is_cap = p[7];
      load_store_unit_i.data_rdata_i.valid = p[8];
      load_store_unit_i.lsu_req_info_q.clrperm = p[12:9];
      load_store_unit_i.data_rdata_i.cperms = 6'd3;
      load_store_unit_i.lsu_resp_info.wdata =
          mem2regcap(load_store_unit_i.data_rdata_i,
                     load_store_unit_i.lsu_req_info_q.clrperm);
      tick();
    end
    lsu_resp_valid = 0; lsu_resp_err = 0;
    load_store_unit_i.data_rvalid_i = 0;
    // Stored WB versus empty bypass, both tags, six causes, and every
    // runtime/saved-mode/err gate. A newer response always has the opposite tag.
    for (int stored = 0; stored < 3; stored++)
      for (int p = 0; p < 16; p++)
        for (int cause = 0; cause < 6; cause++) begin
          wb_write = 0; wb_read = 0;
          save_mode(p[0]);
          wb_input = '0;
          wb_input.is_cap = p[2];
          wb_input.err = p[3];
          case (cause)
            0: wb_input.mcause = EXC_CAUSE_LOAD_ADDR_MISALIGN;
            1: wb_input.mcause = EXC_CAUSE_LOAD_ACCESS_FAULT;
            2: wb_input.mcause = EXC_CAUSE_STORE_ADDR_MISALIGN;
            3: wb_input.mcause = EXC_CAUSE_STORE_ACCESS_FAULT;
            4: wb_input.mcause = EXC_CAUSE_CHERI_FAULT;
            5: wb_input.mcause = EXC_CAUSE_ILLEGAL_INSN;
          endcase
          if (stored) begin
            cheri_pmode_i = 0; // Capture must not count the presented FIFO head.
            wb_write = 1; tick(); wb_write = 0;
            // Change response provenance while the older entry remains stored.
            save_mode(!p[0]);
          end
          cheri_pmode_i = p[1];
          load_store_unit_i.lsu_resp_info.is_cap = !p[2];
          lsu_resp_valid = stored != 1; // Delayed WB with/without a newer response.
          wb_write = !stored; wb_read = !stored;
          #1;
          if (monitor.wb_cheri_mode !== (CHERIoTEn && p[0]) ||
              lspl_output_o !== wb_input || !lspl_valid_o)
            $fatal(1, "WB provenance/data fixture failed stored=%0d pattern=%0d", stored, p);
          // Unequal tag/cause/scenario multiplicities catch a swapped axis,
          // even when both tags eventually cover every exception bin.
          repeat (stored * 6 + int'(p[2]) + cause) tick();
          wb_read = 1;
          tick();
          wb_write = 0; wb_read = 0; lsu_resp_valid = 0;
        end
  endtask
endmodule

module kudu_top;
`ifdef CHERIoT
  localparam bit CHERIoTEn = 1;
`else
  localparam bit CHERIoTEn = 0;
`endif
  logic clk_i = 0, rst_ni = 0, cheri_pmode_i = 0, tsmap_cs_o = 0;
  logic [15:0] tsmap_addr_o = 0;
  logic [31:0] tsmap_rdata_i = 0;
  accuracy_level sbd_fifo_i();
  kudu_fcov_top #(.CHERIoTEn(CHERIoTEn)) monitor (
    .clk_i, .rst_ni, .cheri_pmode_i, .tsmap_cs_o, .tsmap_addr_o, .tsmap_rdata_i,
    .hart_id_i(32'b0), .boot_addr_i(32'b0), .instr_req_o(1'b0),
    .instr_gnt_i(1'b0), .instr_rvalid_i(1'b0), .instr_addr_o(32'b0),
    .instr_rdata_i(64'b0), .instr_err_i(1'b0), .data_req_o(1'b0),
    .data_is_cap_o(1'b0), .data_amo_flag_o(4'b0), .data_gnt_i(1'b0),
    .data_rvalid_i(1'b0), .data_we_o(1'b0), .data_be_o(4'b0),
    .data_addr_o(32'b0), .data_wdata_o(33'b0), .data_rdata_i(33'b0),
    .data_err_i(1'b0), .data_sc_fail_i(1'b0), .cheri_fatal_err_o(1'b0),
    .irq_software_i(1'b0), .irq_timer_i(1'b0), .irq_external_i(1'b0),
    .irq_fast_i(15'b0), .debug_req_i(1'b0)
  );
  task automatic tick;
    #5; clk_i = 1; #5; clk_i = 0;
  endtask
  task automatic map_cycle(input bit mode, cs, input logic [31:0] data);
    cheri_pmode_i = mode; tsmap_cs_o = cs; tsmap_rdata_i = data;
    tick();
  endtask
  task automatic exercise;
    tick(); rst_ni = 1;
    // Isolated returns and idle stale values, then consecutive requests.
    map_cycle(1, 1, '1); map_cycle(1, 0, 0); map_cycle(1, 0, '1);
    map_cycle(1, 1, 0); map_cycle(1, 0, 3); map_cycle(1, 0, 0);
    map_cycle(1, 1, 0); map_cycle(1, 0, 32'hff); map_cycle(1, 0, 0);
    map_cycle(1, 1, 0); map_cycle(1, 0, '1); map_cycle(1, 0, 0);
    map_cycle(1, 1, '1); map_cycle(1, 1, 0); map_cycle(1, 1, 3);
    map_cycle(1, 1, 32'hff); map_cycle(1, 0, '1);
    // RV32 request cannot acquire CHERI response provenance; dropping mode
    // at return also suppresses an older CHERI request.
    map_cycle(0, 1, 0); map_cycle(1, 0, '1);
    map_cycle(1, 1, 0); map_cycle(0, 0, '1); map_cycle(1, 0, '1);
    // Pending request must not survive reset.
    map_cycle(1, 1, 0); rst_ni = 0; tick(); rst_ni = 1;
    map_cycle(1, 0, '1); map_cycle(1, 0, '1);
  endtask
endmodule

module tb;
  dcache cache();
  ls_pipeline lspl();
  kudu_top top();
  int bad = 0;
  initial begin
    void'($value$plusargs("BAD=%d", bad));
    cache.exercise(bad);
    if (!bad) begin
      lspl.exercise();
      top.exercise();
    end
    $display("PASS FCOV accuracy HW=%0d BAD=%0d", lspl.CHERIoTEn, bad);
    $finish;
  end
endmodule
