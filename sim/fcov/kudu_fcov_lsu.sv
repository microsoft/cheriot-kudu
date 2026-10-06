// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// FC_MA_LSU -- load/store pipeline: request decode, the LSU bus FSM, the
// forwarding cache and capability revocation stage.
//
// Bound to ls_pipeline and separately to dcache and cheri_trvk_stage.
// Scalar bus coverage and queued response timing are owned by FC_MA_TOP.
//
// See doc/functional_coverage_plan.md section 12.

module kudu_fcov_lsu
  import super_pkg::*;
  import csr_pkg::*;
  import kudu_fcov_pkg::*;
(
  input logic          clk_i,
  input logic          rst_ni,

  // --- pipeline handshakes ---------------------------------------------------
  input logic          us_valid_i,
  input logic          lspl_rdy_o,
  input logic          ds_rdy_i,
  input logic          lspl_valid_o,
  input logic          flush_i,
  input logic          sel_ira_i,
  input logic          cmplx_lsu_req_valid_i,

  // --- request / response ----------------------------------------------------
  input lsu_req_info_t lsu_req_info,
  input logic          lsu_req,
  input logic          lsu_req_done,
  input logic          lsu_resp_valid,
  input logic          lsu_resp_err,
  input pl_out_t       lspl_output_o,
  input logic          lsu_err_active,
  input logic          resp_err_latched,
  input logic          is_lr,
  input logic          is_sc,
  input logic          data_sc_resp_i,

  // --- data bus (as seen at the pipeline boundary) ---------------------------
  input logic          data_req_o,
  input logic          data_gnt_i,
  input logic          data_rvalid_i,
  input logic          data_we_o,
  input logic          data_err_i,
  input logic [3:0]    data_be_o,
  input logic          data_is_cap_o,
  input logic [3:0]    data_amo_flag_o,
  input logic [31:0]   data_addr_o,

  // --- LSU FSM (load_store_unit_i) ------------------------------------------
  input ls_fsm_e       ls_fsm_cs,
  input logic          split_misaligned_access,
  input logic          handle_misaligned_q,
  input logic          addr_incr_req,
  input logic          lsu_busy,

  // --- revocation, as seen at the pipeline boundary --------------------------
  input logic          trvk_en_o,
  input logic          trvk_outstanding_o,
  input logic          tsafe_en_i,

  input logic          debug_mode_i,
  input logic          cheri_pmode_i
);

`ifndef KUDU_FCOV_OFF

  // lsu_req_info_t has no mode bit. Shadow its actual buffer enables and mux,
  // then the response register and write-through WB FIFO, so a mode change
  // cannot reclassify an older request, CSR access, fault, or capability load.
  logic cheri_active, req_dly_cheri_mode, req_hold_cheri_mode;
  logic req_cheri_mode, resp_cheri_mode, wb_cheri_mode;
  logic [3:0] wb_cheri_mode_mem;
  cheri_pkg::mem_cap_t resp_mem_cap;
  cheri_pkg::reg_cap_t resp_reg_cap;
  logic resp_cap_sample;
  logic split_first_err_q, split_active_q;

  assign resp_mem_cap =
      cheri_pkg::mem_cap_t'(ls_pipeline.load_store_unit_i.data_rdata_i);
  assign resp_reg_cap =
      cheri_pkg::reg_cap_t'(ls_pipeline.load_store_unit_i.lsu_resp_info.wdata);
  // Observe the raw memory capability before response permission masking.
  assign resp_cap_sample = cheri_active && resp_cheri_mode && lsu_resp_valid &&
      ls_pipeline.load_store_unit_i.data_rvalid_i &&
      !ls_pipeline.load_store_unit_i.data_err_i && !lsu_resp_err &&
      ls_pipeline.load_store_unit_i.lsu_req_info_q.is_load &&
      ls_pipeline.load_store_unit_i.lsu_resp_info.is_cap;

  assign cheri_active = ls_pipeline.CHERIoTEn && cheri_pmode_i;
  always_comb begin
    case (ls_pipeline.lsu_if_i.lsif_fsm_q)
      ls_pipeline.lsu_if_i.DLY1: req_cheri_mode = req_dly_cheri_mode;
      ls_pipeline.lsu_if_i.DLY0_WGNT,
      ls_pipeline.lsu_if_i.DLY1_WGNT: req_cheri_mode = req_hold_cheri_mode;
      default: req_cheri_mode = cheri_active;
    endcase
  end
  assign wb_cheri_mode = ls_pipeline.wb_fifo_i.fifo_empty ? resp_cheri_mode :
      wb_cheri_mode_mem[ls_pipeline.wb_fifo_i.rd_mem_addr];

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      req_dly_cheri_mode <= 1'b0;
      req_hold_cheri_mode <= 1'b0;
      resp_cheri_mode <= 1'b0;
      wb_cheri_mode_mem <= '0;
    end else begin
      if (!flush_i && ls_pipeline.lsu_if_i.lsif_rdy_local)
        req_dly_cheri_mode <= cheri_active;
      if (ls_pipeline.lsu_if_i.xfr2hold0)
        req_hold_cheri_mode <= cheri_active;
      else if (ls_pipeline.lsu_if_i.xfr2hold1)
        req_hold_cheri_mode <= req_dly_cheri_mode;
      if (ls_pipeline.load_store_unit_i.ls_go || ls_pipeline.load_store_unit_i.csr_go)
        resp_cheri_mode <= req_cheri_mode;
      if (ls_pipeline.wb_fifo_i.wr_data_en)
        wb_cheri_mode_mem[ls_pipeline.wb_fifo_i.wr_mem_addr] <= resp_cheri_mode;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      split_first_err_q <= 1'b0;
      split_active_q <= 1'b0;
    end else begin
      if (ls_pipeline.load_store_unit_i.ls_go) begin
        split_first_err_q <= 1'b0;
        split_active_q <= split_misaligned_access;
      end else if (lsu_resp_valid) begin
        split_active_q <= 1'b0;
      end
      if (ls_fsm_cs == WAIT_RVALID_MIS &&
          (data_rvalid_i || ls_pipeline.load_store_unit_i.pmp_err_q))
        split_first_err_q <= data_err_i | ls_pipeline.load_store_unit_i.pmp_err_q;
      else if (ls_fsm_cs == WAIT_RVALID_MIS_GNTS_DONE && data_rvalid_i)
        split_first_err_q <= data_err_i;
    end
  end

  // ==========================================================================
  // FC_MA_LSU - load/store pipeline
  // ==========================================================================
  covergroup cg_ma_lsu @(posedge clk_i iff rst_ni);
    option.per_instance = 1;
    option.name         = "FC_MA_LSU.lspl";

    // ======================================================================
    // 12.1 Request decode and pipeline flow
    // ======================================================================

    cp_us: coverpoint {us_valid_i, lspl_rdy_o} {
      bins idle       = {2'b00};
      bins rdy_no_req = {2'b01};
      bins stalled    = {2'b10};
      bins accepted   = {2'b11};
    }
    cp_ds: coverpoint {lspl_valid_o, ds_rdy_i} {
      bins idle       = {2'b00};
      bins rdy_no_out = {2'b01};
      bins stalled    = {2'b10};
      bins committed  = {2'b11};
    }
    cp_sel_ira: coverpoint sel_ira_i iff (us_valid_i);
    // The complex unit steals the LS pipeline for the two halves of an AMO.
    cp_cmplx_req: coverpoint cmplx_lsu_req_valid_i { bins hit = {1'b1}; }

    cp_is_load: coverpoint lsu_req_info.is_load iff (lsu_req);
    cp_is_cap:  coverpoint lsu_req_info.is_cap
        iff (cheri_active && req_cheri_mode && lsu_req) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }
    cp_is_csr:  coverpoint lsu_req_info.is_csr  iff (us_valid_i);
    cp_data_type: coverpoint lsu_req_info.data_type iff (lsu_req & ~lsu_req_info.is_csr) {
      bins word = {2'd0};
      bins half = {2'd1};
      bins byte_ = {2'd2};
    }
    cp_sign_ext: coverpoint lsu_req_info.sign_ext iff (lsu_req & lsu_req_info.is_load);
    cp_early_load: coverpoint lsu_req_info.early_load iff (lsu_req & lsu_req_info.is_load);
    cp_cache_ok:   coverpoint lsu_req_info.cache_ok iff (lsu_req);
    cp_amo_flag: coverpoint lsu_req_info.amo_flag iff (lsu_req) {
      bins none  = {4'b0000};
      bins lr    = {4'b0001};
      bins sc    = {4'b0010};
      bins amo_r = {4'b0100};
      bins amo_w = {4'b1000};
    }

    // The external bus is word aligned. Use the original effective address
    // before addr_incr_req selects a split request's second bus word.
    cp_addr_align: coverpoint lsu_req_info.addr[1:0]
        iff (lsu_req && !lsu_req_info.is_csr && ls_fsm_cs == IDLE) {
      bins b0 = {2'd0};
      bins b1 = {2'd1};
      bins b2 = {2'd2};
      bins b3 = {2'd3};
    }
    cp_size_align: coverpoint {lsu_req_info.data_type, lsu_req_info.addr[1:0]}
        iff (lsu_req && !lsu_req_info.is_csr && !lsu_req_info.is_cap &&
             ls_fsm_cs == IDLE) {
      bins word_aligned = {4'b0000};
      bins word_split[] = {4'b0001, 4'b0010, 4'b0011};
      bins half_aligned[] = {4'b0100, 4'b0110};
      bins half_unaligned = {4'b0101};
      bins half_split = {4'b0111};
      bins byte_offset[] = {4'b1000, 4'b1001, 4'b1010, 4'b1011};
    }
    cp_cap_addr_align: coverpoint lsu_req_info.addr[2:0]
        iff (cheri_active && req_cheri_mode && lsu_req && !lsu_req_info.is_csr &&
             lsu_req_info.is_cap && ls_fsm_cs == IDLE) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins aligned = {3'd0};
      bins misaligned[] = {[3'd1:3'd7]};
    }

    // CHERI faults are detected before the bus request is made, so they must
    // be covered on the request-info side, not on the response.
    cp_cheri_req_err: coverpoint lsu_req_info.cheri_err
        iff (cheri_active && req_cheri_mode && lsu_req) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }
    cp_cheri_req_cause: coverpoint lsu_req_info.cheri_cause
        iff (cheri_active && req_cheri_mode && lsu_req && lsu_req_info.cheri_err) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins c_align = {5'h00};
      bins c_bound = {5'h01};
      bins c_tag   = {5'h02};
      bins c_seal  = {5'h03};
      bins c_ld    = {5'h12};
      bins c_sd    = {5'h13};
      bins c_sc    = {5'h15};
      illegal_bins other = default;
    }
    // This is cheri_ls_check's alignment-only result, not RV32 split alignment.
    cp_align_err_only: coverpoint lsu_req_info.align_err_only
        iff (cheri_active && req_cheri_mode && lsu_req) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }

    cp_lr: coverpoint is_lr iff (us_valid_i) { bins hit = {1'b1}; }
    cp_sc: coverpoint is_sc iff (us_valid_i) { bins hit = {1'b1}; }
    // SC response polarity and request association are covered by FC_MA_TOP.

    cp_flush:      coverpoint flush_i { bins hit = {1'b1}; }
    cp_flush_busy: coverpoint (flush_i & (lsu_busy | lspl_valid_o)) { bins hit = {1'b1}; }
    cp_debug_mode: coverpoint debug_mode_i;
    // Both runtime modes are goals only on CHERI-capable hardware.
    cp_pmode: coverpoint cheri_pmode_i iff (ls_pipeline.CHERIoTEn) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }

    // Observe the RTL's two request buffers, not the live upstream decode.
    // lsu_if.sv transfers either the early input or a valid delayed request.
    cp_lsif_hold_capture: coverpoint {
        ls_pipeline.lsu_if_i.xfr2hold0, ls_pipeline.lsu_if_i.xfr2hold1}
        iff (!flush_i &&
             (ls_pipeline.lsu_if_i.xfr2hold0 ||
              (ls_pipeline.lsu_if_i.xfr2hold1 && ls_pipeline.lsu_if_i.req_dly_valid))) {
      bins early_input = {2'b10};
      bins delayed_request = {2'b01};
    }
    cp_lsif_delayed_backlog: coverpoint ls_pipeline.lsu_if_i.req_dly_valid
        iff (!flush_i &&
             ls_pipeline.lsu_if_i.lsif_fsm_q == ls_pipeline.lsu_if_i.DLY1_WGNT &&
             ls_pipeline.lsu_if_i.lsu_req_o && ls_pipeline.lsu_if_i.lsu_req_done_i) {
      // DLY1_WGNT: finishing req_hold_q either drains or exposes req_dly_q.
      bins drained = {1'b0};
      bins queued = {1'b1};
    }

    cp_waw_fifo_level: coverpoint ls_pipeline.waw_fifo_i.fifo_level {
      bins empty = {8'sd0};
      bins one = {8'sd1};
      bins two_or_more = {[8'sd2:8'sd127]};
    }
    cp_wb_fifo_level: coverpoint ls_pipeline.wb_fifo_i.fifo_level {
      bins empty = {8'sd0};
      bins one_or_more = {[8'sd1:8'sd127]};
    }

    // wt_fifo.sv accepts writes with wr_rdy and can read through an empty
    // FIFO. Count transfers only when flush does not discard pointer updates.
    cp_wb_storage_flow: coverpoint {
        ls_pipeline.wb_fifo_i.fifo_empty,
        (ls_pipeline.wb_fifo_i.wr_valid_i && ls_pipeline.wb_fifo_i.wr_rdy),
        (ls_pipeline.wb_fifo_i.rd_valid && ls_pipeline.wb_fifo_i.rd_rdy_i)}
        iff (!flush_i) {
      bins empty_capture = {3'b110};
      bins empty_bypass = {3'b111};
      bins stored_push = {3'b010};
      bins stored_pop = {3'b001};
      bins stored_exchange = {3'b011};
    }
    // Only a live, still-reserved head that remains resident can be cancelled.
    // WAW cancellation clears bit 5, not occupancy (waw_tracking_fifo.sv).
    cp_waw_resident_head_cancel: coverpoint ls_pipeline.waw_fifo_i.waw_match_head
        iff (!flush_i && ls_pipeline.waw_fifo_i.rd_valid &&
             !ls_pipeline.waw_fifo_i.rd_rdy_i &&
             ls_pipeline.waw_fifo_i.fifo_head_data[5]) {
      bins cancelled = {1'b1};
    }

    // Cross weights and sampling guards do not inherit coverpoint options.
    x_ls_type_1 : cross cp_is_load, cp_is_cap, cp_cache_ok
        iff (cheri_active && req_cheri_mode && lsu_req) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }
    x_ls_type_2 : cross cp_is_cap, cp_cache_ok, cp_cheri_req_cause
        iff (cheri_active && req_cheri_mode && lsu_req && lsu_req_info.cheri_err) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }

    x_ls_cap_1 : cross cp_is_load, cp_cap_addr_align
        iff (cheri_active && req_cheri_mode && lsu_req && !lsu_req_info.is_csr &&
             lsu_req_info.is_cap && ls_fsm_cs == IDLE) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }
    x_ls_rv32_1 : cross cp_is_load, cp_data_type, cp_addr_align;

    

    // ======================================================================
    // 12.2 LSU bus FSM (bus timing is owned by FC_MA_TOP)
    // ======================================================================
    cp_state: coverpoint ls_fsm_cs;
    cp_transition: coverpoint ls_fsm_cs {
      // Observe consecutive sampled states, not a combinational next-state pair.
      bins start_aligned = (IDLE => WAIT_GNT);
      bins start_split   = (IDLE => WAIT_GNT_MIS);
      bins split_fast_gnt = (IDLE => WAIT_RVALID_MIS);
      bins mis_gnt       = (WAIT_GNT_MIS => WAIT_RVALID_MIS);
      bins mis_second    = (WAIT_RVALID_MIS => WAIT_GNT);
      bins mis_gnts_done = (WAIT_RVALID_MIS => WAIT_RVALID_MIS_GNTS_DONE);
      bins done          = (WAIT_GNT => IDLE);
      bins mis_done = (WAIT_RVALID_MIS => IDLE);
      bins mis_resps_pending = (WAIT_RVALID_MIS_GNTS_DONE => IDLE);
      bins hold[] = (IDLE => IDLE), (WAIT_GNT => WAIT_GNT),
                    (WAIT_GNT_MIS => WAIT_GNT_MIS),
                    (WAIT_RVALID_MIS => WAIT_RVALID_MIS),
                    (WAIT_RVALID_MIS_GNTS_DONE => WAIT_RVALID_MIS_GNTS_DONE);
    }

    cp_data_err_state: coverpoint ls_fsm_cs iff (data_err_i && data_rvalid_i) {
      bins wait_rvalid_mis = {WAIT_RVALID_MIS};
      bins wait_rvalid_mis_gnts_done = {WAIT_RVALID_MIS_GNTS_DONE};
      bins idle = {IDLE};
    }

    cp_split:      coverpoint split_misaligned_access { bins hit = {1'b1}; }
    cp_mis_q:      coverpoint handle_misaligned_q     { bins hit = {1'b1}; }
    cp_addr_incr:  coverpoint addr_incr_req           { bins hit = {1'b1}; }
    cp_busy:       coverpoint lsu_busy;

    // load_store_unit.sv gates ls_go/csr_go with these independent blockers.
    cp_lsu_start_blocker: coverpoint {
        ls_pipeline.load_store_unit_i.resp_wait,
        !ls_pipeline.load_store_unit_i.ds_rdy_i}
        iff (!flush_i && lsu_req && ls_fsm_cs == IDLE) {
      bins response_pending = {2'b10};
      bins downstream = {2'b01};
      bins both = {2'b11};
    }
    // rdata_update captures the first word of a split load. Classify the
    // saved transaction, only on an actual successful data response.
    cp_split_load_capture: coverpoint {
        ls_pipeline.load_store_unit_i.lsu_req_info_q.data_type,
        ls_pipeline.load_store_unit_i.lsu_req_info_q.sign_ext}
        iff (ls_pipeline.load_store_unit_i.rdata_update && data_rvalid_i && !data_err_i) {
      wildcard bins word = {3'b00?};
      bins signed_half = {3'b011};
      bins unsigned_half = {3'b010};
    }
    cp_split_err_phase: coverpoint {
        split_first_err_q,
        (data_err_i | ls_pipeline.load_store_unit_i.pmp_err_q)}
        iff (lsu_resp_valid && split_active_q) {
      bins none = {2'b00};
      bins second = {2'b01};
      bins first = {2'b10};
      bins both = {2'b11};
    }
    cp_split_resp_is_load: coverpoint ls_pipeline.load_store_unit_i.lsu_req_info_q.is_load
        iff (lsu_resp_valid && split_active_q) {
      bins store = {1'b0};
      bins load = {1'b1};
    }
    x_split_err_phase: cross cp_split_resp_is_load, cp_split_err_phase
        iff (lsu_resp_valid && split_active_q);

    cp_csr_cheri_asr_err: coverpoint ls_pipeline.load_store_unit_i.csr_cheri_asr_err
        iff (cheri_active && resp_cheri_mode && lsu_resp_valid &&
             ls_pipeline.load_store_unit_i.csr_go_q) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins clear = {1'b0};
      bins error = {1'b1};
    }
    cp_cheri_ls_err: coverpoint ls_pipeline.load_store_unit_i.cheri_ls_err
        iff (cheri_active && resp_cheri_mode && lsu_resp_valid &&
             !ls_pipeline.load_store_unit_i.lsu_req_info_q.is_csr) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins clear = {1'b0};
      bins error = {1'b1};
    }
    cp_ls_align_err_only: coverpoint ls_pipeline.load_store_unit_i.ls_align_err_only
        iff (cheri_active && resp_cheri_mode && lsu_resp_valid &&
             !ls_pipeline.load_store_unit_i.lsu_req_info_q.is_csr &&
             ls_pipeline.load_store_unit_i.cheri_ls_err) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins other_cheri_fault = {1'b0};
      bins alignment_only = {1'b1};
    }
    cp_resp_early_cheri_cause: coverpoint ls_pipeline.load_store_unit_i.cheri_err_cause
        iff (cheri_active && resp_cheri_mode && lsu_resp_valid &&
             ls_pipeline.load_store_unit_i.cheri_ls_err &&
             !ls_pipeline.load_store_unit_i.lsu_req_info_q.cheri_err) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins c_align = {5'h00};
      bins c_bound = {5'h01};
      bins c_tag   = {5'h02};
      bins c_seal  = {5'h03};
      bins c_ld    = {5'h12};
      bins c_sd    = {5'h13};
      bins c_sc    = {5'h15};
      illegal_bins other = default;
    }

    // clrperm and is_load are retained in the response's saved request, not pl_out_t.
    cp_resp_clrperm: coverpoint ls_pipeline.load_store_unit_i.lsu_req_info_q.clrperm
        iff (cheri_active && resp_cheri_mode && lsu_resp_valid &&
             ls_pipeline.load_store_unit_i.lsu_resp_info.is_cap) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins none = {4'h0};
      bins some[] = {[4'h1:4'hf]} with (item[2] == 1'b0);
    }
    cp_resp_is_load: coverpoint ls_pipeline.load_store_unit_i.lsu_req_info_q.is_load
        iff (lsu_resp_valid);
    cp_resp_is_cap: coverpoint ls_pipeline.load_store_unit_i.lsu_resp_info.is_cap
        iff (cheri_active && resp_cheri_mode && lsu_resp_valid) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }

    cp_resp_cap_valid: coverpoint resp_mem_cap.valid iff (resp_cap_sample) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins untagged = {1'b0};
      bins tagged_cap = {1'b1};
    }
    cp_resp_cap_rsvd: coverpoint resp_mem_cap.rsvd
        iff (resp_cap_sample && resp_mem_cap.valid) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }
    cp_resp_cap_cperms: coverpoint resp_mem_cap.cperms
        iff (resp_cap_sample && resp_mem_cap.valid) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }
    cp_resp_cap_otype: coverpoint resp_mem_cap.otype
        iff (resp_cap_sample && resp_mem_cap.valid) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }
    cp_resp_cap_cexp: coverpoint resp_mem_cap.cexp
        iff (resp_cap_sample && resp_mem_cap.valid) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins zero = {5'd0};
      bins max_ = {5'd31};
      bins twenty_four = {5'd24};
      bins one = {5'd1};
      bins other = {[5'd2:5'd23], [5'd25:5'd30]};
    }
    cp_resp_cap_top_vs_base: coverpoint {
        (resp_mem_cap.top8 > resp_mem_cap.base9[7:0]),
        (resp_mem_cap.top8 < resp_mem_cap.base9[7:0])}
        iff (resp_cap_sample && resp_mem_cap.valid) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins equal = {2'b00};
      bins greater = {2'b10};
      bins less = {2'b01};
    }
    cp_resp_cap_addr: coverpoint resp_mem_cap.addr
        iff (resp_cap_sample && resp_mem_cap.valid) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }
    cp_resp_cap_top_path: coverpoint {
        (resp_mem_cap.cexp == 5'd0),
        resp_mem_cap.base9[8],
        (resp_mem_cap.top8 < resp_mem_cap.base9[7:0])}
        iff (resp_cap_sample && resp_mem_cap.valid) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins path[] = {[3'b000:3'b111]};
    }
    cp_resp_cap_perm_effect: coverpoint {
        (resp_mem_cap.otype != cheri_pkg::OTYPE_UNSEALED),
        ls_pipeline.load_store_unit_i.lsu_req_info_q.clrperm[0],
        ls_pipeline.load_store_unit_i.lsu_req_info_q.clrperm[1],
        (resp_reg_cap.cperms != resp_mem_cap.cperms)}
        iff (resp_cap_sample && resp_mem_cap.valid) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins unsealed_none = {4'b0000};
      bins unsealed_cglg_changed = {4'b0101};
      bins unsealed_csdlm_changed = {4'b0011};
      bins unsealed_both_changed = {4'b0111};
      bins sealed_none = {4'b1000};
      bins sealed_cglg_changed = {4'b1101};
      bins sealed_csdlm_suppressed = {4'b1010};
      bins sealed_both_gl_only = {4'b1111};
      bins unchanged_by_absent_perms[] = {4'b0100, 4'b0010, 4'b0110, 4'b1100,
                                          4'b1110};
      ignore_bins inconsistent_changed = {4'b0001, 4'b1001, 4'b1011};
    }
    cp_resp_cap_tag_outcome: coverpoint {
        resp_mem_cap.valid,
        ls_pipeline.load_store_unit_i.lsu_req_info_q.clrperm[3],
        resp_reg_cap.valid}
        iff (resp_cap_sample) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins raw_untagged = {3'b000, 3'b010};
      bins raw_tag_kept = {3'b101};
      bins raw_tag_cleared_by_load = {3'b110};
      illegal_bins tag_mismatch = {3'b001, 3'b011, 3'b100, 3'b111};
    }

    cp_err_active:  coverpoint lsu_err_active   { bins hit = {1'b1}; }
    cp_err_latched: coverpoint resp_err_latched { bins hit = {1'b1}; }
    cp_out_err:     coverpoint lspl_output_o.err iff (lspl_valid_o) {
      bins ok  = {1'b0};
      bins err = {1'b1};
    }
    // The LS pipeline is the only unit that drives .err, which is why the
    // committer can hardwire its error capture to lspl_output_i (finding F-03).
    cp_out_mcause: coverpoint lspl_output_o.mcause
        iff (lspl_valid_o && lspl_output_o.err &&
             (lspl_output_o.mcause != EXC_CAUSE_CHERI_FAULT ||
              (cheri_active && wb_cheri_mode))) {
      bins load_align  = {EXC_CAUSE_LOAD_ADDR_MISALIGN};
      bins load_fault  = {EXC_CAUSE_LOAD_ACCESS_FAULT};
      bins store_align = {EXC_CAUSE_STORE_ADDR_MISALIGN};
      bins store_fault = {EXC_CAUSE_STORE_ACCESS_FAULT};
      bins cheri       = {EXC_CAUSE_CHERI_FAULT};
      bins illegal     = {EXC_CAUSE_ILLEGAL_INSN};
    }

    // Both error-cross axes describe the same WB FIFO head, not a newer response.
    cp_out_is_cap: coverpoint lspl_output_o.is_cap
        iff (cheri_active && wb_cheri_mode && lspl_valid_o && lspl_output_o.err) {
      option.weight = 0;
    }
    x_access_err : cross cp_out_is_cap, cp_out_mcause
        iff (cheri_active && wb_cheri_mode && lspl_valid_o && lspl_output_o.err) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }
    x_resp_clrperm_1: cross cp_resp_cap_valid, cp_resp_clrperm
        iff (resp_cap_sample) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }
    x_resp_clrperm_2: cross cp_resp_cap_cperms, cp_resp_clrperm
        iff (resp_cap_sample && resp_mem_cap.valid) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }
    

    // ======================================================================
    // 12.3 Temporal safety
    // ======================================================================
    cp_tsafe_en: coverpoint tsafe_en_i iff (cheri_active) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }
    // trvk_en / outstanding scalar coverage lives in the bound trvk module.
  endgroup

  cg_ma_lsu u_cg_ma_lsu = new();

  AssertCheriReqCauseReachable: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (cheri_active && req_cheri_mode && lsu_req && lsu_req_info.cheri_err) |->
    (lsu_req_info.cheri_cause inside
     {5'h00, 5'h01, 5'h02, 5'h03, 5'h12, 5'h13, 5'h15}))
    else $error("FCOV: LSU CHERI request cause outside cheri_ls_check encoding");

  AssertRespEarlyCheriCauseReachable: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (cheri_active && resp_cheri_mode && lsu_resp_valid &&
     ls_pipeline.load_store_unit_i.cheri_ls_err &&
     !ls_pipeline.load_store_unit_i.lsu_req_info_q.cheri_err) |->
    (ls_pipeline.load_store_unit_i.cheri_err_cause inside
     {5'h00, 5'h01, 5'h02, 5'h03, 5'h12, 5'h13, 5'h15}))
    else $error("FCOV: LSU response CHERI cause outside cheri_ls_check encoding");

  AssertRespCapTagMatchesClrperm: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    resp_cap_sample |-> (resp_reg_cap.valid ==
                         (resp_mem_cap.valid &
                          ~ls_pipeline.load_store_unit_i.lsu_req_info_q.clrperm[3])))
    else $error("FCOV: capability load tag result does not match clrperm[3]");

`endif  // KUDU_FCOV_OFF

endmodule


// ===========================================================================
// Forwarding cache.  Bound to the dcache module directly rather than reached
// through ls_pipeline: dcache_i sits inside an unnamed "if (DCacheEn)" block
// (ls_pipeline.sv:359), so its hierarchical path is not stable.
// ===========================================================================
module kudu_fcov_dcache
  import super_pkg::*;
  import kudu_fcov_pkg::*;
(
  input logic       clk_i,
  input logic       rst_ni,

  input logic       cache_enable_i,
  input logic       lsu_req_i,
  input pl_fwd_t    fwd_info_o,
  input logic [3:0] line_valid,
  input logic [3:0] rd_tag_match,
  input logic [3:0] wr_tag_match,
  input logic       cache_rd_hit,
  input logic       cache_rd_match_ok,
  input logic       rd_hit_q,
  input logic       byp_tag_match,
  input logic       byp_data_good,
  input logic       unaligned_access,
  input logic       unaligned_access_q,
  input logic [3:0] repl_sel,
  input logic [3:0] update_valid,
  input logic [3:0] update_invalid,
  input logic       resp_full_word,
  input logic       resp_partial_word,
  input logic       resp_invalidate,
  input logic       waw_act_match
);

`ifndef KUDU_FCOV_OFF

  // ==========================================================================
  // 12.4 Forwarding cache
  // ==========================================================================
  covergroup cg_ma_dcache @(posedge clk_i iff rst_ni);
    option.per_instance = 1;
    option.name         = "FC_MA_LSU.dcache";

    cp_enable:    coverpoint cache_enable_i;
    cp_occupancy: coverpoint $countones(line_valid) { bins n[] = {[0:4]}; }

    cp_rd_match: coverpoint rd_tag_match {
      bins miss = {4'b0000};
      bins hit[] = {4'b0001, 4'b0010, 4'b0100, 4'b1000};
      illegal_bins multi = {[4'b0000:4'b1111]} with ($countones(item) >= 2);
    }
    cp_wr_match: coverpoint wr_tag_match {
      bins miss = {4'b0000};
      bins hit[] = {4'b0001, 4'b0010, 4'b0100, 4'b1000};
      bins two_hits = {[4'b0000:4'b1111]} with ($countones(item) == 2);
      illegal_bins multi = {[4'b0000:4'b1111]} with ($countones(item) >= 3);
    }

    cp_rd_hit:       coverpoint cache_rd_hit iff (lsu_req_i);
    cp_rd_match_ok:  coverpoint cache_rd_match_ok iff (lsu_req_i);
    cp_rd_hit_q:     coverpoint rd_hit_q;
    cp_fwd_addr1: coverpoint fwd_info_o.addr1 iff (fwd_info_o.valid[1]);
    // Dcache forwards a zero-extended integer, even when OpW includes capability fields.
    cp_fwd_data1: coverpoint fwd_info_o.data1[31:0] iff (fwd_info_o.valid[1]);
    // A tag match that is nevertheless not usable (partially written line,
    // wrong size) is the case that must fall back to the bus.
    cp_match_no_hit: coverpoint (|rd_tag_match & ~cache_rd_hit) { bins hit = {1'b1}; }

    cp_byp_match: coverpoint byp_tag_match { bins hit = {1'b1}; }
    cp_byp_good:  coverpoint byp_data_good iff (byp_tag_match) {
      bins stale = {1'b0};
      bins good  = {1'b1};
    }
    cp_unaligned: coverpoint unaligned_access { bins hit = {1'b1}; }

    cp_repl: coverpoint repl_sel
        iff (cache_enable_i && (|(update_valid & ~update_invalid))) {
      bins way[] = {4'b0001, 4'b0010, 4'b0100, 4'b1000};
      bins none  = {4'b0000};
    }
    cp_update_valid: coverpoint $countones(update_valid) {
      bins n[] = {0, 1};
      illegal_bins multiple = {[2:4]};
    }
    cp_update_invalid: coverpoint $countones(update_invalid) {
      bins n[] = {0, 1, 2, 4};
      illegal_bins three = {3};
    }

    cp_resp_full:    coverpoint resp_full_word    { bins hit = {1'b1}; }
    cp_resp_partial: coverpoint resp_partial_word { bins hit = {1'b1}; }
    cp_resp_inval:   coverpoint resp_invalidate   { bins hit = {1'b1}; }
    cp_resp_inval_two_matches: coverpoint resp_invalidate
        iff ($countones(wr_tag_match) == 2) {
      bins hit = {1'b1};
    }
    cp_unaligned_two_matches: coverpoint unaligned_access_q
        iff ($countones(wr_tag_match) == 2) {
      bins hit = {1'b1};
    }
    cp_waw_match:    coverpoint waw_act_match     { bins hit = {1'b1}; }

    // This depth-4 WAW FIFO uses WrThrough=1, unlike the pipeline's FIFO.
    // Its read handshake consumes reservation metadata at request completion.
    cp_waw_read_source: coverpoint dcache.waw_fifo_i.fifo_empty
        iff (!dcache.flush_i && dcache.waw_fifo_i.rd_valid &&
             dcache.waw_fifo_i.rd_rdy_i) {
      bins stored = {1'b0};
      bins write_through = {1'b1};
    }
  endgroup

  cg_ma_dcache u_cg_lsu_cache = new();

  AssertRdTagOneHot: assert property (
    @(posedge clk_i) disable iff (!rst_ni) $onehot0(rd_tag_match))
    else $error("FCOV: dcache read tag matched more than one line");

  AssertWrTagAtMostTwo: assert property (
    @(posedge clk_i) disable iff (!rst_ni) $countones(wr_tag_match) <= 2)
    else $error("FCOV: dcache write tag matched more than two lines");

  AssertUpdateValidOneHot: assert property (
    @(posedge clk_i) disable iff (!rst_ni) $onehot0(update_valid))
    else $error("FCOV: dcache updated more than one line");

  AssertUpdateInvalidNotThree: assert property (
    @(posedge clk_i) disable iff (!rst_ni) $countones(update_invalid) != 3)
    else $error("FCOV: dcache invalidated exactly three lines");

`endif  // KUDU_FCOV_OFF

endmodule


// ===========================================================================
// Capability revocation stage.  Bound directly for the same reason: the
// instance lives inside gen_trvk (ls_pipeline.sv:383).
// ===========================================================================
// Match the bind guard so RV32 builds cannot elaborate an unbound monitor as a top.
`ifdef CHERIoT
module kudu_fcov_trvk
  import super_pkg::*;
  import kudu_fcov_pkg::*;
(
  input logic       clk_i,
  input logic       rst_ni,

  input logic       clc_valid_i,
  input logic       clc_err_i,
  input logic [4:0] clc_rd_i,
  input logic       trvk_en_o,
  input logic       trvk_clrtag_o,
  input logic       trvk_outstanding_o,
  input logic       tsmap_cs_o
);

`ifndef KUDU_FCOV_OFF

  // Revocation is three cycles behind the retiring load. In addition to the
  // live CHERI gate, retain that load's mode, including a WB FIFO bypass.
  logic clc_cheri_mode;
  logic [2:0] trvk_cheri_mode_q;
  logic [4:0] trvk_bitpos_q[2:0];
  logic prev_trvk_valid, prev_trvk_clrtag, prev_trvk_cheri_mode;
  wire cheri_active = ls_pipeline.CHERIoTEn && ls_pipeline.cheri_pmode_i;
  assign clc_cheri_mode = ls_pipeline.u_fcov_lsu.wb_cheri_mode;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      trvk_cheri_mode_q <= '0;
      trvk_bitpos_q[0] <= '0;
      trvk_bitpos_q[1] <= '0;
      trvk_bitpos_q[2] <= '0;
      prev_trvk_valid <= 1'b0;
      prev_trvk_clrtag <= 1'b0;
      prev_trvk_cheri_mode <= 1'b0;
    end else begin
      trvk_cheri_mode_q <= {trvk_cheri_mode_q[1:0], clc_cheri_mode && clc_valid_i};
      trvk_bitpos_q[0] <= cheri_trvk_stage.tsmap_ptr[4:0];
      trvk_bitpos_q[1] <= trvk_bitpos_q[0];
      trvk_bitpos_q[2] <= trvk_bitpos_q[1];
      prev_trvk_valid <= trvk_en_o;
      prev_trvk_clrtag <= trvk_clrtag_o;
      prev_trvk_cheri_mode <= trvk_cheri_mode_q[2];
    end
  end

  // ==========================================================================
  // 12.5 Capability revocation
  // ==========================================================================
  covergroup cg_ma_trvk @(posedge clk_i iff (rst_ni && cheri_active));
    option.per_instance = 1;
    option.name         = "FC_MA_LSU.trvk";

    cp_clc_valid_i: coverpoint clc_valid_i iff (clc_cheri_mode) { bins hit = {1'b1}; }
    // A capability load that faulted still enters the revocation stage; it
    // must not produce a tag-clear.
    cp_clc_err_i:   coverpoint clc_err_i iff (clc_cheri_mode && clc_valid_i) {
      bins ok  = {1'b0};
      bins err = {1'b1};
    }
    cp_clc_rd_i: coverpoint clc_rd_i iff (clc_cheri_mode && clc_valid_i) {
      bins x0     = {5'd0};
      bins reg_[] = {[1:15]};
    }
    cp_tsmap_cs: coverpoint tsmap_cs_o iff (trvk_cheri_mode_q[0]) { bins hit = {1'b1}; }
    cp_trvk_en: coverpoint trvk_en_o iff (trvk_cheri_mode_q[2]) { bins hit = {1'b1}; }
    cp_trvk_clrtag: coverpoint trvk_clrtag_o iff (trvk_cheri_mode_q[2] && trvk_en_o) {
      bins kept    = {1'b0};
      bins cleared = {1'b1};
    }
    cp_outstanding: coverpoint trvk_outstanding_o
        iff (!trvk_outstanding_o || (|trvk_cheri_mode_q));

    // range_ok describes in_cap_q at stage 0, including the sealing-cap
    // exclusion. Stale saved capabilities and faulted/untagged loads do not count.
    cp_saved_range: coverpoint cheri_trvk_stage.range_ok
        iff (trvk_cheri_mode_q[0] && cheri_trvk_stage.clc_valid_q[0] &&
             cheri_trvk_stage.cap_good_q[0]) {
      bins excluded = {1'b0};
      bins eligible = {1'b1};
    }
    cp_selected_bitpos: coverpoint trvk_bitpos_q[2]
        iff (trvk_cheri_mode_q[2] && cheri_trvk_stage.cap_good_q[2] &&
             cheri_trvk_stage.range_ok_q[2]) {
      bins pos[] = {[0:31]};
    }
    cp_selected_bit_value: coverpoint cheri_trvk_stage.trvk_status
        iff (trvk_cheri_mode_q[2] && cheri_trvk_stage.cap_good_q[2] &&
             cheri_trvk_stage.range_ok_q[2]) {
      bins kept = {1'b0};
      bins selected = {1'b1};
    }
    x_selected_bit: cross cp_selected_bitpos, cp_selected_bit_value
        iff (trvk_cheri_mode_q[2] && cheri_trvk_stage.cap_good_q[2] &&
             cheri_trvk_stage.range_ok_q[2]) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }
    cp_range_boundary: coverpoint (
        cheri_trvk_stage.base32 < cheri_trvk_stage.HeapBase ? 3'd3 :
        cheri_trvk_stage.tsmap_ptr[31:5] == 0 ? 3'd0 :
        cheri_trvk_stage.tsmap_ptr[31:5] == cheri_trvk_stage.TSMapSize ? 3'd1 :
        cheri_trvk_stage.tsmap_ptr[31:5] > cheri_trvk_stage.TSMapSize ? 3'd2 : 3'd4)
        iff (trvk_cheri_mode_q[0] && cheri_trvk_stage.clc_valid_q[0] &&
             cheri_trvk_stage.cap_good_q[0]) {
      bins low_word = {3'd0};
      bins inclusive_limit = {3'd1};
      bins above_limit = {3'd2};
      bins below_heap = {3'd3};
      bins interior = {3'd4};
    }
    cp_b2b_revocation_outcome: coverpoint {prev_trvk_clrtag, trvk_clrtag_o}
        iff (prev_trvk_valid && trvk_en_o && prev_trvk_cheri_mode &&
             trvk_cheri_mode_q[2]) {
      bins kept_then_cleared = {2'b01};
      bins cleared_then_kept = {2'b10};
    }
  endgroup

  cg_ma_trvk u_cg_lsu_trvk = new();

`endif  // KUDU_FCOV_OFF

endmodule
`endif  // CHERIoT
