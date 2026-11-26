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
  input logic          lr_insn,
  input logic          sc_insn,
  input logic          data_sc_fail_i,

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
  // check_ls_err results. The request side carries lschk_err in lsu_req_info
  // (set by lsu_if only on CHERI hardware); the response side merges it with
  // the LSU's own recheck. vio_cause_enc returns {align_only, cause[4:0]}.
  logic [5:0] req_err_cause;
  cheri_pkg::lschk_err_t resp_lschk_err;
  logic [5:0] resp_err_cause;
  logic resp_atomic_align_err;

  assign req_err_cause  = cheri_pkg::vio_cause_enc(lsu_req_info.lschk_err);
  assign resp_lschk_err = ls_pipeline.load_store_unit_i.lschk_err_final;
  assign resp_err_cause = ls_pipeline.load_store_unit_i.ls_err_cause;
  // Misaligned LR/SC/AMO fault in every mode, including RV32-only hardware
  // where only the response-side check sees them.
  assign resp_atomic_align_err = lsu_resp_valid && resp_lschk_err.any_fault &&
      resp_lschk_err.align && resp_err_cause[5] &&
      (|ls_pipeline.load_store_unit_i.lsu_req_info_q.amo_flag);

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
    end
  end

  // --- bug-driven response classes (sim/testplan/fcov_bug_crosscheck.md) ----
  logic [3:0]  resp_amo_flag;
  logic [5:0]  resp_mcause;
  logic [31:0] resp_mtval, split_addr, split_addr2;
  logic        amo_bus_err, amo_cheri_err, split_bus_err, clrperm_sample;
  logic        csr_noasr_sample, mshwm_upd;

  assign resp_amo_flag = ls_pipeline.load_store_unit_i.lsu_req_info_q.amo_flag;
  assign resp_mcause   = ls_pipeline.load_store_unit_i.lsu_resp_info.mcause;
  assign resp_mtval    = ls_pipeline.load_store_unit_i.lsu_resp_info.mtval;

  // KUDU-008: bus error on LR/SC/AMO. Only LR reports a load fault.
  assign amo_bus_err = lsu_resp_valid && (|resp_amo_flag) &&
      (resp_mcause == EXC_CAUSE_LOAD_ACCESS_FAULT ||
       resp_mcause == EXC_CAUSE_STORE_ACCESS_FAULT);
  // KUDU-032/061: CHERI fault on the AMO read phase (SD checked there too).
  assign amo_cheri_err = cheri_active && resp_cheri_mode && lsu_resp_valid &&
      resp_lschk_err.any_fault && !resp_err_cause[5] && (resp_amo_flag == 4'b0100);

  // KUDU-052: mtval of a split access with a bus error. The first half
  // reports the access address, the second half its word-aligned address.
  typedef enum logic [1:0] {SMT_FIRST_ADDR, SMT_SECOND_WORD, SMT_OTHER} fcov_split_mtval_e;
  fcov_split_mtval_e split_mtval_cls;
  assign split_addr  = ls_pipeline.load_store_unit_i.lsu_req_info_q.addr;
  assign split_addr2 = {split_addr[31:2] + 30'd1, 2'b00};
  assign split_bus_err = lsu_resp_valid && split_active_q &&
      (resp_mcause == EXC_CAUSE_LOAD_ACCESS_FAULT ||
       resp_mcause == EXC_CAUSE_STORE_ACCESS_FAULT);
  assign split_mtval_cls = (resp_mtval == split_addr)  ? SMT_FIRST_ADDR :
                           (resp_mtval == split_addr2) ? SMT_SECOND_WORD : SMT_OTHER;

  // KUDU-024: CLC permission stripping, including in debug mode.
  assign clrperm_sample = cheri_active && resp_cheri_mode && lsu_resp_valid &&
      ls_pipeline.load_store_unit_i.lsu_resp_info.is_cap;

  // KUDU-017/018: CSR/SCR access in CHERI mode without PCC.ASR, classed by
  // what the access should report.
  typedef enum logic [2:0] {
    CA_ILLEGAL, CA_CNT_WR, CA_ALWAYS_OK, CA_SCR, CA_OTHER
  } fcov_csr_asr_e;
  typedef enum logic [1:0] {CO_OK, CO_ILL, CO_ASR, CO_OTHER} fcov_csr_out_e;
  fcov_csr_asr_e csr_asr_cls;
  fcov_csr_out_e csr_out_cls;
  logic [11:0]   lsu_csr_addr;
  assign lsu_csr_addr = ls_pipeline.load_store_unit_i.csr_addr;
  assign csr_noasr_sample = cheri_active && resp_cheri_mode && lsu_resp_valid &&
      ls_pipeline.load_store_unit_i.csr_go_q && !debug_mode_i &&
      !ls_pipeline.load_store_unit_i.pcc_asr_bit;
  always_comb begin
    if (ls_pipeline.load_store_unit_i.illegal_csr_insn_i)    csr_asr_cls = CA_ILLEGAL;
    else if (ls_pipeline.load_store_unit_i.csr_cheri)        csr_asr_cls = CA_SCR;
    else if (ls_pipeline.load_store_unit_i.csr_cheri_always_ok) csr_asr_cls = CA_ALWAYS_OK;
    else if (lsu_csr_addr inside {12'hb00, 12'hb02, 12'hb80, 12'hb82})
                                                             csr_asr_cls = CA_CNT_WR;
    else                                                     csr_asr_cls = CA_OTHER;
    if (!lsu_resp_err)                                       csr_out_cls = CO_OK;
    else if (resp_mcause == EXC_CAUSE_ILLEGAL_INSN)          csr_out_cls = CO_ILL;
    else if (resp_mcause == EXC_CAUSE_CHERI_FAULT)           csr_out_cls = CO_ASR;
    else                                                     csr_out_cls = CO_OTHER;
  end

  // KUDU-037: source of an MSHWM update request (store, successful SC, AMO).
  assign mshwm_upd = ls_pipeline.load_store_unit_i.csr_lsu_wr_req_o;

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
      // committer lspl_rdy_o needs sbd_deq of a valid LS entry (AssertLsDsRdyValid).
      illegal_bins rdy_no_out = {2'b01};
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
    // before handle_misaligned_q selects a split request's second bus word.
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
    cp_cheri_req_err: coverpoint lsu_req_info.lschk_err.any_fault
        iff (cheri_active && req_cheri_mode && lsu_req) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }
    cp_cheri_req_cause: coverpoint req_err_cause[4:0]
        iff (cheri_active && req_cheri_mode && lsu_req && lsu_req_info.lschk_err.any_fault) {
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
    // This is check_ls_err's alignment-only result (vio_cause_enc bit 5),
    // not RV32 split alignment.
    cp_align_err_only: coverpoint req_err_cause[5]
        iff (cheri_active && req_cheri_mode && lsu_req) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }

    cp_lr: coverpoint lr_insn iff (us_valid_i) { bins hit = {1'b1}; }
    cp_sc: coverpoint sc_insn iff (us_valid_i) { bins hit = {1'b1}; }
    // SC response polarity and request association are covered by FC_MA_TOP.

    cp_flush:      coverpoint flush_i { bins hit = {1'b1}; }
    // A flush only follows a committed LS error, by which time the LSU and the
    // WB FIFO are drained (AssertLsNotBusyAtFlush).
    cp_flush_busy: coverpoint (flush_i & (lsu_busy | lspl_valid_o)) {
      bins         none = {1'b0};
      illegal_bins hit  = {1'b1};
    }
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
        iff (cheri_active && req_cheri_mode && lsu_req && lsu_req_info.lschk_err.any_fault) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      // check_ls_err sets .sc only for capability stores (AssertReqScFaultIsCap).
      illegal_bins sc_scalar = binsof(cp_is_cap) intersect {1'b0} &&
                               binsof(cp_cheri_req_cause.c_sc);
      // Scalar .align only for LR/SC/AMO, which are never cache_ok
      // (AssertReqScalarAlignUncached).
      illegal_bins align_cached_scalar = binsof(cp_is_cap) intersect {1'b0} &&
                                         binsof(cp_cache_ok) intersect {1'b1} &&
                                         binsof(cp_cheri_req_cause.c_align);
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
      bins done          = (WAIT_GNT => IDLE);
      bins mis_done = (WAIT_RVALID_MIS => IDLE);
      bins hold[] = (IDLE => IDLE), (WAIT_GNT => WAIT_GNT),
                    (WAIT_GNT_MIS => WAIT_GNT_MIS),
                    (WAIT_RVALID_MIS => WAIT_RVALID_MIS);
    }

    cp_data_err_state: coverpoint ls_fsm_cs iff (data_err_i && data_rvalid_i) {
      bins wait_rvalid_mis = {WAIT_RVALID_MIS};
      bins idle = {IDLE};
    }

    cp_split:      coverpoint split_misaligned_access { bins hit = {1'b1}; }
    cp_mis_q:      coverpoint handle_misaligned_q     { bins hit = {1'b1}; }
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

    // KUDU-052: mtval of a split access with a bus error, by failing half.
    cp_split_bus_err_phase: coverpoint {
        split_first_err_q,
        (data_err_i | ls_pipeline.load_store_unit_i.pmp_err_q)}
        iff (split_bus_err) {
      bins second = {2'b01};
      bins first  = {2'b10, 2'b11};
    }
    cp_split_bus_err_mtval: coverpoint split_mtval_cls iff (split_bus_err) {
      bins first_addr  = {SMT_FIRST_ADDR};
      bins second_word = {SMT_SECOND_WORD};
      illegal_bins other = {SMT_OTHER};
    }
    x_split_err_mtval: cross cp_split_bus_err_phase, cp_split_bus_err_mtval
        iff (split_bus_err) {
      illegal_bins first_wrong  = binsof(cp_split_bus_err_phase.first) &&
                                  binsof(cp_split_bus_err_mtval.second_word);
      illegal_bins second_wrong = binsof(cp_split_bus_err_phase.second) &&
                                  binsof(cp_split_bus_err_mtval.first_addr);
    }

    // KUDU-017/018: CSR access without PCC.ASR. Expected outcomes: illegal
    // CSR -> illegal instruction; counter write -> CHERI fault; read-only
    // counter read -> no fault.
    cp_csr_noasr_cls: coverpoint csr_asr_cls iff (csr_noasr_sample) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins illegal   = {CA_ILLEGAL};
      bins cnt_wr    = {CA_CNT_WR};
      bins always_ok = {CA_ALWAYS_OK};
      bins scr       = {CA_SCR};
      bins other     = {CA_OTHER};
    }
    cp_csr_noasr_out: coverpoint csr_out_cls iff (csr_noasr_sample) {
      option.weight = 0;
      bins ok  = {CO_OK};
      bins ill = {CO_ILL};
      bins asr = {CO_ASR};
      illegal_bins other = {CO_OTHER};
    }
    x_csr_asr: cross cp_csr_noasr_cls, cp_csr_noasr_out iff (csr_noasr_sample) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      illegal_bins illegal_not_ill = binsof(cp_csr_noasr_cls.illegal) &&
                                     !binsof(cp_csr_noasr_out.ill);
      illegal_bins cnt_wr_ok       = binsof(cp_csr_noasr_cls.cnt_wr) &&
                                     binsof(cp_csr_noasr_out.ok);
      illegal_bins always_ok_asr   = binsof(cp_csr_noasr_cls.always_ok) &&
                                     binsof(cp_csr_noasr_out.asr);
      // Without ASR, anything legal that is not always_ok faults with ASR.
      ignore_bins not_reachable = (binsof(cp_csr_noasr_cls.cnt_wr) ||
                                   binsof(cp_csr_noasr_cls.scr) ||
                                   binsof(cp_csr_noasr_cls.other)) &&
                                  !binsof(cp_csr_noasr_out.asr);
      ignore_bins always_ok_ill  = binsof(cp_csr_noasr_cls.always_ok) &&
                                   binsof(cp_csr_noasr_out.ill);
    }

    // KUDU-037: a successful SC.W must update MSHWM like a store.
    cp_mshwm_upd_src: coverpoint resp_amo_flag iff (mshwm_upd) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins store = {4'b0000};
      bins sc    = {4'b0010};
      bins amo_w = {4'b1000};
    }

    cp_csr_cheri_asr_err: coverpoint ls_pipeline.load_store_unit_i.csr_cheri_asr_err
        iff (cheri_active && resp_cheri_mode && lsu_resp_valid &&
             ls_pipeline.load_store_unit_i.csr_go_q) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins clear = {1'b0};
      bins error = {1'b1};
    }
    cp_cheri_ls_err: coverpoint resp_lschk_err.any_fault
        iff (cheri_active && resp_cheri_mode && lsu_resp_valid &&
             !ls_pipeline.load_store_unit_i.lsu_req_info_q.is_csr) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins clear = {1'b0};
      bins error = {1'b1};
    }
    cp_ls_align_err_only: coverpoint resp_err_cause[5]
        iff (cheri_active && resp_cheri_mode && lsu_resp_valid &&
             !ls_pipeline.load_store_unit_i.lsu_req_info_q.is_csr &&
             resp_lschk_err.any_fault) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins other_cheri_fault = {1'b0};
      bins alignment_only = {1'b1};
    }
    cp_resp_early_cheri_cause: coverpoint resp_err_cause[4:0]
        iff (cheri_active && resp_cheri_mode && lsu_resp_valid &&
             resp_lschk_err.any_fault &&
             !ls_pipeline.load_store_unit_i.lsu_req_info_q.lschk_err.any_fault) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins c_align = {5'h00};
      bins c_bound = {5'h01};
      bins c_tag   = {5'h02};
      bins c_seal  = {5'h03};
      bins c_ld    = {5'h12};
      // Only plain early loads skip the request-side check, so store causes
      // cannot appear here (AssertRespEarlyCheriCauseReachable).
      illegal_bins store_cause = {5'h13, 5'h15};
      illegal_bins other = default;
    }

    // check_ls_err flags misaligned LR/SC/AMO in every mode; the LSU reports
    // LR as a load and SC/AMO as a store address-misaligned fault. A faulting
    // AMO read phase never issues its write phase, so amo_w is not a goal.
    cp_atomic_align_fault_rv32: coverpoint
        ls_pipeline.load_store_unit_i.lsu_req_info_q.amo_flag
        iff (resp_atomic_align_err && !(cheri_active && resp_cheri_mode)) {
      bins lr    = {4'b0001};
      bins sc    = {4'b0010};
      bins amo_r = {4'b0100};
    }
    cp_atomic_align_fault_cheri: coverpoint
        ls_pipeline.load_store_unit_i.lsu_req_info_q.amo_flag
        iff (resp_atomic_align_err && cheri_active && resp_cheri_mode) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins lr    = {4'b0001};
      bins sc    = {4'b0010};
      bins amo_r = {4'b0100};
    }

    // clrperm and is_load are retained in the response's saved request, not pl_out_t.
    cp_resp_clrperm: coverpoint ls_pipeline.load_store_unit_i.lsu_req_info_q.clrperm
        iff (cheri_active && resp_cheri_mode && lsu_resp_valid &&
             ls_pipeline.load_store_unit_i.lsu_resp_info.is_cap) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins none = {4'h0};
      // clrperm = {~MC,0,~LM,~LG}; expand_perms grants LG/LM only with MC, so
      // clearing MC always clears LG and LM too (AssertRespClrpermMcImpliesLgLm).
      bins some[] = {[4'h1:4'hf]} with (item[2] == 1'b0 && (!item[3] || item[1:0] == 2'b11));
      illegal_bins no_mc_keeps_lg_lm = {[4'h8:4'hf]} with (item[2] == 1'b0 && item[1:0] != 2'b11);
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
    // Memory never holds a tagged capability with RSVD set: only CSetHigh can
    // set it, and its result is untagged (AssertRespTaggedCapEncoding).
    cp_resp_cap_rsvd: coverpoint resp_mem_cap.rsvd
        iff (resp_cap_sample && resp_mem_cap.valid) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins zero = {1'b0};
      illegal_bins set = {1'b1};
    }
    cp_resp_cap_cperms: coverpoint resp_mem_cap.cperms
        iff (resp_cap_sample && resp_mem_cap.valid) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }
    cp_resp_cap_perm_category: coverpoint fcov_cperm_category(resp_mem_cap.cperms)
        iff (resp_cap_sample && resp_mem_cap.valid) {
      option.weight = 0;
      bins memory_capability = {PC_MEMORY};
      bins load_capability = {PC_LOAD};
      bins store_capability = {PC_STORE};
      bins data_only = {PC_DATA};
      bins execute = {PC_EXECUTE};
      bins sealing = {PC_SEAL};
    }
    cp_resp_cap_perm_bits: coverpoint {
        fcov_maskable_permissions(resp_mem_cap.cperms),
        fcov_maskable_permissions(resp_reg_cap.cperms)}
        iff (resp_cap_sample && resp_mem_cap.valid) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      wildcard bins global_00 = {12'b0?????0?????};
      wildcard bins global_10 = {12'b1?????0?????};
      wildcard bins global_11 = {12'b1?????1?????};
      wildcard bins load_global_00 = {12'b?0?????0????};
      wildcard bins load_global_10 = {12'b?1?????0????};
      wildcard bins load_global_11 = {12'b?1?????1????};
      wildcard bins load_mutable_00 = {12'b??0?????0???};
      wildcard bins load_mutable_10 = {12'b??1?????0???};
      wildcard bins load_mutable_11 = {12'b??1?????1???};
      wildcard bins store_00 = {12'b???0?????0??};
      wildcard bins store_10 = {12'b???1?????0??};
      wildcard bins store_11 = {12'b???1?????1??};
      wildcard bins capability_00 = {12'b????0?????0?};
      wildcard bins capability_10 = {12'b????1?????0?};
      wildcard bins capability_11 = {12'b????1?????1?};
      wildcard bins store_local_00 = {12'b?????0?????0};
      wildcard bins store_local_10 = {12'b?????1?????0};
      wildcard bins store_local_11 = {12'b?????1?????1};
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
      bins other = {[5'd7:5'd23], [5'd25:5'd30]};
      // CEXP = EXP ^ 31, so 1..6 is an exponent above the root's 24
      // (AssertRespTaggedCapEncoding).
      illegal_bins above_max = {[5'd1:5'd6]};
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
      // ILLEGAL_INSN comes only from CSR requests, which never set is_cap
      // (AssertIllegalInsnRespNotCap).
      illegal_bins cap_illegal = binsof(cp_out_is_cap) intersect {1'b1} &&
                                 binsof(cp_out_mcause.illegal);
    }
    x_resp_clrperm_1: cross cp_resp_cap_valid, cp_resp_clrperm
        iff (resp_cap_sample) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }
    x_resp_clrperm_2: cross cp_resp_cap_perm_category, cp_resp_clrperm
        iff (resp_cap_sample && resp_mem_cap.valid) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }

    // KUDU-024: CLC permission stripping must also apply in debug mode.
    cp_resp_clrperm_any: coverpoint (|ls_pipeline.load_store_unit_i.lsu_req_info_q.clrperm)
        iff (clrperm_sample) {
      option.weight = 0;
      bins none = {1'b0};
      bins some = {1'b1};
    }
    x_clrperm_dm: cross cp_resp_clrperm_any, cp_debug_mode iff (clrperm_sample) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
    }

    // KUDU-008: LR/SC/AMO bus errors. LR reports a load fault, the others a
    // store/AMO fault, in both AMO phases.
    cp_amo_bus_err_phase: coverpoint resp_amo_flag iff (amo_bus_err) {
      bins lr    = {4'b0001};
      bins sc    = {4'b0010};
      bins amo_r = {4'b0100};
      bins amo_w = {4'b1000};
    }
    cp_amo_bus_err_cause: coverpoint resp_mcause iff (amo_bus_err) {
      option.weight = 0;
      bins load_fault  = {EXC_CAUSE_LOAD_ACCESS_FAULT};
      bins store_fault = {EXC_CAUSE_STORE_ACCESS_FAULT};
    }
    x_amo_bus_err_cause: cross cp_amo_bus_err_phase, cp_amo_bus_err_cause
        iff (amo_bus_err) {
      illegal_bins lr_store = binsof(cp_amo_bus_err_phase.lr) &&
                              binsof(cp_amo_bus_err_cause.store_fault);
      illegal_bins rmw_load = !binsof(cp_amo_bus_err_phase.lr) &&
                              binsof(cp_amo_bus_err_cause.load_fault);
    }
    // KUDU-032/061: the AMO read phase must check SD as well as LD.
    cp_amo_cheri_cause: coverpoint resp_err_cause[4:0] iff (amo_cheri_err) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins c_bound = {5'h01};
      bins c_tag   = {5'h02};
      bins c_seal  = {5'h03};
      bins c_ld    = {5'h12};
      bins c_sd    = {5'h13};
    }
    

    // ======================================================================
    // 12.3 Temporal safety
    // ======================================================================
    // kudu_top ties cheri_tsafe_en = CHERIoTEn (AssertTsafeTiedOn); revisit
    // if it becomes a real input or CSR.
    cp_tsafe_en: coverpoint tsafe_en_i iff (cheri_active) {
      option.weight = ls_pipeline.CHERIoTEn ? 1 : 0;
      bins         on  = {1'b1};
      illegal_bins off = {1'b0};
    }
    // trvk_en / outstanding scalar coverage lives in the bound trvk module.
  endgroup

  cg_ma_lsu u_cg_ma_lsu = new();

  AssertCheriReqCauseReachable: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (cheri_active && req_cheri_mode && lsu_req && lsu_req_info.lschk_err.any_fault) |->
    (req_err_cause[4:0] inside
     {5'h00, 5'h01, 5'h02, 5'h03, 5'h12, 5'h13, 5'h15}))
    else $error("FCOV: LSU CHERI request cause outside check_ls_err encoding");

  AssertRespEarlyCheriCauseReachable: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (cheri_active && resp_cheri_mode && lsu_resp_valid &&
     resp_lschk_err.any_fault &&
     !ls_pipeline.load_store_unit_i.lsu_req_info_q.lschk_err.any_fault) |->
    (resp_err_cause[4:0] inside
     {5'h00, 5'h01, 5'h02, 5'h03, 5'h12}))
    else $error("FCOV: LSU response-only CHERI cause is not a plain-load cause");

  // Twins of the cg_ma_lsu illegal bins that mark structural invariants.
  // Sim-only, like AssertAuipccPccEncoding: memory holds no such tagged capability.
  AssertRespTaggedCapEncoding: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (resp_cap_sample && resp_mem_cap.valid) |->
    (!resp_mem_cap.rsvd && !(resp_mem_cap.cexp inside {[5'd1:5'd6]})))
    else $error("FCOV: loaded tagged capability with RSVD set or CEXP 1..6");

  AssertLsDsRdyValid: assert property (
    @(posedge clk_i) disable iff (!rst_ni) ds_rdy_i |-> lspl_valid_o)
    else $error("FCOV: committer ready for LS pipeline without LS output valid");

  AssertLsNotBusyAtFlush: assert property (
    @(posedge clk_i) disable iff (!rst_ni) flush_i |-> !(lsu_busy || lspl_valid_o))
    else $error("FCOV: LSU busy or WB FIFO valid at flush");

  AssertReqScFaultIsCap: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (cheri_active && req_cheri_mode && lsu_req && lsu_req_info.lschk_err.any_fault &&
     (req_err_cause[4:0] == 5'h15)) |-> lsu_req_info.is_cap)
    else $error("FCOV: SC (store-cap) fault on a scalar request");

  AssertReqScalarAlignUncached: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (cheri_active && req_cheri_mode && lsu_req && lsu_req_info.lschk_err.any_fault &&
     (req_err_cause[4:0] == 5'h00) && !lsu_req_info.is_cap) |-> !lsu_req_info.cache_ok)
    else $error("FCOV: scalar alignment fault on a cacheable request");

  AssertRespClrpermMcImpliesLgLm: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (cheri_active && resp_cheri_mode && lsu_resp_valid &&
     ls_pipeline.load_store_unit_i.lsu_resp_info.is_cap &&
     ls_pipeline.load_store_unit_i.lsu_req_info_q.clrperm[3]) |->
    (ls_pipeline.load_store_unit_i.lsu_req_info_q.clrperm[1:0] == 2'b11))
    else $error("FCOV: clrperm clears MC but keeps LG/LM");

  AssertIllegalInsnRespNotCap: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (cheri_active && wb_cheri_mode && lspl_valid_o && lspl_output_o.err &&
     (lspl_output_o.mcause == EXC_CAUSE_ILLEGAL_INSN)) |-> !lspl_output_o.is_cap)
    else $error("FCOV: illegal-instruction LS response marked as capability");

  AssertTsafeTiedOn: assert property (
    @(posedge clk_i) disable iff (!rst_ni) cheri_active |-> tsafe_en_i)
    else $error("FCOV: tsafe_en low with CHERI active; update cp_tsafe_en");

  AssertRespCapTagMatchesClrperm: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    resp_cap_sample |-> (resp_reg_cap.valid ==
                         (resp_mem_cap.valid &
                          ~ls_pipeline.load_store_unit_i.lsu_req_info_q.clrperm[3])))
    else $error("FCOV: capability load tag result does not match clrperm[3]");

  AssertAmoBusErrCause: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    amo_bus_err |-> ((resp_mcause == EXC_CAUSE_LOAD_ACCESS_FAULT) ==
                     (resp_amo_flag == 4'b0001)))
    else $error("FCOV: LR/SC/AMO bus error reported with the wrong cause (KUDU-008)");

  AssertSplitErrMtval: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    split_bus_err |-> (split_first_err_q ? (split_mtval_cls == SMT_FIRST_ADDR)
                                         : (split_mtval_cls == SMT_SECOND_WORD)))
    else $error("FCOV: split access bus error mtval 0x%08x for addr 0x%08x (KUDU-052)",
                resp_mtval, split_addr);

  AssertCsrNoAsrOutcome: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    csr_noasr_sample |->
      (csr_out_cls != CO_OTHER) &&
      ((csr_asr_cls == CA_ILLEGAL)   -> (csr_out_cls == CO_ILL)) &&
      ((csr_asr_cls == CA_CNT_WR)    -> (csr_out_cls != CO_OK)) &&
      ((csr_asr_cls == CA_ALWAYS_OK) -> (csr_out_cls != CO_ASR)))
    else $error("FCOV: CSR access without ASR: class %s outcome %s (KUDU-017/018)",
                csr_asr_cls.name(), csr_out_cls.name());

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
#(
  parameter int unsigned TagHi = 31
) (
  input logic       clk_i,
  input logic       rst_ni,

  input logic       cache_enable_i,
  input logic       lsu_req_i,
  input pl_fwd_t    fwd_info_o,
  input logic [3:0] line_valid,
  input logic [TagHi-2:0] tags [4],
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
  input logic       waw_act_match,
  input logic       lsu_req_done_i,
  input logic       lsu_req_q,
  input lsu_req_info_t lsu_req_info_i,
  input lsu_req_info_t lsu_req_info_q
);

`ifndef KUDU_FCOV_OFF

  // KUDU-014/033/050: a cacheable load issued while an earlier request is
  // still in flight (lsu_req_q), classed by that request and by the word the
  // load reads relative to it. A capability, misaligned or SC request in
  // flight must block forwarding (dcache.sv rd_data_good).
`ifdef CHERIoT
  localparam bit CapEn = 1'b1;
`else
  localparam bit CapEn = 1'b0;
`endif
  typedef enum logic [2:0] {
    IF_WORD_ST, IF_PART_ST, IF_LOAD, IF_UNAL, IF_CAP, IF_SC, IF_OTHER
  } fcov_inflight_e;
  typedef enum logic [1:0] {REL_SAME, REL_NEXT, REL_OTHER} fcov_inflight_rel_e;
  fcov_inflight_e     inflight_cls;
  fcov_inflight_rel_e inflight_rel;
  logic               ld_fwd_sample;

  always_comb begin
    if (lsu_req_info_q.is_csr || (|lsu_req_info_q.amo_flag[3:2])) inflight_cls = IF_OTHER;
    else if (lsu_req_info_q.amo_flag[1])                         inflight_cls = IF_SC;
    else if (lsu_req_info_q.is_cap)                              inflight_cls = IF_CAP;
    else if (unaligned_access_q)                                 inflight_cls = IF_UNAL;
    else if (lsu_req_info_q.is_load)                             inflight_cls = IF_LOAD;
    else if (lsu_req_info_q.data_type == 2'b00)                  inflight_cls = IF_WORD_ST;
    else                                                         inflight_cls = IF_PART_ST;
    if (lsu_req_info_i.addr[31:2] == lsu_req_info_q.addr[31:2])  inflight_rel = REL_SAME;
    else if (lsu_req_info_i.addr[31:2] == lsu_req_info_q.addr[31:2] + 30'd1)
                                                                 inflight_rel = REL_NEXT;
    else                                                         inflight_rel = REL_OTHER;
  end
  assign ld_fwd_sample = cache_enable_i && lsu_req_i && lsu_req_done_i && lsu_req_q &&
      lsu_req_info_i.is_load && lsu_req_info_i.cache_ok && !lsu_req_info_i.is_cap &&
      !unaligned_access && (lsu_req_info_i.amo_flag == 4'b0000);

  // A misaligned integer access that straddles words addr and addr+4 (the
  // accesses load_store_unit splits), accepted while both words are cached.
  // Lines are checked at acceptance, before unaligned_access_q invalidates them.
  typedef enum logic [1:0] {UA_WORD1, UA_WORD2, UA_WORD3, UA_HALF3} fcov_straddle_e;
  fcov_straddle_e straddle_kind;
  logic           straddle_req, next_word_cached, straddle_both_cached;

  always_comb begin
    straddle_kind = fcov_straddle_e'(lsu_req_info_i.addr[1:0] - 2'd1);
    if (lsu_req_info_i.data_type == 2'b01) straddle_kind = UA_HALF3;
    next_word_cached = 1'b0;
    for (int i = 0; i < 4; i++)
      if (line_valid[i] && tags[i] == lsu_req_info_i.addr[TagHi:2] + 1'b1)
        next_word_cached = 1'b1;
  end
  assign straddle_req = lsu_req_i && lsu_req_done_i && !lsu_req_info_i.is_csr &&
      !lsu_req_info_i.is_cap && (lsu_req_info_i.amo_flag == 4'b0000) &&
      !lsu_req_info_i.lschk_err.any_fault &&
      (((lsu_req_info_i.data_type == 2'b00) && (lsu_req_info_i.addr[1:0] != 2'b00)) ||
       ((lsu_req_info_i.data_type == 2'b01) && (lsu_req_info_i.addr[1:0] == 2'b11)));
  assign straddle_both_cached = straddle_req && cache_enable_i && (|rd_tag_match) &&
                                next_word_cached;

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
    // Both words of a straddling access are cached; read/write x misaligned type.
    cp_unaligned_two_matches: coverpoint {lsu_req_info_i.is_load, straddle_kind}
        iff (straddle_both_cached) {
      bins store_word_off1 = {{1'b0, UA_WORD1}};
      bins store_word_off2 = {{1'b0, UA_WORD2}};
      bins store_word_off3 = {{1'b0, UA_WORD3}};
      bins store_half_off3 = {{1'b0, UA_HALF3}};
      bins load_word_off1  = {{1'b1, UA_WORD1}};
      bins load_word_off2  = {{1'b1, UA_WORD2}};
      bins load_word_off3  = {{1'b1, UA_WORD3}};
      bins load_half_off3  = {{1'b1, UA_HALF3}};
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

    cp_inflight_cls: coverpoint inflight_cls iff (ld_fwd_sample) {
      option.weight = 0;
      bins word_st = {IF_WORD_ST};
      bins part_st = {IF_PART_ST};
      bins load    = {IF_LOAD};
      bins unal    = {IF_UNAL};
      bins cap     = {IF_CAP};
      bins sc      = {IF_SC};
    }
    cp_inflight_rel: coverpoint inflight_rel iff (ld_fwd_sample) {
      option.weight = 0;
      bins same  = {REL_SAME};
      bins next  = {REL_NEXT};
      bins other = {REL_OTHER};
    }
    cp_inflight_hit: coverpoint cache_rd_hit iff (ld_fwd_sample) {
      option.weight = 0;
      bins miss = {1'b0};
      bins hit  = {1'b1};
    }
    x_inflight_fwd: cross cp_inflight_cls, cp_inflight_rel, cp_inflight_hit
        iff (ld_fwd_sample && inflight_cls != IF_CAP) {
      illegal_bins risky_fwd = (binsof(cp_inflight_cls.unal) ||
                                binsof(cp_inflight_cls.sc)) &&
                               binsof(cp_inflight_hit.hit);
      // Same-word bypass forwards only a full-word store's data.
      ignore_bins same_no_byp = (binsof(cp_inflight_cls.part_st) ||
                                 binsof(cp_inflight_cls.load)) &&
                                binsof(cp_inflight_rel.same) && binsof(cp_inflight_hit.hit);
      ignore_bins cap = binsof(cp_inflight_cls.cap);
      // A same-word load behind a full-word store always takes the bypass, so
      // it always hits (AssertWordStSameWordHit).
      illegal_bins word_st_same_miss = binsof(cp_inflight_cls.word_st) &&
                                       binsof(cp_inflight_rel.same) &&
                                       binsof(cp_inflight_hit.miss);
    }
    // A capability store/load spans two words: same word and the next.
    x_inflight_cap: cross cp_inflight_rel, cp_inflight_hit
        iff (ld_fwd_sample && inflight_cls == IF_CAP) {
      option.weight = CapEn;
      illegal_bins cap_fwd = binsof(cp_inflight_hit.hit);
    }
  endgroup

  cg_ma_dcache u_cg_lsu_cache = new();

  AssertNoFwdBehindRiskyReq: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (ld_fwd_sample && (inflight_cls inside {IF_UNAL, IF_CAP, IF_SC})) |-> !cache_rd_hit)
    else $error("FCOV: load forwarded while a %s request is in flight (KUDU-014/033/050)",
                inflight_cls.name());

  AssertWordStSameWordHit: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (ld_fwd_sample && (inflight_cls == IF_WORD_ST) && (inflight_rel == REL_SAME)) |-> cache_rd_hit)
    else $error("FCOV: same-word load behind a full-word store did not hit");

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


// ===========================================================================
// SVA design properties for the load/store pipeline (not coverage).
// Bound to ls_pipeline as u_fcov_sva_lsu; reaches load_store_unit_i, lsu_if_i
// and the WB/WAW FIFOs through explicit bind connections.
// Checks: data bus handshake stability and beat accounting, byte enables /
// address / store lanes against a reference model of the access, load data
// alignment and extension, faulting requests never reach the bus, capability
// tag on stores, error cause/mtval legality, AMO sequencing, lsu_if hold
// protocol, flush/error quiescence, FIFO no-overrun and bounded busy time.
// ===========================================================================
module kudu_sva_lsu
  import super_pkg::*;
  import cheri_pkg::*;
  import csr_pkg::*;
#(
  parameter bit CHERIoTEn = 1'b1
) (
  input logic            clk_i,
  input logic            rst_ni,

  input logic            cheri_pmode,
  input logic            debug_mode_i,
  input logic            flush_i,
  input logic            lsu_err_active,
  input logic            resp_err_latched,
  input logic            csr_op_en_o,

  // --- data bus ---------------------------------------------------------------
  input logic            data_req_o,
  input logic            data_we_o,
  input logic [3:0]      data_be_o,
  input logic            data_is_cap_o,
  input logic [3:0]      data_amo_flag_o,
  input logic [31:0]     data_addr_o,
  input logic [MemW-1:0] data_wdata_o,
  input logic            data_gnt_i,
  input logic            data_rvalid_i,
  input logic            data_err_i,
  input logic [MemW-1:0] data_rdata_i,

  // --- lsu_if -> LSU request, LSU response ------------------------------------
  input logic            lsu_req,
  input lsu_req_info_t   lsu_req_info,
  input logic            lsu_req_done,
  input logic            lsu_resp_valid,
  input logic            lsu_resp_err,
  input pl_out_t         lsu_resp_info,

  // --- internals (hierarchical, see bind) -------------------------------------
  input ls_fsm_e         ls_fsm_cs,
  input logic            handle_misaligned_q,
  input logic            outstanding_resp_q,
  input logic            req_err_q,
  input logic            csr_go_q,
  input logic            ls_go,
  input logic            csr_go,
  input lsu_req_info_t   lsu_req_info_q,
  input logic [2:0]      lsif_fsm_q,
  input logic            req_dly_valid,
  input logic            wb_fifo_wr_rdy,
  input logic            waw_fifo_wvalid,
  input logic            waw_fifo_wr_rdy
);

`ifndef KUDU_FCOV_OFF

  // lsu_if.sv:28 DLY1 encoding (lsif_fsm_e is local to lsu_if)
  localparam logic [2:0] LsifDly1 = 3'h2;
  // bits above the 32-bit integer data (capability metadata/tag); 0 for RV32
  localparam logic [MemW-1:0] MemHiMask = ~MemW'(33'h0_ffff_ffff);
  localparam logic [RegW-1:0] RegHiMask = ~RegW'(33'h0_ffff_ffff);

  // ---------------------------------------------------------------------------
  // Reference model of the accepted access (captured at ls_go)
  // ---------------------------------------------------------------------------
  function automatic logic [2:0] acc_size (logic [1:0] dtype);
    return (dtype == 2'b00) ? 3'd4 : (dtype == 2'b01) ? 3'd2 : 3'd1;
  endfunction

  logic [2:0]  cur_size;
  logic [7:0]  cur_mask8;
  logic [3:0]  ref_be;
  logic [31:0] ref_addr;
  logic        cur_split;

  always_comb begin
    cur_size  = acc_size(lsu_req_info.data_type);
    cur_mask8 = 8'((8'h1 << cur_size) - 8'h1) << lsu_req_info.addr[1:0];
    cur_split = !lsu_req_info.is_cap && (({1'b0, lsu_req_info.addr[1:0]} + cur_size) > 3'd4);
    if (cheri_pmode && lsu_req_info.is_cap)
      ref_be = 4'b1111;
    else
      ref_be = handle_misaligned_q ? cur_mask8[7:4] : cur_mask8[3:0];
    ref_addr = {lsu_req_info.addr[31:2], 2'b00} + (handle_misaligned_q ? 32'h4 : 32'h0);
  end

  logic        m_active, m_split, m_is_cap, m_is_load, m_sign, m_bus_err, m_err_seen;
  logic [1:0]  m_dtype, m_exp_beats, m_gnt_cnt, m_rv_cnt;
  logic [3:0]  m_amo;
  logic [31:0] m_addr, m_lo;
  logic        m_amo_rd_ok;
  logic [31:0] m_amo_rd_addr, m_amo_rd_data;
  logic        bus_gnt;

  assign bus_gnt = data_req_o & data_gnt_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      m_active      <= 1'b0;
      m_split       <= 1'b0;
      m_is_cap      <= 1'b0;
      m_is_load     <= 1'b0;
      m_sign        <= 1'b0;
      m_bus_err     <= 1'b0;
      m_dtype       <= 2'b00;
      m_exp_beats   <= 2'd0;
      m_gnt_cnt     <= 2'd0;
      m_rv_cnt      <= 2'd0;
      m_amo         <= 4'h0;
      m_addr        <= 32'h0;
      m_lo          <= 32'h0;
      m_err_seen    <= 1'b0;
      m_amo_rd_ok   <= 1'b0;
      m_amo_rd_addr <= 32'h0;
      m_amo_rd_data <= 32'h0;
    end else begin
      if (ls_go || csr_go) begin
        m_active    <= 1'b1;
        m_split     <= ls_go && cur_split;
        m_is_cap    <= lsu_req_info.is_cap;
        m_is_load   <= lsu_req_info.is_load;
        m_sign      <= lsu_req_info.sign_ext;
        m_dtype     <= lsu_req_info.data_type;
        m_amo       <= lsu_req_info.amo_flag;
        m_addr      <= lsu_req_info.addr;
        m_exp_beats <= (csr_go || lsu_req_info.lschk_err.any_fault) ? 2'd0 :
                       cur_split ? 2'd2 : 2'd1;
        m_gnt_cnt   <= {1'b0, bus_gnt};
        m_rv_cnt    <= 2'd0;
        m_bus_err   <= 1'b0;
      end else begin
        if (lsu_resp_valid)
          m_active <= 1'b0;
        if (bus_gnt && (m_gnt_cnt != 2'd3))
          m_gnt_cnt <= m_gnt_cnt + 2'd1;
        if (data_rvalid_i) begin
          if (m_rv_cnt != 2'd3)
            m_rv_cnt <= m_rv_cnt + 2'd1;
          if (m_rv_cnt == 2'd0)
            m_lo <= data_rdata_i[31:0];
          if (data_err_i)
            m_bus_err <= 1'b1;
        end
      end

      // error response seen and not yet flushed
      if (flush_i)
        m_err_seen <= 1'b0;
      else if (lsu_resp_valid && lsu_resp_err)
        m_err_seen <= 1'b1;

      // last LSU operation was an error-free AMO read phase
      if (flush_i || ls_go || csr_go)
        m_amo_rd_ok <= 1'b0;
      if (lsu_resp_valid && !lsu_resp_err && !csr_go_q && m_is_load && m_amo[2]) begin
        m_amo_rd_ok   <= !(flush_i || ls_go || csr_go);
        m_amo_rd_addr <= m_addr;
        m_amo_rd_data <= lsu_resp_info.wdata[31:0];
      end
    end
  end

  // Expected load result from the bus words seen by the model.
  logic [63:0] ld_words, ld_shift;
  logic [31:0] ld_ref;
  always_comb begin
    ld_words = m_split ? {data_rdata_i[31:0], m_lo} : {32'h0, data_rdata_i[31:0]};
    ld_shift = ld_words >> {m_addr[1:0], 3'b000};
    case (m_dtype)
      2'b00:   ld_ref = ld_shift[31:0];
      2'b01:   ld_ref = {{16{m_sign & ld_shift[15]}}, ld_shift[15:0]};
      default: ld_ref = {{24{m_sign & ld_shift[7]}},  ld_shift[7:0]};
    endcase
  end

  // CHERI check of the request currently driven to the bus and of the request
  // being answered (same function the RTL uses at lsu_if.sv:53 and :511).
  lschk_err_t bus_chk, resp_chk;
  always_comb begin
    bus_chk  = check_ls_err(cheri_pmode, debug_mode_i, lsu_req_info.cs1_fcap,
                            lsu_req_info.cs2_valid, lsu_req_info.cs2_perms,
                            lsu_req_info.addr, lsu_req_info.is_load,
                            lsu_req_info.is_cap, lsu_req_info.data_type,
                            lsu_req_info.amo_flag);
    resp_chk = check_ls_err(cheri_pmode, debug_mode_i, lsu_req_info_q.cs1_fcap,
                            lsu_req_info_q.cs2_valid, lsu_req_info_q.cs2_perms,
                            lsu_req_info_q.addr, lsu_req_info_q.is_load,
                            lsu_req_info_q.is_cap, lsu_req_info_q.data_type,
                            lsu_req_info_q.amo_flag);
  end

  logic resp_ls;     // response to a load/store (not CSR)
  logic resp_ld_cls; // reported with load causes (load-only; not AMO)
  assign resp_ls     = lsu_resp_valid && !csr_go_q;
  assign resp_ld_cls = lsu_req_info_q.is_load && (lsu_req_info_q.amo_flag[3:2] == 2'b00);

  // busy-time counter for the liveness bound
  logic [7:0] busy_cnt;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)
      busy_cnt <= 8'h0;
    else if (((ls_fsm_cs != IDLE) || (outstanding_resp_q && !lsu_resp_valid)) &&
             (busy_cnt != 8'hff))
      busy_cnt <= busy_cnt + 8'h1;
    else if (!((ls_fsm_cs != IDLE) || (outstanding_resp_q && !lsu_resp_valid)))
      busy_cnt <= 8'h0;
  end

  // ---------------------------------------------------------------------------
  // Data bus protocol
  // ---------------------------------------------------------------------------

  // load_store_unit.sv:394-445 a request waiting for grant is never withdrawn
  AssertBusReqHeld: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (data_req_o && !data_gnt_i) |=> data_req_o)
    else $error("SVA: data_req_o withdrawn before data_gnt_i");

  // load_store_unit.sv:125,671-678 address/attributes/store data stable while waiting for grant
  AssertBusAttrStable: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (data_req_o && !data_gnt_i) |=>
      ($stable(data_addr_o) && $stable(data_we_o) && $stable(data_be_o) &&
       $stable(data_is_cap_o) && $stable(data_amo_flag_o) &&
       (!data_we_o || $stable(data_wdata_o))))
    else $error("SVA: data bus attributes changed while waiting for grant");

  // load_store_unit.sv:412,648 rvalid only arrives when the LSU expects a response
  AssertRvalidExpected: assert property (@(posedge clk_i) disable iff (!rst_ni)
    data_rvalid_i |->
      ((ls_fsm_cs == WAIT_RVALID_MIS) ||
       ((ls_fsm_cs == IDLE) && outstanding_resp_q && !req_err_q && !csr_go_q)))
    else $error("SVA: data_rvalid_i while the LSU is not waiting for a response");

  // load_store_unit.sv:376-393 every granted bus beat belongs to an accepted access
  // and never exceeds its expected beat count (1, or 2 for a split access)
  AssertNoExtraBusBeat: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (bus_gnt && !ls_go) |-> (m_active && (m_gnt_cnt < m_exp_beats)))
    else $error("SVA: unexpected data bus beat");

  // load_store_unit.sv:376-445,648 a load/store response comes after exactly the
  // expected beats: 0 for a request-side fault, 2 for a split access, else 1
  AssertAccessBeatCount: assert property (@(posedge clk_i) disable iff (!rst_ni)
    resp_ls |-> (m_active && (m_gnt_cnt == m_exp_beats) &&
                 ((m_rv_cnt + {1'b0, data_rvalid_i}) == m_exp_beats)))
    else $error("SVA: LSU response with %0d grants / %0d rvalids, expected %0d",
                m_gnt_cnt, m_rv_cnt, m_exp_beats);

  // load_store_unit.sv:133-189 byte enables match access size and offset
  // (first or second word of a split access; capabilities use all four lanes)
  AssertBusBeMatchesAccess: assert property (@(posedge clk_i) disable iff (!rst_ni)
    data_req_o |-> (data_be_o == ref_be))
    else $error("SVA: data_be_o %b, expected %b", data_be_o, ref_be);

  // load_store_unit.sv:125,668-671 bus address is the access word (second part: next word)
  AssertBusAddrMatchesAccess: assert property (@(posedge clk_i) disable iff (!rst_ni)
    data_req_o |-> (data_addr_o == ref_addr))
    else $error("SVA: data_addr_o 0x%08x, expected 0x%08x", data_addr_o, ref_addr);

  // load_store_unit.sv:196-212 each enabled lane of an integer store carries the
  // matching register byte (rotation by the byte offset)
  for (genvar b = 0; b < 4; b++) begin : gen_st_lane
    AssertStoreDataLanes: assert property (@(posedge clk_i) disable iff (!rst_ni)
      (data_req_o && data_we_o && !lsu_req_info.is_cap && data_be_o[b]) |->
        kudu_fcov_pkg::sva_xok(data_wdata_o[8*b +: 8] ==
                               lsu_req_info.wdata[8*((b - lsu_req_info.addr[1:0]) & 3) +: 8]))
      else $error("SVA: store lane %0d carries the wrong byte", b);
  end

  // load_store_unit.sv:209 integer stores never write a capability tag/metadata
  AssertIntStoreNoTag: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (data_req_o && data_we_o && !data_is_cap_o) |-> ((data_wdata_o & MemHiMask) == '0))
    else $error("SVA: integer store drives non-zero upper (capability) bits");

  // load_store_unit.sv:377 + lsu_if.sv:53-71 a checked (non-early) access that
  // reaches the bus passes the CHERI/alignment check evaluated on the bus request
  AssertNoFaultingReqOnBus: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (data_req_o && !lsu_req_info.early_load) |-> !bus_chk.any_fault)
    else $error("SVA: faulting request driven on the data bus");

  // cheri_pkg.sv:1037,1043 checked capability accesses on the bus are 8-byte aligned
  // (debug mode is exempt: check_ls_err disables all CHERI checks there by design)
  AssertCapAccess8Aligned: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (data_req_o && cheri_pmode && !debug_mode_i && data_is_cap_o &&
     !lsu_req_info.early_load) |->
      (lsu_req_info.addr[2:0] == 3'b000))
    else $error("SVA: capability bus access at a non 8-byte aligned address");

  // cheri_pkg.sv:1047,1052 + cmplx_unit.sv:166 LR/SC/AMO bus accesses are aligned full words
  AssertAmoBusWordAligned: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (data_req_o && (data_amo_flag_o != 4'h0)) |->
      ((lsu_req_info.addr[1:0] == 2'b00) && (data_be_o == 4'b1111) &&
       !handle_misaligned_q))
    else $error("SVA: misaligned or partial LR/SC/AMO bus access");

`ifndef KUDU_CUSTOM_ADDR_DECODE
  // ls_pipeline.sv:227 early (response-checked) loads only reach side-effect-free RAM
  AssertEarlyLoadSideEffectFree: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (data_req_o && lsu_req_info.early_load && !handle_misaligned_q) |->
      (!data_we_o && (data_amo_flag_o == 4'h0) && (data_addr_o[31:24] == 8'h80)))
    else $error("SVA: unchecked early load outside the early-load region");

  // ls_pipeline.sv:93-96,227 + load_store_unit.sv:125 the second beat of a split
  // early load also stays in the early-load region (decode looks at the base only).
  // Waived (INT-3, sim/testplan/integration_issues.md); an expected CEX in fv_kudu_fcov.tcl.
  AssertEarlyLoadSplitInRegion: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (data_req_o && lsu_req_info.early_load && handle_misaligned_q) |->
      (data_addr_o[31:24] == 8'h80))
    else $error("SVA: second beat of an unchecked early load leaves the early-load region");
`endif

  if (CHERIoTEn) begin : gen_cap_tag
    // ls_pipeline.sv:217 + lsu_if.sv:70 capability store tag = source tag & ~SLC violation
    AssertCapStoreTag: assert property (@(posedge clk_i) disable iff (!rst_ni)
      (data_req_o && data_we_o && data_is_cap_o && cheri_pmode) |->
        (data_wdata_o[MemW-1] == (lsu_req_info.cs2_valid && !bus_chk.slc)))
      else $error("SVA: capability store tag does not match cs2 tag/SLC check");
  end

  // ---------------------------------------------------------------------------
  // Load data
  // ---------------------------------------------------------------------------

  // load_store_unit.sv:228-340,617-622 integer load data is the addressed bytes,
  // re-assembled across a split access and sign/zero extended
  AssertLoadDataExt: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (resp_ls && !lsu_resp_err && m_is_load && !m_is_cap && !m_amo[1] && !m_amo[3]) |->
      kudu_fcov_pkg::sva_xok(((lsu_resp_info.wdata[31:0] == ld_ref) && ((lsu_resp_info.wdata & RegHiMask) == '0))))
    else $error("SVA: load data 0x%08x, expected 0x%08x",
                lsu_resp_info.wdata[31:0], ld_ref);

  // ---------------------------------------------------------------------------
  // Errors
  // ---------------------------------------------------------------------------

  // load_store_unit.sv:644-646 a load/store reports an error iff a bus beat erred
  // or the CHERI/alignment check (request or response side) failed
  AssertLsErrIffCause: assert property (@(posedge clk_i) disable iff (!rst_ni)
    resp_ls |-> (lsu_resp_err ==
                 (m_bus_err || (data_rvalid_i && data_err_i) ||
                  (!lsu_req_info_q.is_csr &&
                   (resp_chk.any_fault || lsu_req_info_q.lschk_err.any_fault)))))
    else $error("SVA: LSU error flag does not match bus/check errors");

  // load_store_unit.sv:588-612 error mcause of a load/store is legal for the
  // access class (CSR responses are left to AssertCsrNoAsrOutcome, KUDU-076)
  AssertRespErrCauseLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (lsu_resp_valid && lsu_resp_err && !csr_go_q) |->
      (resp_ld_cls ? (lsu_resp_info.mcause inside {6'(EXC_CAUSE_LOAD_ADDR_MISALIGN),
                                                    6'(EXC_CAUSE_LOAD_ACCESS_FAULT),
                                                    6'(EXC_CAUSE_CHERI_FAULT)}) :
                     (lsu_resp_info.mcause inside {6'(EXC_CAUSE_STORE_ADDR_MISALIGN),
                                                    6'(EXC_CAUSE_STORE_ACCESS_FAULT),
                                                    6'(EXC_CAUSE_CHERI_FAULT)})))
    else $error("SVA: illegal LSU error mcause 0x%0x", lsu_resp_info.mcause);

  // load_store_unit.sv:592-596 misaligned trap only for a truly misaligned
  // capability or LR/SC/AMO access; mtval is the full access address
  AssertMisalignTrapInfo: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (resp_ls && lsu_resp_err &&
     (lsu_resp_info.mcause inside {6'(EXC_CAUSE_LOAD_ADDR_MISALIGN),
                                    6'(EXC_CAUSE_STORE_ADDR_MISALIGN)})) |->
      ((lsu_resp_info.mtval == lsu_req_info_q.addr) &&
       (lsu_req_info_q.is_cap ? (lsu_req_info_q.addr[2:0] != 3'b000) :
        ((lsu_req_info_q.amo_flag != 4'h0) && (lsu_req_info_q.addr[1:0] != 2'b00)))))
    else $error("SVA: misaligned trap for an aligned/non-AMO access or bad mtval");

  // load_store_unit.sv:601-604 non-split access fault: mtval is the access address
  AssertAccessFaultMtval: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (resp_ls && lsu_resp_err && !m_split &&
     (lsu_resp_info.mcause inside {6'(EXC_CAUSE_LOAD_ACCESS_FAULT),
                                    6'(EXC_CAUSE_STORE_ACCESS_FAULT)})) |->
      (lsu_resp_info.mtval == lsu_req_info_q.addr))
    else $error("SVA: access fault mtval 0x%08x, expected 0x%08x",
                lsu_resp_info.mtval, lsu_req_info_q.addr);

  // ---------------------------------------------------------------------------
  // AMO sequencing (cmplx_unit.sv:160-170)
  // ---------------------------------------------------------------------------

  // an AMO write phase only follows an error-free AMO read of the same address
  AssertAmoWriteFollowsGoodRead: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (ls_go && lsu_req_info.amo_flag[3]) |->
      (m_amo_rd_ok && (lsu_req_info.addr == m_amo_rd_addr)))
    else $error("SVA: AMO write phase without a matching good AMO read");

  // load_store_unit.sv:627-634,660 the AMO write phase returns the AMO read data
  AssertAmoWriteReturnsReadData: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (resp_ls && !lsu_resp_err && m_amo[3]) |->
      (lsu_resp_info.wdata[31:0] == m_amo_rd_data))
    else $error("SVA: AMO result is not the value read by the AMO read phase");

  // ---------------------------------------------------------------------------
  // lsu_if -> LSU request protocol
  // ---------------------------------------------------------------------------

  // lsu_if.sv:96-133 a pending request is held stable until lsu_req_done (or flush)
  AssertLsifReqHeld: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (lsu_req && !lsu_req_done && !flush_i) |=> (lsu_req && $stable(lsu_req_info)))
    else $error("SVA: lsu_if changed/dropped a request before lsu_req_done");

  // load_store_unit.sv:125,135,198,672-678 while the LSU FSM is busy, its input
  // request is still presented and equals the captured copy
  AssertLsuReqHeldWhileBusy: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (ls_fsm_cs != IDLE) |-> (lsu_req && kudu_fcov_pkg::sva_xok(lsu_req_info == lsu_req_info_q)))
    else $error("SVA: LSU busy but lsu_if no longer presents the same request");

  // lsu_if.sv:109-118 the DLY1 state always holds a valid delayed request
  // (otherwise a stale req_dly_q could be moved to the hold register and issued)
  AssertLsifDly1Valid: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (lsif_fsm_q == LsifDly1) |-> req_dly_valid)
    else $error("SVA: lsu_if in DLY1 without a valid delayed request");

  // ---------------------------------------------------------------------------
  // Error / flush quiescence
  // ---------------------------------------------------------------------------

  // ls_pipeline.sv:238-249 a pipeline flush is only caused by a load/store/CSR error
  AssertFlushOnlyOnLsErr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    flush_i |-> lsu_err_active)
    else $error("SVA: flush without a pending LS pipeline error");

  // load_store_unit.sv:368-460 flush never hits an in-flight LSU access
  // (the LSU and lsu_if do not cancel bus transactions on flush)
  AssertLsuIdleAtFlush: assert property (@(posedge clk_i) disable iff (!rst_ni)
    flush_i |-> ((ls_fsm_cs == IDLE) && !ls_go && !csr_go &&
                 !(outstanding_resp_q && !lsu_resp_valid)))
    else $error("SVA: flush while the LSU has an access in flight");

  // ls_pipeline.sv:247-249 after an error response no memory or CSR side effect
  // happens until the flush
  AssertNoSideEffectAfterErr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_err_seen |-> (!data_req_o && !csr_op_en_o))
    else $error("SVA: memory/CSR access issued after an LSU error, before flush");

  // ---------------------------------------------------------------------------
  // FIFOs and liveness
  // ---------------------------------------------------------------------------

  // ls_pipeline.sv:325-343 wr_rdy2 backpressure prevents a WB FIFO overrun
  AssertWbFifoNoOverrun: assert property (@(posedge clk_i) disable iff (!rst_ni)
    lsu_resp_valid |-> wb_fifo_wr_rdy)
    else $error("SVA: LSU response written to a full WB FIFO");

  // ls_pipeline.sv:345-353 the WAW tracking FIFO never overruns
  AssertWawFifoNoOverrun: assert property (@(posedge clk_i) disable iff (!rst_ni)
    waw_fifo_wvalid |-> waw_fifo_wr_rdy)
    else $error("SVA: WAW tracking FIFO written while full");

  // load_store_unit.sv:368-448 an accepted access completes in bounded time
  // (bus waits are bounded by the environment / memory model)
  AssertLsuNeverStuck: assert property (@(posedge clk_i) disable iff (!rst_ni)
    busy_cnt < 8'd100)
    else $error("SVA: LSU busy for 100 cycles");

`endif  // KUDU_FCOV_OFF

endmodule


// ===========================================================================
// SVA for the forwarding cache.  Bound to dcache by module name (it sits in
// an unnamed generate block, ls_pipeline.sv:373).
// Checks: only cacheable addresses are cached, and after a store/fill
// response every still-valid line for that word holds the new data.
// ===========================================================================
module kudu_sva_dcache
  import super_pkg::*;
#(
  parameter int unsigned TagHi = 31
) (
  input logic             clk_i,
  input logic             rst_ni,

  input logic             lsu_resp_valid_i,
  input logic             lsu_resp_err_i,
  input logic [MemW-1:0]  data_rdata_i,
  input lsu_req_info_t    lsu_req_info_q,
  input logic             rd_hit_q,
  input logic             unaligned_access_q,
  input logic [3:0]       line_valid,
  input logic [TagHi-2:0] tags [4],
  input logic [31:0]      cache_mem [4]
);

`ifndef KUDU_FCOV_OFF

  // Snapshot of a completed, error-free, word-aligned integer access.
  logic        s_chk, s_cap;
  logic [31:0] s_addr, s_data;
  logic [3:0]  s_be;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      s_chk  <= 1'b0;
      s_cap  <= 1'b0;
      s_addr <= 32'h0;
      s_data <= 32'h0;
      s_be   <= 4'h0;
    end else begin
      s_chk  <= lsu_resp_valid_i && !lsu_resp_err_i && !lsu_req_info_q.is_csr &&
                !unaligned_access_q &&
                (lsu_req_info_q.is_cap ||
                 (lsu_req_info_q.is_load ? !rd_hit_q : (lsu_req_info_q.amo_flag[1] == 1'b0)));
      s_cap  <= lsu_req_info_q.is_cap;
      s_addr <= lsu_req_info_q.addr;
      s_data <= lsu_req_info_q.is_load ? data_rdata_i[31:0] :
                (lsu_req_info_q.wdata[31:0] << {lsu_req_info_q.addr[1:0], 3'b000});
      s_be   <= lsu_req_info_q.is_load ? 4'b1111 :
                (lsu_req_info_q.data_type == 2'b00) ? 4'b1111 :
                (lsu_req_info_q.data_type == 2'b01) ? (4'b0011 << lsu_req_info_q.addr[1:0]) :
                                                      (4'b0001 << lsu_req_info_q.addr[1:0]);
    end
  end

  for (genvar i = 0; i < 4; i++) begin : gen_line
`ifndef KUDU_CUSTOM_ADDR_DECODE
    // dcache.sv:304 + ls_pipeline.sv:228 only cacheable (0x80xx_xxxx) words are cached
    AssertCacheLineCacheable: assert property (@(posedge clk_i) disable iff (!rst_ni)
      line_valid[i] |-> (tags[i][TagHi-2 -: 8] == 8'h80))
      else $error("SVA: dcache line %0d holds a non-cacheable address", i);
`endif

    // dcache.sv:262-310 after a good integer store/fill, a valid line tagged with
    // that word holds the stored bytes / the fill data; after a capability
    // access no line of that 8-byte granule stays valid ('===': in simulation a
    // sub-word load fills the line with the X lanes the memory model returns)
    AssertCacheCoherentAfterResp: assert property (@(posedge clk_i) disable iff (!rst_ni)
      (s_chk && line_valid[i] &&
       (s_cap ? (tags[i][TagHi-2:1] == s_addr[TagHi:3]) : (tags[i] == s_addr[TagHi:2]))) |->
        (!s_cap &&
         (!s_be[0] || (cache_mem[i][ 7: 0] === s_data[ 7: 0])) &&
         (!s_be[1] || (cache_mem[i][15: 8] === s_data[15: 8])) &&
         (!s_be[2] || (cache_mem[i][23:16] === s_data[23:16])) &&
         (!s_be[3] || (cache_mem[i][31:24] === s_data[31:24]))))
      else $error("SVA: dcache line %0d stale after a completed access (cap %0b addr 0x%08x data 0x%08x be %b; line tag 0x%0x data 0x%08x)",
                  i, s_cap, s_addr, s_data, s_be, tags[i], cache_mem[i]);
  end

`endif  // KUDU_FCOV_OFF

endmodule


// ===========================================================================
// SVA for the capability revocation (load filter) stage.  Bound to
// cheri_trvk_stage by module name (inside gen_trvk, ls_pipeline.sv:383).
// Checks: each revocation slot matches the CLC that retired three cycles
// earlier, the tag-map read address is that of the loaded capability's base,
// and a tag is cleared only for a tagged, error-free load whose base is in
// the heap and whose revocation bit was set.
// ===========================================================================
`ifdef CHERIoT
module kudu_sva_trvk
  import cheri_pkg::*;
#(
  parameter int unsigned HeapBase  = 32'h2001_0000,
  parameter int unsigned TSMapSize = 1024
) (
  input logic        clk_i,
  input logic        rst_ni,

  input logic        clc_valid_i,
  input logic [4:0]  clc_rd_i,
  input logic        clc_err_i,
  input reg_cap_t    clc_rcap_i,
  input logic [4:0]  trvk_addr_o,
  input logic        trvk_en_o,
  input logic        trvk_clrtag_o,
  input logic        tsmap_cs_o,
  input logic [15:0] tsmap_addr_o,
  input logic [31:0] tsmap_rdata_i
);

`ifndef KUDU_FCOV_OFF

  function automatic logic [31:0] cap_base (reg_cap_t cap);
    op_cap_t ocap;
    ocap = reg2opcap(cap);
    return 32'(get_bound33(ocap.base9, {2{ocap.base_cor}}, ocap.exp, ocap.addr));
  endfunction

  logic [2:0]  v_q, good_q;
  logic [4:0]  rd_q [3];
  reg_cap_t    cap_q;
  logic [31:0] base1;
  logic        heap2, heap2_q;
  logic [4:0]  bit2;
  logic        rev3;

  // byte offset of the base from the heap base; bits [7:3] select the bit
  // (8-byte granule) and [23:8] the 32-bit tag-map word
  logic [31:0] off1;
  logic        in_heap1;
  assign base1    = cap_base(cap_q);
  assign off1     = base1 - HeapBase;
  // base in [HeapBase, HeapBase + TSMapSize*32*8)
  assign in_heap1 = (base1 >= HeapBase) && ((off1 >> 8) < TSMapSize);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      v_q    <= '0;
      good_q <= '0;
      rd_q[0] <= '0;
      rd_q[1] <= '0;
      rd_q[2] <= '0;
      cap_q  <= NULL_REG_CAP;
      heap2  <= 1'b0;
      heap2_q <= 1'b0;
      bit2   <= '0;
      rev3   <= 1'b0;
    end else begin
      v_q    <= {v_q[1:0], clc_valid_i};
      good_q <= {good_q[1:0], clc_valid_i && !clc_err_i && clc_rcap_i.valid};
      rd_q[0] <= clc_rd_i;
      rd_q[1] <= rd_q[0];
      rd_q[2] <= rd_q[1];
      if (clc_valid_i && !clc_err_i)
        cap_q <= clc_rcap_i;
      heap2  <= in_heap1;
      heap2_q <= heap2;
      bit2   <= off1[7:3];
      rev3   <= tsmap_rdata_i[bit2];
    end
  end

  // cheri_trvk_stage.sv:53-56,74-85 revocation slot matches the CLC retired 3 cycles ago
  AssertTrvkMatchesClc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (trvk_en_o == v_q[2]) && (!trvk_en_o || (trvk_addr_o == rd_q[2])))
    else $error("SVA: trvk slot does not match the retired CLC");

  // cheri_trvk_stage.sv:44-52 tag-map read is for the good CLC one cycle ago, at
  // the word that holds the revocation bit of its base
  AssertTsmapAddrMatchesBase: assert property (@(posedge clk_i) disable iff (!rst_ni)
    tsmap_cs_o |-> (good_q[0] && (tsmap_addr_o == off1[23:8])))
    else $error("SVA: tag-map read address does not match the loaded cap base");

  // cheri_trvk_stage.sv:55 a tag is cleared only for a tagged, error-free CLC
  // whose base lies in the revocable heap and whose revocation bit is set
  AssertTrvkClrtagJustified: assert property (@(posedge clk_i) disable iff (!rst_ni)
    trvk_clrtag_o |-> (trvk_en_o && good_q[2] && heap2_q && rev3))
    else $error("SVA: capability tag cleared without a set revocation bit");

`endif  // KUDU_FCOV_OFF

endmodule
`endif  // CHERIoT
