// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// FC_MA_IF -- instruction fetch, prefetch buffer, fetch FIFO, alt-path
// allocation and branch prediction.  Bound to rtl/if_stage.sv, reaching into
// branch_predict_i and prefetch_buffer_i.
//
// See doc/functional_coverage_plan.md section 8.

module kudu_fcov_if
  import super_pkg::*;
  import kudu_fcov_pkg::*;
#(
  parameter int unsigned BhtSize       = 16,
  parameter int unsigned PrefetchDepth = 3,
  parameter bit          AltEnable     = 1'b0,
  parameter bit          InstrBufEn    = 1'b1,
  parameter bit          PredictRA     = 1'b0
) (
  input logic         clk_i,
  input logic         rst_ni,

  // --- fetch request / downstream handshake ---------------------------------
  input logic         req_i,
  input logic         instr_req_o,
  input logic         instr_gnt_i,
  input logic         instr_rvalid_i,
  input logic         instr_err_i,
  input logic         if_busy_o,
  input logic         prefetch_busy,
  input logic [1:0]   if_valid_o,
  input logic [1:0]   ds_rdy_i,
  input ir_reg_t      if_instr0_o,
  input ir_reg_t      if_instr1_o,

  // --- redirect --------------------------------------------------------------
  input logic         ex_pc_set_i,
  input logic [31:0]  ex_pc_target_i,
  input logic         ex_bp_init_i,
  input ex_alt_ctrl_t ex_alt_ctrl_i,
  input logic         alloc_alt,
  input logic         alt_has_free,
  input logic [1:0]   alt_free_id,

  // --- prefetch buffer -------------------------------------------------------
  input logic [PrefetchDepth-1:0] rdata_outstanding_q,
  input logic [PrefetchDepth-1:0] branch_discard_q,
  input logic                     discard_req_q,
  input logic                     fifo_clear,
  input logic [PrefetchDepth-1:0] fifo_busy,

  // --- fetch FIFO ------------------------------------------------------------
  input int unsigned fifo_occupancy,   // $countones of the FIFO valid vector
  input logic [1:0]   alt_status,       // one bit per allocated alt entry

  // --- branch prediction -----------------------------------------------------
  input logic         pdt_en_i,
  input logic [1:0]   pdt_valid_o,
  input ir_reg_t      pdt_instr0,
  input ir_reg_t      pdt_instr1,
  input logic [1:0]   bp_is_branch,
  input logic [1:0]   bp_is_jal,
  input logic [1:0]   bp_is_jalr_ra,
  input logic [1:0]   pdt_branch_go,
  input logic [1:0]   pdt_jal_go,
  input logic [1:0]   pdt_jalr_go,
  input logic [31:0]  cur_ra32_i,
  input logic [1:0]   pdt_pc_set,
  input logic [1:0]   bht_rdata0,
  input logic [1:0]   bht_rdata1,
  input logic         fetch_instr0_is_comp,

  // --- prediction outcome from EX -------------------------------------------
  input ex_bp_info_t  ex_bp_info_i
);

`ifndef KUDU_FCOV_OFF

  localparam int unsigned BhtAW = $clog2(BhtSize);
  localparam int unsigned BhtLo = 1;
  localparam int unsigned BhtHi = BhtLo + BhtAW - 1;
  localparam int unsigned FifoDepth = AltEnable ? PrefetchDepth + 4 : PrefetchDepth + 1;
  typedef logic [PrefetchDepth-1:0] discard_mask_t;
  typedef logic [PrefetchDepth:0] discard_state_t;

  function automatic bit is_discard_prefix(discard_mask_t mask);
    return (mask & (mask + discard_mask_t'(1))) == '0;
  endfunction

  fcov_pdt_src_e pdt_src;
  logic          bht_update;
  logic          bht_dual_update;
  logic          bht_slot1_dropped;

  typedef enum logic [1:0] {
    PDT_CAND_NONE, PDT_CAND_BRANCH, PDT_CAND_JAL, PDT_CAND_JALR
  } fcov_pdt_cand_e;

  function automatic fcov_pdt_cand_e fcov_pdt_cand(logic is_branch,
                                                   logic is_jal,
                                                   logic is_jalr);
    if (is_branch) return PDT_CAND_BRANCH;
    if (is_jal)    return PDT_CAND_JAL;
    if (is_jalr)   return PDT_CAND_JALR;
    return PDT_CAND_NONE;
  endfunction

  fcov_pdt_cand_e pdt_cand0, pdt_cand1;

  assign pdt_src = fcov_pdt_src(pdt_branch_go, pdt_jal_go, pdt_jalr_go);

  // KUDU-049: set from reset until the predicted return address first changes,
  // so a return predicted in that window uses the reset value of cur_ra32.
  logic [31:0] ra_prev_q;
  logic        ra_prev_vld_q, ra_fresh_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ra_prev_q     <= '0;
      ra_prev_vld_q <= 1'b0;
      ra_fresh_q    <= 1'b1;
    end else begin
      ra_prev_q     <= cur_ra32_i;
      ra_prev_vld_q <= 1'b1;
      if (ra_prev_vld_q && (cur_ra32_i != ra_prev_q)) ra_fresh_q <= 1'b0;
    end
  end
  assign pdt_cand0 = fcov_pdt_cand(pdt_branch_go[0], pdt_jal_go[0], pdt_jalr_go[0]);
  assign pdt_cand1 = fcov_pdt_cand(pdt_branch_go[1], pdt_jal_go[1], pdt_jalr_go[1]);

  assign bht_update      = |ex_bp_info_i.is_branch;
  assign bht_dual_update = &ex_bp_info_i.is_branch;

  // Finding F-19.  Both EX slots resolved a branch that indexes the same BHT
  // entry, so bht_entry_sel == 2'b11 and the mux at branch_predict.sv:195-196
  // takes slot 0 unconditionally -- slot 1's outcome is silently discarded and
  // the counter is trained on the wrong branch.  The index arithmetic is
  // duplicated from branch_predict.sv:56-59 because bht_entry_sel lives inside
  // a generate block and cannot be reached by a bind.
  assign bht_slot1_dropped =
      bht_dual_update &&
      (ex_bp_info_i.pc0[BhtHi:BhtLo] == ex_bp_info_i.pc1[BhtHi:BhtLo]);

  // ==========================================================================
  // FC_MA_IF - instruction fetch stage
  // ==========================================================================
  covergroup cg_ma_if @(posedge clk_i iff rst_ni);
    option.per_instance = 1;
    option.name         = "FC_MA_IF";

    // ======================================================================
    // 8.1 Fetch request and bus handshake
    // ======================================================================

    cp_req:      coverpoint req_i;
    cp_instr_req: coverpoint instr_req_o;
    // if_busy_o is prefetch_busy (if_stage.sv:139); the bits cannot differ
    // (AssertIfBusyEqPrefetchBusy).
    cp_busy:     coverpoint {prefetch_busy, if_busy_o} {
      bins idle = {2'b00};
      bins busy = {2'b11};
      illegal_bins split = {2'b01, 2'b10};
    }

    // Fetch-side backpressure: the request is up but the bus has not granted.
    cp_req_no_gnt: coverpoint (instr_req_o & ~instr_gnt_i) { bins stalled = {1'b1}; }

    // Outstanding fetches.  The prefetch buffer tracks up to PrefetchDepth.
    // $countones returns int, so an open-ended {[4:$]} bin would span the whole
    // signed 32-bit range and VCS drops it ("Warning-[PSBU] Invalid values in
    // bin") -- a silently deleted bin.  The count cannot exceed the vector
    // width, so the parameter bounds the range exactly and no bin is either
    // discarded or left permanently unreachable when PrefetchDepth < 4.
    cp_outstanding: coverpoint $countones(rdata_outstanding_q) {
      bins n[] = {[0:PrefetchDepth]};
    }

    // Pending discard state, not a response event. Redirects mark older
    // requests first; bit 0 is oldest, so the bitmap is a low-order prefix.
    cp_discard: coverpoint {branch_discard_q, discard_req_q} {
      bins state[] = {[discard_state_t'('0):discard_state_t'('1)]}
        with (is_discard_prefix(discard_mask_t'(item >> 1)));
      illegal_bins non_prefix = {[discard_state_t'('0):discard_state_t'('1)]}
        with (!is_discard_prefix(discard_mask_t'(item >> 1)));
    }

    cp_fetch_err: coverpoint instr_err_i iff (instr_rvalid_i) {
      bins ok  = {1'b0};
      bins err = {1'b1};
    }

    cp_fifo_clear: coverpoint fifo_clear { bins hit = {1'b1}; }
    // Bounded by the parameter for the same reason as cp_outstanding.
    cp_fifo_busy:  coverpoint $countones(fifo_busy) {
      bins n[] = {[0:PrefetchDepth]};
    }

    // Match fetch_fifo64.DEPTH, including the extra shadow-fetch storage.
    cp_fifo_occupancy: coverpoint fifo_occupancy {
      bins empty = {0};
      bins n[]   = {[1:FifoDepth]};
    }

    cp_alt_occupancy: coverpoint $countones(alt_status) {
      bins n[] = {[0:(AltEnable ? 2 : 0)]};
    }

    // ======================================================================
    // 8.1a Prefetch arbitration and fetch_fifo64 word/halfword handling
    // ======================================================================
    cp_prefetch_capacity: coverpoint {
        if_stage.prefetch_buffer_i.fifo_ready,
        if_stage.prefetch_buffer_i.rdata_outstanding_q[PrefetchDepth-1]}
        iff (req_i && !if_stage.prefetch_buffer_i.branch_i &&
             !if_stage.prefetch_buffer_i.valid_req_q) {
      bins fifo_limited = {2'b00};
      bins outstanding_limited = {2'b01};
      bins available = {2'b10};
    }
    cp_prefetch_redirect_request: coverpoint {
        if_stage.prefetch_buffer_i.valid_req_q, instr_gnt_i}
        iff (if_stage.prefetch_buffer_i.valid_req &&
             if_stage.prefetch_buffer_i.branch_i) {
      bins new_wait = {2'b00};
      bins new_grant = {2'b01};
      bins held_wait = {2'b10};
      bins held_grant = {2'b11};
    }

    // cp_fifo_occupancy above already covers the registered word count.
    // This event view records how much buffered data a redirect encounters.
    cp_fifo_clear_level: coverpoint
        $countones(if_stage.prefetch_buffer_i.fifo_i.valid_q)
        iff (if_stage.prefetch_buffer_i.fifo_i.clear_i) {
      bins words[] = {[0:FifoDepth]};
    }
    cp_fifo_word_flow: coverpoint {
        if_stage.prefetch_buffer_i.fifo_i.in_valid_i,
        if_stage.prefetch_buffer_i.fifo_i.pop_fifo}
        iff (!if_stage.prefetch_buffer_i.fifo_i.clear_i) {
      bins neither = {2'b00};
      bins pop = {2'b01};
      bins arrival = {2'b10};
      bins arrival_and_pop = {2'b11};
    }
    cp_fifo_empty_bypass: coverpoint if_stage.prefetch_buffer_i.fifo_i.instr_xfr
        iff (!if_stage.prefetch_buffer_i.fifo_i.valid_q[0] &&
             if_stage.prefetch_buffer_i.fifo_i.in_valid_i &&
             !if_stage.prefetch_buffer_i.fifo_i.clear_i) {
      bins buffered = {2'b00};
      bins one_instruction = {2'b01};
      bins two_instructions = {2'b11};
    }

    // Bit 2 is instruction length; bits 1:0 are the PC's halfword offset
    // within a 64-bit word. Observe the FIFO, before predictor substitution.
    cp_fifo_instr0_alignment: coverpoint {
        if_stage.prefetch_buffer_i.fifo_i.out_is_comp[0],
        if_stage.prefetch_buffer_i.fifo_i.out_addr0[2:1]}
        iff (if_stage.prefetch_buffer_i.fifo_i.instr_xfr[0] &&
             !if_stage.prefetch_buffer_i.fifo_i.fetch_err[0] &&
             !if_stage.prefetch_buffer_i.fifo_i.clear_i) {
      bins instruction32_at_halfword[] = {[3'b000:3'b011]};
      bins instruction16_at_halfword[] = {[3'b100:3'b111]};
    }
    cp_fifo_instr1_alignment: coverpoint {
        if_stage.prefetch_buffer_i.fifo_i.out_is_comp[1],
        if_stage.prefetch_buffer_i.fifo_i.out_addr1[2:1]}
        iff (if_stage.prefetch_buffer_i.fifo_i.instr_xfr[1] &&
             !if_stage.prefetch_buffer_i.fifo_i.fetch_err[1] &&
             !if_stage.prefetch_buffer_i.fifo_i.clear_i) {
      bins instruction32_at_halfword[] = {[3'b000:3'b011]};
      bins instruction16_at_halfword[] = {[3'b100:3'b111]};
    }
    cp_fifo_aligner_offset: coverpoint if_stage.prefetch_buffer_i.fifo_i.instr_addr16
        iff (if_stage.prefetch_buffer_i.fifo_i.instr_xfr[0] &&
             !if_stage.prefetch_buffer_i.fifo_i.fetch_err[0] &&
             !if_stage.prefetch_buffer_i.fifo_i.clear_i) {
      bins halfword[] = {[0:3]};
    }
    cp_fifo_pair_lengths: coverpoint if_stage.prefetch_buffer_i.fifo_i.out_is_comp
        iff ((&if_stage.prefetch_buffer_i.fifo_i.instr_xfr) &&
             !(|if_stage.prefetch_buffer_i.fifo_i.fetch_err) &&
             !if_stage.prefetch_buffer_i.fifo_i.clear_i) {
      bins first32_second32 = {2'b00};
      bins first16_second32 = {2'b01};
      bins first32_second16 = {2'b10};
      bins first16_second16 = {2'b11};
    }
    cp_fifo_advance_pop: coverpoint {
        if_stage.prefetch_buffer_i.fifo_i.addr16_incr,
        if_stage.prefetch_buffer_i.fifo_i.pop_fifo}
        iff ((|if_stage.prefetch_buffer_i.fifo_i.instr_xfr) &&
             !if_stage.prefetch_buffer_i.fifo_i.clear_i) {
      bins bytes2_keep = {4'b0010};
      bins bytes2_pop = {4'b0011};
      bins bytes4_keep = {4'b0100};
      bins bytes4_pop = {4'b0101};
      bins bytes6_keep = {4'b0110};
      bins bytes6_pop = {4'b0111};
      bins bytes8_pop = {4'b1001};
    }
    // With only the head word present, its last halfword may need a second
    // word even for a compressed instruction when constant-fetch is enabled.
    cp_fifo_tail_ready: coverpoint if_stage.prefetch_buffer_i.fifo_i.out_valid_o[0]
        iff (if_stage.prefetch_buffer_i.fifo_i.valid_q[0] &&
             !if_stage.prefetch_buffer_i.fifo_i.valid_q[1] &&
             !if_stage.prefetch_buffer_i.fifo_i.in_valid_i &&
             if_stage.prefetch_buffer_i.fifo_i.instr_addr16 == 2'd3 &&
             !if_stage.prefetch_buffer_i.fifo_i.first_word_err &&
             !if_stage.prefetch_buffer_i.fifo_i.clear_i) {
      bins waiting_for_word = {0};
      bins instruction_ready = {1};
    }
    cp_fifo_split_second_source: coverpoint if_stage.prefetch_buffer_i.fifo_i.valid_q[1]
        iff (if_stage.prefetch_buffer_i.fifo_i.instr_xfr[0] &&
             if_stage.prefetch_buffer_i.fifo_i.instr_addr16 == 2'd3 &&
             !if_stage.prefetch_buffer_i.fifo_i.out_is_comp[0] &&
             !if_stage.prefetch_buffer_i.fifo_i.fetch_err[0] &&
             !if_stage.prefetch_buffer_i.fifo_i.clear_i) {
      bins arriving_word = {0};
      bins buffered_word = {1};
    }
    cp_fifo_word_errors: coverpoint {
        if_stage.prefetch_buffer_i.fifo_i.second_word_err,
        if_stage.prefetch_buffer_i.fifo_i.first_word_err}
        iff (if_stage.prefetch_buffer_i.fifo_i.instr_xfr[0] &&
             !if_stage.prefetch_buffer_i.fifo_i.clear_i) {
      bins neither = {2'b00};
      bins first = {2'b01};
      bins second = {2'b10};
      bins both = {2'b11};
    }
    cp_fifo_alt_restore_level: coverpoint
        $countones(if_stage.prefetch_buffer_i.fifo_i.alt_rd_valid)
        iff (if_stage.prefetch_buffer_i.fifo_i.apply_alt) {
      option.weight = AltEnable ? 1 : 0;
      bins words[] = {[0:3]};
    }
    cp_fifo_alt_save_pop: coverpoint {
        if_stage.prefetch_buffer_i.fifo_i.pop_alt,
        if_stage.prefetch_buffer_i.fifo_i.pop_fifo}
        iff (if_stage.prefetch_buffer_i.fifo_i.alloc_alt) {
      option.weight = AltEnable ? 1 : 0;
      bins keep_both = {2'b00};
      bins preserve_second_instruction = {2'b01};
      bins pop_both = {2'b11};
    }

    // ======================================================================
    // 8.2 Downstream issue of fetched instructions
    // ======================================================================
    cp_if_valid: coverpoint if_valid_o {
      bins none = {2'b00};
      bins one  = {2'b01};
      bins two  = {2'b11};
      illegal_bins slot1_only = {2'b10};
    }

    cp_ds_rdy: coverpoint ds_rdy_i {
      bins none = {2'b00};
      bins one  = {2'b01};
      bins two  = {2'b11};
      illegal_bins slot1_only = {2'b10};
    }

    // Fetch produced instructions but the IR stage could not take them.
    cp_if_stalled: coverpoint (if_valid_o[0] & ~ds_rdy_i[0]) { bins stalled = {1'b1}; }

    cp_is_comp0: coverpoint if_instr0_o.is_comp iff (if_valid_o[0]);
    cp_is_comp1: coverpoint if_instr1_o.is_comp iff (if_valid_o[1]);

    // A 32-bit instruction split across two 64-bit fetch words.  The fetch FIFO
    // has to hold the first half while the second is still in flight.
    cp_unaligned0: coverpoint (if_instr0_o.pc[2:1] == 2'b11)
                   iff (if_valid_o[0] && !if_instr0_o.is_comp) {
      bins split = {1'b1};
      bins whole = {1'b0};
    }

    cp_fetch_err0: coverpoint if_instr0_o.errs.fetch_err iff (if_valid_o[0]) {
      bins err = {1'b1};
      bins ok  = {1'b0};
    }
    cp_fetch_err1: coverpoint if_instr1_o.errs.fetch_err iff (if_valid_o[1]) {
      bins err = {1'b1};
      bins ok  = {1'b0};
    }

    x_cp_comp_align: cross cp_is_comp0, cp_is_comp1, cp_unaligned0 {
      // Split coverage only samples 32-bit slot-0 instructions.
      ignore_bins compressed_slot0 = binsof(cp_is_comp0) intersect {1'b1};
    }

    // ======================================================================
    // 8.3 Redirects and the alt (shadow-fetch) path
    // ======================================================================
    cp_ex_pc_set:  coverpoint ex_pc_set_i  { bins hit = {1'b1}; }
    cp_ex_bp_init: coverpoint ex_bp_init_i { bins hit = {1'b1}; }

    cp_redirect_align: coverpoint ex_pc_target_i[1:0] iff (ex_pc_set_i) {
      bins word = {2'b00};
      bins half = {2'b10};
      // All redirect targets are halfword aligned (AssertRedirectTargetEven,
      // AssertPcTargetEven).
      illegal_bins misaligned = {2'b01, 2'b11};
    }

    cp_alt_flush:  coverpoint ex_alt_ctrl_i.flush  { bins hit = {1'b1}; }
    cp_alt_apply:  coverpoint ex_alt_ctrl_i.apply  { bins hit = {1'b1}; }
    cp_alt_cancel: coverpoint ex_alt_ctrl_i.cancel {
      bins none = {2'b00};
      bins id0  = {2'b01};
      bins id1  = {2'b10};
      bins both = {2'b11};
    }
    cp_alt_ir_sel: coverpoint ex_alt_ctrl_i.ir_sel iff (ex_alt_ctrl_i.apply);
    cp_alt_id: coverpoint (ex_alt_ctrl_i.ir_sel ? ex_alt_ctrl_i.id1 : ex_alt_ctrl_i.id0)
        iff (ex_alt_ctrl_i.apply) {
      bins id[] = {[0:1]};
    }

    cp_alloc_alt: coverpoint alloc_alt {
      option.weight = AltEnable ? 1 : 0;
      bins hit = {1'b1};
    }
    // fetch_fifo64 has two alt entries; find_zero cannot return IDs 2 or 3.
    cp_alt_free_id: coverpoint alt_free_id iff (alloc_alt) {
      option.weight = AltEnable ? 1 : 0;
      bins id[] = {[0:1]};
    }
    // Alt allocation requested with no free slot: the predictor must fall back
    // to a plain redirect.
    cp_alt_exhausted: coverpoint (~alt_has_free) {
      option.weight = AltEnable ? 1 : 0;
      bins exhausted = {1'b1};
    }

    x_cp_alt_apply_id: cross cp_alt_apply, cp_alt_ir_sel, cp_alt_id;

    // ======================================================================
    // 8.4 Branch prediction -- predict side
    // ======================================================================
    // KUDU-011: a valid JAL fetched with the predictor disabled (CPUCTRL
    // pdt_en = 0) must still redirect from execute.
    cp_pdt_en: coverpoint pdt_en_i {
      bins off = {1'b0};
      bins on  = {1'b1};
    }
    cp_fetch_jal: coverpoint |(bp_is_jal & pdt_valid_o) {
      bins jal = {1'b1};
    }
    x_jal_pdt_off: cross cp_fetch_jal, cp_pdt_en;

    cp_ra_pdt_fresh: coverpoint ra_fresh_q iff (pdt_en_i && |pdt_jalr_go) {
      option.weight = PredictRA ? 1 : 0;
      bins before_ra_update = {1'b1};
      bins after_ra_update  = {1'b0};
    }

    cp_pdt_valid: coverpoint pdt_valid_o {
      bins none = {2'b00};
      bins one  = {2'b01};
      bins two  = {2'b11};
      illegal_bins slot1_only = {2'b10};
    }

    // Candidate classification per slot.  is_branch is qualified by ~fetch_err
    // but is_jal / is_jalr_ra are not (finding F-01), so a faulting fetch can
    // still be treated as a jump candidate.
    // The illegal values are listed explicitly rather than caught with
    // 'default': a default bin also matches X, and the decode outputs are X
    // until the first fetch returns, which would fail the run during reset.
    cp_cand0: coverpoint {bp_is_jalr_ra[0], bp_is_jal[0], bp_is_branch[0]} {
      bins none   = {3'b000};
      bins branch = {3'b001};
      bins jal    = {3'b010};
      bins jalr   = {3'b100};
      illegal_bins multiple = {3'b011, 3'b101, 3'b110, 3'b111};
    }
    cp_cand1: coverpoint {bp_is_jalr_ra[1], bp_is_jal[1], bp_is_branch[1]} {
      bins none   = {3'b000};
      bins branch = {3'b001};
      bins jal    = {3'b010};
      bins jalr   = {3'b100};
      illegal_bins multiple = {3'b011, 3'b101, 3'b110, 3'b111};
    }

    // The six-way priority chain (branch_predict.sv:305-335).  Per-slot
    // coverpoints reach 100% without ever exercising the jalr1 arm, which is
    // why the chain gets its own coverpoint.
    cp_pdt_src: coverpoint pdt_src;

    cp_pdt_cand0: coverpoint pdt_cand0 iff (pdt_en_i && pdt_pc_set[0]) {
      bins branch = {PDT_CAND_BRANCH};
      bins jal = {PDT_CAND_JAL};
      bins jalr = {PDT_CAND_JALR};
    }
    cp_pdt_cand1: coverpoint pdt_cand1 iff (pdt_en_i && pdt_pc_set[1]) {
      bins branch = {PDT_CAND_BRANCH};
      bins jal = {PDT_CAND_JAL};
      bins jalr = {PDT_CAND_JALR};
    }

    // pdt_pc_set is a raw per-slot decode, not an arbitrated output
    // (branch_predict.sv:266-267), so both bits can set in the same cycle when
    // both fetch slots hold a redirect candidate.  Slot 0 wins everywhere that
    // matters: predict_target is a strict slot-0-first priority mux (:305-316),
    // slot 1's alt allocation is gated on ~pdt_pc_set[0] (:283) and slot 1 is
    // dropped from the bundle (:272).  2'b11 is therefore the dual-candidate
    // case, and a useful one -- it is the only way the slot-1 arms of the
    // priority chain are known to be losing to slot 0 rather than never
    // offered.  The arbitration guarantee is asserted below.
    cp_pdt_pc_set: coverpoint pdt_pc_set iff (pdt_en_i) {
      bins none  = {2'b00};
      bins slot0 = {2'b01};
      bins slot1 = {2'b10};
      bins both  = {2'b11};
    }

    x_cp_pdt_priority_contention: cross cp_pdt_cand0, cp_pdt_cand1, cp_pdt_src
        iff (pdt_en_i && (pdt_pc_set == 2'b11)) {
      ignore_bins non_slot0_winner = binsof(cp_pdt_src) intersect
          {PDT_BR1, PDT_JAL1, PDT_JALR1, PDT_NONE};
      // pdt_src and pdt_cand0 are both derived from the slot-0 go bits with
      // the same br > jal > jalr priority, so the slot-0 winner always
      // matches cand0 (AssertPdtSrcMatchesCand0).
      illegal_bins src_ne_cand0 =
          (binsof(cp_pdt_cand0.branch) && binsof(cp_pdt_src) intersect {PDT_JAL0, PDT_JALR0}) ||
          (binsof(cp_pdt_cand0.jal)    && binsof(cp_pdt_src) intersect {PDT_BR0,  PDT_JALR0}) ||
          (binsof(cp_pdt_cand0.jalr)   && binsof(cp_pdt_src) intersect {PDT_BR0,  PDT_JAL0});
    }

    // The predictor reads only bit 1 of the counter (T/NT); bit 0 (strength) is
    // update-only.  Both bits are covered so that the two "weak" states are
    // known to have been visited on the predict path, not just the update path.
    cp_bht_rdata0: coverpoint bht_rdata0 {
      bins strong_t = {2'b00};
      bins weak_t   = {2'b01};
      bins strong_n = {2'b10};
      bins weak_n   = {2'b11};
    }
    cp_bht_rdata1: coverpoint bht_rdata1 {
      bins strong_t = {2'b00};
      bins weak_t   = {2'b01};
      bins strong_n = {2'b10};
      bins weak_n   = {2'b11};
    }

    // Slot 1's BHT/JTB index is chosen by whether slot 0 is compressed
    // (branch_predict.sv:238, :241, :252) -- a speculative index select that
    // must be exercised both ways or half the slot-1 prediction path is dead.
    cp_slot1_index_sel: coverpoint fetch_instr0_is_comp iff (|pdt_valid_o) {
      bins spec0_comp   = {1'b1};
      bins spec1_uncomp = {1'b0};
    }

    cp_ptaken0: coverpoint pdt_instr0.ptaken iff (pdt_valid_o[0]);
    cp_ptaken1: coverpoint pdt_instr1.ptaken iff (pdt_valid_o[1]);

    // ======================================================================
    // 8.5 Branch prediction -- update side
    //
    // Kept separate from the predict side on purpose: the two live in different
    // time domains (a fetch-cycle lookup versus an EX-cycle train) and mixing
    // them in one covergroup produces cells that no single cycle can fill.
    // ======================================================================
    cp_update_slots: coverpoint ex_bp_info_i.is_branch {
      bins none  = {2'b00};
      bins slot0 = {2'b01};
      bins slot1 = {2'b10};
      bins both  = {2'b11};
    }

    cp_outcome0: coverpoint ex_bp_info_i.taken[0] iff (ex_bp_info_i.is_branch[0]);
    cp_outcome1: coverpoint ex_bp_info_i.taken[1] iff (ex_bp_info_i.is_branch[1]);

    // See F-19.  Two branches resolving in the same cycle into the same BHT
    // entry: slot 1's outcome is dropped.
    cp_bht_slot1_dropped: coverpoint bht_slot1_dropped iff (bht_dual_update) {
      bins distinct_entries = {1'b0};
      bins same_entry       = {1'b1};
    }

    cp_jal_update: coverpoint ex_bp_info_i.is_jal {
      bins none  = {2'b00};
      bins slot0 = {2'b01};
      bins slot1 = {2'b10};
      bins both  = {2'b11};
    }

  endgroup

  cg_ma_if u_cg_ma_if = new();

  // ==========================================================================
  // Structural assertions backing the illegal_bins above.
  // ==========================================================================
  AssertDiscardPrefix: assert property (
    @(posedge clk_i) disable iff (!rst_ni) is_discard_prefix(branch_discard_q))
    else $error("FCOV: pending branch-discard bitmap is not an oldest-first prefix");

  AssertIfValidLegal: assert property (
    @(posedge clk_i) disable iff (!rst_ni) if_valid_o[1] |-> if_valid_o[0])
    else $error("FCOV: if_valid_o == 2'b10");

  AssertIfBusyEqPrefetchBusy: assert property (
    @(posedge clk_i) disable iff (!rst_ni) if_busy_o == prefetch_busy)
    else $error("FCOV: if_busy_o != prefetch_busy");

  AssertRedirectTargetEven: assert property (
    @(posedge clk_i) disable iff (!rst_ni) ex_pc_set_i |-> !ex_pc_target_i[0])
    else $error("FCOV: odd redirect target 0x%08x", ex_pc_target_i);

  AssertPdtSrcMatchesCand0: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (pdt_en_i && pdt_pc_set[0]) |->
      ((pdt_cand0 == PDT_CAND_BRANCH && pdt_src == PDT_BR0) ||
       (pdt_cand0 == PDT_CAND_JAL    && pdt_src == PDT_JAL0) ||
       (pdt_cand0 == PDT_CAND_JALR   && pdt_src == PDT_JALR0)))
    else $error("FCOV: slot-0 PDT winner %s does not match candidate %s",
                pdt_src.name(), pdt_cand0.name());

`endif  // KUDU_FCOV_OFF

endmodule

// ============================================================================
// kudu_sva_if -- SVA properties for the instruction fetch path (if_stage,
// prefetch_buffer64, fetch_fifo64, branch_predict).  Bound to rtl/if_stage.sv
// as u_fcov_sva_if; reaches into prefetch_buffer_i, prefetch_buffer_i.fifo_i
// and branch_predict_i (module-scope signals only).
//
// The checker keeps three reference models that are independent of the DUT
// bookkeeping:
//  * sq_*  : one entry per granted bus request {word address, stale}.  An
//            entry turns stale on any redirect (branch_req) after the request
//            was first presented; it pops on each response.
//  * exp_* : the next word address to be pushed into the fetch FIFO and the
//            architectural pc of the next instruction (advanced by the length
//            of every instruction handed to IR).
//  * sd_*  : a copy of every response word accepted by the FIFO, popped when
//            exp_pc leaves the word.  Gives the expected 128-bit window, so the
//            delivered instruction bits, valids and fetch errors are checked
//            end to end.  Invalid after an ALT restore (the restored words were
//            buffered before the predicted-taken branch) until the next
//            non-ALT redirect.
// ============================================================================
module kudu_sva_if
  import super_pkg::*;
#(
  parameter int unsigned PrefetchDepth  = 3,
  parameter bit          AltEnable      = 1'b0,
  parameter bit          PredictRA      = 1'b0,
  parameter bit          UnalignedFetch = 1'b0,
  parameter bit          PredictUseBtb  = 1'b1,
  // fetch_fifo64 DEPTH (rtl/fetch_fifo64.sv localparam DEPTH)
  parameter int unsigned FDepth         = AltEnable ? PrefetchDepth + 4 : PrefetchDepth + 1
) (
  input logic                     clk_i,
  input logic                     rst_ni,
  input logic                     req_i,
  input cpu_ctrl_t                cpu_ctrl_i,

  // --- instruction bus -------------------------------------------------------
  input logic                     instr_req_o,
  input logic [31:0]              instr_addr_o,
  input logic                     instr_gnt_i,

  // --- IR handshake / redirect -----------------------------------------------
  input logic [1:0]               ds_rdy_i,
  input logic [1:0]               if_valid_o,
  input logic                     ex_pc_set_i,
  input ex_alt_ctrl_t             ex_alt_ctrl_i,
  input logic [31:0]              cur_ra32_i,
  input logic                     branch_req,
  input logic [31:0]              fetch_addr_n,
  input logic                     predict_pc_set,
  input logic [31:0]              predict_pc_target,

  // --- prefetch buffer output / branch predictor output ----------------------
  input logic [1:0]               fetch_valid,
  input ir_reg_t                  fetch_instr0,
  input ir_reg_t                  fetch_instr1,
  input logic [31:0]              instr1_pc_spec0,
  input logic [31:0]              instr1_pc_spec1,
  input ir_reg_t                  pdt_instr0,
  input ir_reg_t                  pdt_instr1,

  // --- prefetch_buffer_i internals --------------------------------------------
  input logic [PrefetchDepth-1:0] pb_outstanding_q,
  input logic [PrefetchDepth-1:0] pb_discard_q,
  input logic                     pb_rvalid_in,
  input logic [63:0]              pb_rdata_in,
  input logic                     pb_err_in,
  input logic                     pb_fifo_valid,
  input logic [31:0]              pb_alt_nxt_addr,

  // --- prefetch_buffer_i.fifo_i internals --------------------------------------
  input logic [FDepth-1:0]        ff_valid_q,
  input logic                     ff_apply_alt,
  input logic                     ff_alloc_alt,
  input logic [1:0]               ff_alt_status,
  input logic [1:0]               ff_alt_free_id,
  input logic                     ff_alt_err_event,

  // --- branch_predict_i internals ---------------------------------------------
  input logic signed [31:0]       bp_bht_rdata0,
  input logic signed [31:0]       bp_bht_rdata1
);

`ifndef KUDU_FCOV_OFF

  localparam int unsigned SqDepth = PrefetchDepth + 1;
  localparam int unsigned SqCntW  = $clog2(SqDepth + 1);
  localparam int unsigned SdDepth = FDepth + 1;
  localparam int unsigned SdCntW  = $clog2(SdDepth + 1);

  // ---------------------------------------------------------------------------
  // Reference decode (RISC-V spec), independent of the DUT pre-decode.
  // ---------------------------------------------------------------------------
  function automatic logic [2:0] ilen(logic [1:0] lo);
    return (lo == 2'b11) ? 3'd4 : 3'd2;
  endfunction

  function automatic logic ref_is_branch(logic [31:0] i);
    return ((i[1:0] == 2'b01) && (i[15:14] == 2'b11)) ||          // c.beqz/c.bnez
           ((i[1:0] == 2'b11) && (i[6:0] == OPCODE_BRANCH));
  endfunction

  function automatic logic ref_is_jal(logic [31:0] i);
    return ((i[1:0] == 2'b01) && (i[14:13] == 2'b01)) ||          // c.jal/c.j
           ((i[1:0] == 2'b11) && (i[6:0] == OPCODE_JAL));
  endfunction

  // Jump through ra with offset 0: c.jr ra, c.jalr ra, jalr rd, 0(ra).
  function automatic logic ref_is_ret(logic [31:0] i);
    return ((i[1:0] == 2'b10) && (i[15:13] == 3'b100) && (i[11:7] == 5'd1) &&
            (i[6:2] == 5'd0)) ||
           ((i[6:0] == OPCODE_JALR) && (i[14:12] == 3'b000) && (i[19:15] == 5'd1) &&
            (i[31:20] == 12'd0));
  endfunction

  function automatic logic [31:0] ref_br_off(logic [31:0] i);
    if (i[1:0] != 2'b11)   // CB format: offset[8|4:3] = c[12|11:10], [7:6|2:1|5] = c[6:5|4:3|2]
      return {{24{i[12]}}, i[6:5], i[2], i[11:10], i[4:3], 1'b0};
    else
      return {{20{i[31]}}, i[7], i[30:25], i[11:8], 1'b0};
  endfunction

  function automatic logic [31:0] ref_j_off(logic [31:0] i);
    if (i[1:0] != 2'b11)   // CJ format: offset[11|4|9:8|10|6|7|3:1|5] = c[12:2]
      return {{21{i[12]}}, i[8], i[10:9], i[6], i[7], i[2], i[11], i[5:3], 1'b0};
    else
      return {{12{i[31]}}, i[19:12], i[20], i[30:21], 1'b0};
  endfunction

  // ---------------------------------------------------------------------------
  // Model 1: granted requests in flight.
  // ---------------------------------------------------------------------------
  typedef struct packed {
    logic [31:3] addr;
    logic        stale;
  } sq_ent_t;

  sq_ent_t [SqDepth-1:0] sq_q, sq_d;
  logic [SqCntW-1:0]     sq_cnt_q, sq_cnt_d;
  logic                  req_pend_q, pend_stale_q;
  logic                  sq_push, sq_pop, gnt_stale;
  logic [SqDepth-1:0]    sq_mask, sq_stale_vec;

  assign sq_push   = instr_req_o & instr_gnt_i;
  assign sq_pop    = pb_rvalid_in & (sq_cnt_q != '0);
  // A request is fetched from the redirect target in its first cycle
  // (prefetch_buffer64.sv instr_addr mux); a redirect in any later cycle before
  // its grant makes the response stale.
  assign gnt_stale = req_pend_q & (pend_stale_q | branch_req);

  always_comb begin
    sq_d     = sq_q;
    sq_cnt_d = sq_cnt_q;
    for (int unsigned i = 0; i < SqDepth; i++) sq_d[i].stale = sq_q[i].stale | branch_req;
    if (sq_pop) begin
      for (int unsigned i = 0; i < SqDepth - 1; i++) sq_d[i] = sq_d[i+1];
      sq_d[SqDepth-1] = '0;
      sq_cnt_d        = sq_cnt_q - 1'b1;
    end
    if (sq_push && (sq_cnt_d < SqCntW'(SqDepth))) begin
      sq_d[sq_cnt_d] = '{addr: instr_addr_o[31:3], stale: gnt_stale};
      sq_cnt_d       = sq_cnt_d + 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sq_q         <= '0;
      sq_cnt_q     <= '0;
      req_pend_q   <= 1'b0;
      pend_stale_q <= 1'b0;
    end else begin
      sq_q         <= sq_d;
      sq_cnt_q     <= sq_cnt_d;
      req_pend_q   <= instr_req_o & ~instr_gnt_i;
      pend_stale_q <= instr_req_o & ~instr_gnt_i & gnt_stale;
    end
  end

  always_comb begin
    for (int unsigned i = 0; i < SqDepth; i++) begin
      sq_mask[i]      = (i < sq_cnt_q);
      sq_stale_vec[i] = sq_q[i].stale & sq_mask[i];
    end
  end

  // ---------------------------------------------------------------------------
  // Model 2: next word to be pushed, and architectural fetch pc.
  // ---------------------------------------------------------------------------
  logic [31:3] exp_pw_q;
  logic [31:0] exp_pc_q, exp_pc_nxt;
  logic [1:0]  xfr;
  logic [2:0]  len0, len1;
  logic [3:0]  adv;

  assign xfr  = fetch_valid & ds_rdy_i;
  assign len0 = ilen(fetch_instr0.insn[1:0]);
  assign len1 = ilen(fetch_instr1.insn[1:0]);
  assign adv  = xfr[0] ? ({1'b0, len0} + (xfr[1] ? {1'b0, len1} : 4'd0)) : 4'd0;
  assign exp_pc_nxt = exp_pc_q + {28'd0, adv};

  // Reset values match the DUT (fetch_addr_q and instr_addr_q reset to 0).
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      exp_pw_q <= '0;
      exp_pc_q <= '0;
    end else if (branch_req) begin
      exp_pw_q <= ff_apply_alt ? pb_alt_nxt_addr[31:3] : fetch_addr_n[31:3];
      exp_pc_q <= {fetch_addr_n[31:1], 1'b0};
    end else begin
      if (pb_fifo_valid) exp_pw_q <= exp_pw_q + 1'b1;
      exp_pc_q <= exp_pc_nxt;
    end
  end

  // instr_addrp2_q/p4_q reset to 0 rather than pc+2/pc+4; they become consistent
  // with instr_addr_q at the first redirect (no instruction is valid before it).
  logic redir_seen_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)         redir_seen_q <= 1'b0;
    else if (branch_req) redir_seen_q <= 1'b1;
  end

  // ---------------------------------------------------------------------------
  // Model 3: shadow of the FIFO data, giving the expected fetch window.
  // ---------------------------------------------------------------------------
  typedef struct packed {
    logic        err;
    logic [63:0] data;
  } sd_ent_t;

  sd_ent_t [SdDepth-1:0] sd_q, sd_d;
  logic [SdCntW-1:0]     sd_cnt_q, sd_cnt_d;
  logic                  sd_ok_q, sd_push, sd_pop;
  sd_ent_t               sd_in, w0, w1;
  logic                  av0, av1;
  logic [127:0]          win;
  logic [1:0]            h;
  logic [2:0]            p1, end1;
  logic [15:0]           hw0, hw1;
  logic [2:0]            l0, l1;
  logic                  straddle0, fits1_w0;
  logic                  exp_v0, exp_v1, exp_err0, exp_err1, exp_f2w0, exp_f2w1;

  assign sd_in   = '{err: pb_err_in, data: pb_rdata_in};
  assign sd_push = pb_fifo_valid & ~branch_req;
  assign sd_pop  = ~branch_req & (exp_pc_nxt[31:3] != exp_pc_q[31:3]);

  always_comb begin
    sd_d     = sd_q;
    sd_cnt_d = sd_cnt_q;
    if (sd_push && (sd_cnt_q < SdCntW'(SdDepth))) begin
      sd_d[sd_cnt_q] = sd_in;
      sd_cnt_d       = sd_cnt_q + 1'b1;
    end
    if (sd_pop && (sd_cnt_d != '0)) begin
      for (int unsigned i = 0; i < SdDepth - 1; i++) sd_d[i] = sd_d[i+1];
      sd_d[SdDepth-1] = '0;
      sd_cnt_d        = sd_cnt_d - 1'b1;
    end
    if (branch_req) sd_cnt_d = '0;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sd_q     <= '0;
      sd_cnt_q <= '0;
      sd_ok_q  <= 1'b1;
    end else begin
      sd_q     <= sd_d;
      sd_cnt_q <= sd_cnt_d;
      if (branch_req) sd_ok_q <= ~ff_apply_alt;
    end
  end

  // Words visible to the output stage: buffered words first, then the
  // response arriving this cycle (fetch_fifo64.sv rdata128 bypass).
  assign av0 = (sd_cnt_q != '0) | pb_fifo_valid;
  assign av1 = (sd_cnt_q > 1'b1) | ((sd_cnt_q == 1'b1) & pb_fifo_valid);
  assign w0  = (sd_cnt_q != '0)        ? sd_q[0] : sd_in;
  assign w1  = (sd_cnt_q > 1'b1) ? sd_q[1] : sd_in;
  assign win = {w1.data, w0.data};

  assign h         = exp_pc_q[2:1];
  assign hw0       = win[{2'b0, h, 4'd0} +: 16];
  assign l0        = ilen(hw0[1:0]);
  assign straddle0 = (h == 2'd3) && (l0 == 3'd4);
  assign p1        = {1'b0, h} + {1'b0, l0[2:1]};
  assign hw1       = win[{1'b0, p1, 4'd0} +: 16];
  assign l1        = ilen(hw1[1:0]);
  assign end1      = p1 + {1'b0, l1[2:1]};
  assign fits1_w0  = (end1 <= 3'd4);

  // An instruction is offered once all its halfwords are present; a fetch
  // error in the first word is offered alone (KUDU-013 fix); const_fetch
  // holds back a compressed instruction in the last halfword of a lone word.
  assign exp_v0   = av0 & (av1 | w0.err |
                           (~straddle0 & ~(cpu_ctrl_i.const_fetch & (h == 2'd3))));
  assign exp_v1   = av0 & (av1 | (~w0.err & fits1_w0));
  assign exp_err0 = w0.err | (av1 & straddle0 & w1.err);
  assign exp_f2w0 = ~w0.err & av1 & straddle0 & w1.err;
  assign exp_err1 = w0.err | (av1 & (end1 > 3'd4) & w1.err);
  assign exp_f2w1 = ~w0.err & av1 & (p1 < 3'd4) & (end1 > 3'd4) & w1.err;

  // ---------------------------------------------------------------------------
  // Reference prediction (decoded targets).
  // ---------------------------------------------------------------------------
  logic [1:0]  ref_br, ref_jal, ref_ret;
  logic [31:0] ref_tgt0, ref_tgt1;

  assign ref_br[0]  = ref_is_branch(pdt_instr0.insn) & ~pdt_instr0.errs.fetch_err;
  assign ref_br[1]  = ref_is_branch(pdt_instr1.insn) & ~pdt_instr1.errs.fetch_err;
  assign ref_jal[0] = ref_is_jal(pdt_instr0.insn);
  assign ref_jal[1] = ref_is_jal(pdt_instr1.insn);
  assign ref_ret[0] = PredictRA & cpu_ctrl_i.ra_pdt_en & ref_is_ret(pdt_instr0.insn);
  assign ref_ret[1] = PredictRA & cpu_ctrl_i.ra_pdt_en & ref_is_ret(pdt_instr1.insn);

  assign ref_tgt0 = ref_br[0]  ? pdt_instr0.pc + ref_br_off(pdt_instr0.insn) :
                    ref_jal[0] ? pdt_instr0.pc + ref_j_off(pdt_instr0.insn)  :
                                 {cur_ra32_i[31:1], 1'b0};
  assign ref_tgt1 = ref_br[1]  ? pdt_instr1.pc + ref_br_off(pdt_instr1.insn) :
                    ref_jal[1] ? pdt_instr1.pc + ref_j_off(pdt_instr1.insn)  :
                                 {cur_ra32_i[31:1], 1'b0};

  logic [1:0] pt, acc_pt;
  assign pt     = {pdt_instr1.ptaken, pdt_instr0.ptaken};
  assign acc_pt = if_valid_o & ds_rdy_i & pt;

  // ===========================================================================
  // Assertions
  // ===========================================================================

  // --- Instruction bus protocol (prefetch_buffer64.sv valid_req_d / stored_addr_q)
  // rtl/prefetch_buffer64.sv:184-187,327: a request is held until granted
  AssertReqHeldUntilGnt: assert property (@(posedge clk_i) disable iff (!rst_ni)
    instr_req_o && !instr_gnt_i |=> instr_req_o)
    else $error("SVA_IF: instr_req_o dropped before instr_gnt_i");

  // rtl/prefetch_buffer64.sv:216-223,328: the address is held until granted
  AssertAddrStableUntilGnt: assert property (@(posedge clk_i) disable iff (!rst_ni)
    instr_req_o && !instr_gnt_i |=> $stable(instr_addr_o))
    else $error("SVA_IF: instr_addr_o changed while waiting for instr_gnt_i");

  // rtl/prefetch_buffer64.sv:181: a new (not held-over) request needs req_i
  AssertNewReqNeedsReqI: assert property (@(posedge clk_i) disable iff (!rst_ni)
    instr_req_o && !req_pend_q |-> req_i)
    else $error("SVA_IF: new instruction request without req_i");

  // rtl/prefetch_buffer64.sv:328: bus address is 64-bit aligned (32-bit with UnalignedFetch)
  AssertAddrAligned: assert property (@(posedge clk_i) disable iff (!rst_ni)
    instr_req_o |-> (instr_addr_o[2:0] == 3'b000) || (UnalignedFetch && instr_addr_o[1:0] == 2'b00))
    else $error("SVA_IF: misaligned instruction bus address");

  // --- Outstanding-request accounting (rdata_outstanding_q / branch_discard_q)
  // rtl/prefetch_buffer64.sv:272-289: never more than PrefetchDepth requests in flight
  AssertOutstandingBound: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sq_cnt_q <= SqCntW'(PrefetchDepth))
    else $error("SVA_IF: more than PrefetchDepth instruction requests outstanding");

  // rtl/prefetch_buffer64.sv:272-319: rdata_outstanding_q equals granted minus returned requests
  AssertOutstandingTrack: assert property (@(posedge clk_i) disable iff (!rst_ni)
    {1'b0, pb_outstanding_q} == sq_mask)
    else $error("SVA_IF: rdata_outstanding_q does not match granted-minus-returned requests");

  // rtl/prefetch_buffer64.sv:99,297: no response without an outstanding request
  AssertRvalidHasOutstanding: assert property (@(posedge clk_i) disable iff (!rst_ni)
    pb_rvalid_in |-> sq_cnt_q != '0)
    else $error("SVA_IF: instruction response with no request outstanding");

  // rtl/prefetch_buffer64.sv:190,276-297: branch_discard_q marks exactly the requests made stale by a redirect
  AssertDiscardTrack: assert property (@(posedge clk_i) disable iff (!rst_ni)
    {1'b0, pb_discard_q} == sq_stale_vec)
    else $error("SVA_IF: branch_discard_q does not match the requests made stale by a redirect");

  // rtl/prefetch_buffer64.sv:301: stale responses are dropped, fresh ones always reach the FIFO
  AssertDiscardExact: assert property (@(posedge clk_i) disable iff (!rst_ni)
    pb_rvalid_in |-> pb_fifo_valid == !sq_q[0].stale)
    else $error("SVA_IF: stale response pushed into the fetch FIFO, or fresh response dropped");

  // --- Fetch FIFO occupancy (fetch_fifo64.sv valid_d / lowest_free_entry)
  // rtl/fetch_fifo64.sv:402-446: a response is never pushed into a full FIFO
  AssertFifoNoOverflow: assert property (@(posedge clk_i) disable iff (!rst_ni)
    pb_fifo_valid && !branch_req |-> !ff_valid_q[FDepth-1])
    else $error("SVA_IF: response pushed into a full fetch FIFO");

  // rtl/fetch_fifo64.sv:402-445: valid_q is a thermometer code (no holes)
  AssertFifoValidContig: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (ff_valid_q & (ff_valid_q + 1'b1)) == '0)
    else $error("SVA_IF: fetch FIFO valid vector has a hole");

  // rtl/fetch_fifo64.sv:222-279, rtl/if_stage.sv:115: slot 1 is never valid or transferred without slot 0
  AssertFetchValidLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
    fetch_valid != 2'b10 && xfr != 2'b10)
    else $error("SVA_IF: slot 1 fetched/transferred without slot 0");

  if (!UnalignedFetch) begin : gen_aligned_addr
    // rtl/prefetch_buffer64.sv:301, rtl/fetch_fifo64.sv:541: FIFO words arrive in order from the redirect/ALT resume word
    AssertRespAddrSeq: assert property (@(posedge clk_i) disable iff (!rst_ni)
      pb_fifo_valid && !branch_req |-> sq_q[0].addr == exp_pw_q)
      else $error("SVA_IF: fetch FIFO received a word from an unexpected address");

    // rtl/fetch_fifo64.sv:200-201,343-357: FIFO holds the words from the pc word up to the next word to fetch
    AssertFifoAddrCoherent: assert property (@(posedge clk_i) disable iff (!rst_ni)
      fetch_instr0.pc[31:3] + 29'(unsigned'($countones(ff_valid_q))) == exp_pw_q)
      else $error("SVA_IF: fetch FIFO contents not contiguous with the fetch pc");
  end

  // --- PC sequencing (fetch_fifo64.sv instr_addr_q / addr16_incr)
  // rtl/fetch_fifo64.sv:343-358: fetch pc = last redirect target + lengths of the instructions accepted by IR
  AssertPc0Track: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_fcov_pkg::sva_xok(fetch_instr0.pc == exp_pc_q))
    else $error("SVA_IF: fetch pc is not the redirect target plus the delivered lengths");

  // rtl/prefetch_buffer64.sv:181, rtl/fetch_fifo64.sv:222-279: nothing is delivered before the first pc_set
  AssertNoValidBeforeRedirect: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !redir_seen_q |-> fetch_valid == 2'b00)
    else $error("SVA_IF: instruction delivered before the first pc_set");

  // rtl/fetch_fifo64.sv:376: slot 1 pc = slot 0 pc + slot 0 length
  AssertPc1Seq: assert property (@(posedge clk_i) disable iff (!rst_ni)
    fetch_valid[1] |-> kudu_fcov_pkg::sva_xok(fetch_instr1.pc == fetch_instr0.pc + {29'd0, len0}))
    else $error("SVA_IF: slot 1 pc is not slot 0 pc plus slot 0 length");

  // rtl/fetch_fifo64.sv:361-379: speculative slot 1 pcs (BHT index) are slot 0 pc + 2 / + 4
  AssertPcSpecConsistent: assert property (@(posedge clk_i) disable iff (!rst_ni)
    redir_seen_q |->
    instr1_pc_spec0 == fetch_instr0.pc + 32'd2 && instr1_pc_spec1 == fetch_instr0.pc + 32'd4)
    else $error("SVA_IF: instr1_pc_spec0/1 inconsistent with slot 0 pc");

  // --- Pre-decode (fetch_fifo64.sv comp_flag / dec_branch / dec_jal)
  // rtl/fetch_fifo64.sv:189,284-306: slot 0 is_comp/is_branch/is_jal agree with the instruction bits
  AssertPredecodeSlot0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    fetch_valid[0] |->
      kudu_fcov_pkg::sva_xok(fetch_instr0.is_comp   == (fetch_instr0.insn[1:0] != 2'b11) &&
      fetch_instr0.is_branch == ref_is_branch(fetch_instr0.insn) &&
      fetch_instr0.is_jal    == ref_is_jal(fetch_instr0.insn)))
    else $error("SVA_IF: slot 0 pre-decode disagrees with instruction bits");

  // rtl/fetch_fifo64.sv:189,284-306: slot 1 is_comp/is_branch/is_jal agree with the instruction bits
  AssertPredecodeSlot1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    fetch_valid[1] |->
      kudu_fcov_pkg::sva_xok(fetch_instr1.is_comp   == (fetch_instr1.insn[1:0] != 2'b11) &&
      fetch_instr1.is_branch == ref_is_branch(fetch_instr1.insn) &&
      fetch_instr1.is_jal    == ref_is_jal(fetch_instr1.insn)))
    else $error("SVA_IF: slot 1 pre-decode disagrees with instruction bits");

  // --- End-to-end fetch data (fetch_fifo64.sv out_valid_o / fetch_err / out_rdata)
  // rtl/fetch_fifo64.sv:222-279: slot 0 is valid exactly when the buffered bytes hold a whole instruction (or an error)
  AssertFetchValid0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sd_ok_q && !$isunknown({hw0[1:0], hw1[1:0]}) |->
      kudu_fcov_pkg::sva_xok(fetch_valid[0] == exp_v0))
    else $error("SVA_IF: slot 0 valid disagrees with buffered data");

  // rtl/fetch_fifo64.sv:222-279: slot 1 is valid exactly when the buffered bytes hold a second whole instruction
  AssertFetchValid1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sd_ok_q && !$isunknown({hw0[1:0], hw1[1:0]}) |->
      kudu_fcov_pkg::sva_xok(fetch_valid[1] == exp_v1))
    else $error("SVA_IF: slot 1 valid disagrees with buffered data");

  // rtl/fetch_fifo64.sv:243-279,162: slot 0 fetch_err/ferr2w match the bus errors of the words it spans
  // The model is X for a cycle after a speculative fetch returns X data (uninitialised memory); skip those cycles.
  AssertFetchErr0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sd_ok_q && fetch_valid[0] && !$isunknown({exp_err0, exp_f2w0}) |->
      fetch_instr0.errs.fetch_err == exp_err0 && fetch_instr0.ferr2w == exp_f2w0)
    else $error("SVA_IF: slot 0 fetch_err/ferr2w disagrees with response errors");

  // rtl/fetch_fifo64.sv:243-279,175: slot 1 fetch_err/ferr2w match the bus errors of the words it spans
  AssertFetchErr1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sd_ok_q && fetch_valid[1] && !$isunknown({exp_err1, exp_f2w1}) |->
      fetch_instr1.errs.fetch_err == exp_err1 && fetch_instr1.ferr2w == exp_f2w1)
    else $error("SVA_IF: slot 1 fetch_err/ferr2w disagrees with response errors");

  // rtl/fetch_fifo64.sv:200-201,284-306: slot 0 bits are the memory words fetched at pc
  AssertFetchData0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sd_ok_q && fetch_valid[0] |->
      kudu_fcov_pkg::sva_xok(fetch_instr0.insn[15:0] == hw0 &&
      (l0 == 3'd2 || (straddle0 && !av1) || fetch_instr0.insn[31:16] == win[{2'b0, h, 4'd0} + 8'd16 +: 16])))
    else $error("SVA_IF: slot 0 instruction bits are not the fetched memory at pc");

  // rtl/fetch_fifo64.sv:200-201,284-306: slot 1 bits are the memory words fetched at pc1
  AssertFetchData1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sd_ok_q && fetch_valid[1] |->
      kudu_fcov_pkg::sva_xok(fetch_instr1.insn[15:0] == hw1 &&
      (l1 == 3'd2 || fetch_instr1.insn[31:16] == win[{1'b0, p1, 4'd0} + 8'd16 +: 16])))
    else $error("SVA_IF: slot 1 instruction bits are not the fetched memory at pc");

  // rtl/if_stage.sv:115, rtl/branch_predict.sv:304-305: FIFO pops only what IR accepted, except on a redirect
  AssertFifoConsumesIrAccepted: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !branch_req |-> (if_valid_o & ds_rdy_i) == xfr)
    else $error("SVA_IF: fetch FIFO consumed an instruction IR did not accept");

  // --- Branch prediction (branch_predict.sv)
  // rtl/branch_predict.sv:188-197,285-302: slot 0 predicted only for a branch/jal/ret with prediction enabled
  AssertPredictOnlyCtrl0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    if_valid_o[0] && pdt_instr0.ptaken |->
      cpu_ctrl_i.pdt_en && (ref_br[0] || ref_jal[0] || ref_ret[0]))
    else $error("SVA_IF: slot 0 predicted taken but not a predictable control transfer");

  // rtl/branch_predict.sv:188-197,285-302: slot 1 predicted only for a branch/jal/ret with prediction enabled
  AssertPredictOnlyCtrl1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    if_valid_o[1] && pdt_instr1.ptaken |->
      cpu_ctrl_i.pdt_en && (ref_br[1] || ref_jal[1] || ref_ret[1]))
    else $error("SVA_IF: slot 1 predicted taken but not a predictable control transfer");

  // rtl/branch_predict.sv:336-350: predicted targets are halfword aligned
  AssertPtargetEven: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (if_valid_o[0] && pdt_instr0.ptaken |-> !pdt_instr0.ptarget[0]) and
    (if_valid_o[1] && pdt_instr1.ptaken |-> !pdt_instr1.ptarget[0]))
    else $error("SVA_IF: odd predicted target");

  if (!PredictUseBtb) begin : gen_dec_target
    // rtl/branch_predict.sv:85-110,336-350: slot 0 target = pc + B/J immediate, or ra for a return
    AssertPtargetRef0: assert property (@(posedge clk_i) disable iff (!rst_ni)
      if_valid_o[0] && pdt_instr0.ptaken |-> pdt_instr0.ptarget == ref_tgt0)
      else $error("SVA_IF: slot 0 predicted target is not the decoded target");

    // rtl/branch_predict.sv:85-110,336-350: slot 1 target = pc + B/J immediate, or ra for a return
    AssertPtargetRef1: assert property (@(posedge clk_i) disable iff (!rst_ni)
      if_valid_o[1] && pdt_instr1.ptaken |-> pdt_instr1.ptarget == ref_tgt1)
      else $error("SVA_IF: slot 1 predicted target is not the decoded target");
  end

  // rtl/branch_predict.sv:305: no slot 1 behind a predicted-taken slot 0
  AssertNoValidAfterPtaken: assert property (@(posedge clk_i) disable iff (!rst_ni)
    if_valid_o[0] && pdt_instr0.ptaken |-> !if_valid_o[1])
    else $error("SVA_IF: slot 1 delivered behind a predicted-taken slot 0");

  // rtl/branch_predict.sv:299-302: a predicted redirect happens iff IR accepts a ptaken instruction
  AssertPredictPcSetConsistent: assert property (@(posedge clk_i) disable iff (!rst_ni)
    predict_pc_set == |acc_pt)
    else $error("SVA_IF: predict_pc_set disagrees with the accepted ptaken flags");

  // rtl/branch_predict.sv:308,336-350: the redirect target is the accepted instruction's ptarget
  AssertPredictTargetConsistent: assert property (@(posedge clk_i) disable iff (!rst_ni)
    predict_pc_set |->
      predict_pc_target == (acc_pt[0] ? pdt_instr0.ptarget : pdt_instr1.ptarget))
    else $error("SVA_IF: redirect target differs from the accepted instruction's ptarget");

  // rtl/branch_predict.sv:188-195: prediction on a fetch-error word is a don't care
  // (the fetch-error trap flushes it), so it is deliberately not asserted.

  // rtl/branch_predict.sv:71,277-278: BHT counters are legal 2-bit states
  AssertBhtReadLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_fcov_pkg::sva_xok(bp_bht_rdata0 inside {[0:3]} && bp_bht_rdata1 inside {[0:3]}))
    else $error("SVA_IF: BHT counter out of range");

  // --- ALT (fetch_fifo64.sv gen_alt)
  if (AltEnable) begin : gen_alt_sva
    // rtl/fetch_fifo64.sv:486-501: an ALT restore never reads a free entry (alt_err_event, KUDU-045)
    AssertAltApplyValidEntry: assert property (@(posedge clk_i) disable iff (!rst_ni)
      !ff_alt_err_event)
      else $error("SVA_IF: ALT restore from a free ALT entry");

    // rtl/fetch_fifo64.sv:490, rtl/if_stage.sv:94-95: ALT restore only on an EX redirect
    AssertAltApplyNeedsExPcSet: assert property (@(posedge clk_i) disable iff (!rst_ni)
      ex_alt_ctrl_i.apply && branch_req |-> ex_pc_set_i)
      else $error("SVA_IF: ALT restore on a redirect not requested by EX");

    // rtl/fetch_fifo64.sv:492,538: ALT allocation only into a free entry
    AssertAltAllocFree: assert property (@(posedge clk_i) disable iff (!rst_ni)
      ff_alloc_alt |-> ff_alt_free_id < 2'd2 && !ff_alt_status[ff_alt_free_id[0]])
      else $error("SVA_IF: ALT allocation into a busy entry");
  end

`endif  // KUDU_FCOV_OFF

endmodule

// ============================================================================
// kudu_sva_if_cdec -- compressed_decoder against a reference RVC expansion
// written from the RISC-V C spec plus the CHERIoT compressed forms
// (c.incaddr4cspn, c.incaddr16csp, c.clc, c.csc, c.clcsp, c.cscsp) used when
// CHERIoTEn & cheri_pmode_i.  Bound to every compressed_decoder instance
// (if_stage or ir_stage, depending on IfCompDecEn) as u_fcov_sva_if_cdec.
// ============================================================================
module kudu_sva_if_cdec
  import super_pkg::*;
#(
  parameter bit CHERIoTEn = 1'b1
) (
  input logic    clk_i,
  input logic    rst_ni,
  input logic    cheri_pmode_i,
  input ir_reg_t instr_i,
  input ir_reg_t instr_o
);

`ifndef KUDU_FCOV_OFF

  function automatic logic [31:0] enc_i(logic [11:0] imm, logic [4:0] rs1, logic [2:0] f3,
                                        logic [4:0] rd, logic [6:0] op);
    return {imm, rs1, f3, rd, op};
  endfunction

  function automatic logic [31:0] enc_s(logic [11:0] imm, logic [4:0] rs2, logic [4:0] rs1,
                                        logic [2:0] f3, logic [6:0] op);
    return {imm[11:5], rs2, rs1, f3, imm[4:0], op};
  endfunction

  function automatic logic [31:0] enc_r(logic [6:0] f7, logic [4:0] rs2, logic [4:0] rs1,
                                        logic [2:0] f3, logic [4:0] rd, logic [6:0] op);
    return {f7, rs2, rs1, f3, rd, op};
  endfunction

  function automatic logic [31:0] enc_b(logic [12:0] imm, logic [4:0] rs1, logic [2:0] f3);
    return {imm[12], imm[10:5], 5'd0, rs1, f3, imm[4:1], imm[11], 7'(OPCODE_BRANCH)};
  endfunction

  function automatic logic [31:0] enc_j(logic [20:0] imm, logic [4:0] rd);
    return {imm[20], imm[10:1], imm[11], imm[19:12], rd, 7'(OPCODE_JAL)};
  endfunction

  logic [15:0] c;
  logic        pm;
  logic [4:0]  rd, rs2, rdp, rs2p;
  logic [5:0]  imm6;
  logic [31:0] ref_insn;
  logic        ref_ill, ref_hint;

  assign c    = instr_i.insn[15:0];
  assign pm   = CHERIoTEn & cheri_pmode_i;
  assign rd   = c[11:7];
  assign rs2  = c[6:2];
  assign rdp  = {2'b01, c[9:7]};
  assign rs2p = {2'b01, c[4:2]};
  assign imm6 = {c[12], c[6:2]};

  always_comb begin
    ref_insn = instr_i.insn;
    ref_ill  = 1'b0;
    ref_hint = 1'b0;
    case (c[1:0])
      2'b00: case (c[15:13])
        3'b000: begin   // c.addi4spn / c.incaddr4cspn: nzuimm[5:4|9:6|2|3]
          ref_insn = enc_i({2'b00, c[10:7], c[12:11], c[5], c[6], 2'b00}, 5'd2,
                           pm ? 3'b001 : 3'b000, rs2p, pm ? 7'(OPCODE_CHERI) : 7'(OPCODE_OP_IMM));
          ref_ill  = (c[12:5] == 8'd0);
        end
        3'b010: ref_insn = enc_i({5'd0, c[5], c[12:10], c[6], 2'b00}, rdp, 3'b010, rs2p,
                                 7'(OPCODE_LOAD));                                   // c.lw
        3'b011: if (pm) ref_insn = enc_i({4'd0, c[6:5], c[12:10], 3'b000}, rdp, 3'b011, rs2p,
                                         7'(OPCODE_LOAD));                           // c.clc
                else    ref_ill  = 1'b1;
        3'b110: ref_insn = enc_s({5'd0, c[5], c[12:10], c[6], 2'b00}, rs2p, rdp, 3'b010,
                                 7'(OPCODE_STORE));                                  // c.sw
        3'b111: if (pm) ref_insn = enc_s({4'd0, c[6:5], c[12:10], 3'b000}, rs2p, rdp, 3'b011,
                                         7'(OPCODE_STORE));                          // c.csc
                else    ref_ill  = 1'b1;
        default: ref_ill = 1'b1;                                                     // 001/100/101
      endcase

      2'b01: case (c[15:13])
        3'b000: begin   // c.addi (rd=0 or imm=0: nop/HINT)
          ref_hint = (rd == 5'd0) || (imm6 == 6'd0);
          ref_insn = enc_i({{6{c[12]}}, imm6}, rd, 3'b000, rd, 7'(OPCODE_OP_IMM));
        end
        3'b001, 3'b101:  // c.jal / c.j: offset[11|4|9:8|10|6|7|3:1|5]
          ref_insn = enc_j({{10{c[12]}}, c[8], c[10:9], c[6], c[7], c[2], c[11], c[5:3], 1'b0},
                           c[15] ? 5'd0 : 5'd1);
        3'b010: begin   // c.li
          ref_hint = (rd == 5'd0);
          ref_insn = enc_i({{6{c[12]}}, imm6}, 5'd0, 3'b000, rd, 7'(OPCODE_OP_IMM));
        end
        3'b011: begin
          ref_ill = (imm6 == 6'd0);
          if (rd == 5'd2)  // c.addi16sp / c.incaddr16csp: nzimm[9|4|6|8:7|5]
            ref_insn = enc_i({{3{c[12]}}, c[4:3], c[5], c[2], c[6], 4'd0}, 5'd2,
                             pm ? 3'b001 : 3'b000, 5'd2,
                             pm ? 7'(OPCODE_CHERI) : 7'(OPCODE_OP_IMM));
          else begin       // c.lui (rd=0: HINT)
            ref_hint = (rd == 5'd0);
            ref_insn = {{14{c[12]}}, imm6, rd, 7'(OPCODE_LUI)};
          end
        end
        3'b100: case (c[11:10])
          2'b00, 2'b01: begin  // c.srli / c.srai; shamt[5]=1 reserved in RV32, 0: HINT
            ref_ill  = c[12];
            ref_hint = (c[6:2] == 5'd0);
            ref_insn = enc_r({1'b0, c[10], 5'd0}, c[6:2], rdp, 3'b101, rdp, 7'(OPCODE_OP_IMM));
          end
          2'b10: ref_insn = enc_i({{6{c[12]}}, imm6}, rdp, 3'b111, rdp, 7'(OPCODE_OP_IMM));
          default: begin
            if (c[12]) ref_ill = 1'b1;   // c.subw/c.addw and reserved (RV64 only)
            else case (c[6:5])
              2'b00: ref_insn = enc_r(7'b0100000, rs2p, rdp, 3'b000, rdp, 7'(OPCODE_OP));
              2'b01: ref_insn = enc_r(7'b0000000, rs2p, rdp, 3'b100, rdp, 7'(OPCODE_OP));
              2'b10: ref_insn = enc_r(7'b0000000, rs2p, rdp, 3'b110, rdp, 7'(OPCODE_OP));
              default: ref_insn = enc_r(7'b0000000, rs2p, rdp, 3'b111, rdp, 7'(OPCODE_OP));
            endcase
          end
        endcase
        default:  // c.beqz / c.bnez: offset[8|4:3|7:6|2:1|5]
          ref_insn = enc_b({{5{c[12]}}, c[6:5], c[2], c[11:10], c[4:3], 1'b0}, rdp,
                           {2'b00, c[13]});
      endcase

      2'b10: case (c[15:13])
        3'b000: begin   // c.slli; shamt[5]=1 reserved in RV32; rd=0 or shamt=0: HINT
          ref_ill  = c[12];
          ref_hint = (rd == 5'd0) || (c[6:2] == 5'd0);
          ref_insn = enc_i({7'd0, c[6:2]}, rd, 3'b001, rd, 7'(OPCODE_OP_IMM));
        end
        3'b010: begin   // c.lwsp: uimm[5|4:2|7:6]
          ref_ill  = (rd == 5'd0);
          ref_insn = enc_i({4'd0, c[3:2], c[12], c[6:4], 2'b00}, 5'd2, 3'b010, rd,
                           7'(OPCODE_LOAD));
        end
        3'b011: begin   // c.clcsp: uimm[5|4:3|8:6]
          ref_ill  = !pm || (rd == 5'd0);
          if (pm) ref_insn = enc_i({3'd0, c[4:2], c[12], c[6:5], 3'b000}, 5'd2, 3'b011, rd,
                                   7'(OPCODE_LOAD));
        end
        3'b100: begin
          if (!c[12] && rs2 == 5'd0) begin         // c.jr
            ref_ill  = (rd == 5'd0);
            ref_insn = enc_i(12'd0, rd, 3'b000, 5'd0, 7'(OPCODE_JALR));
          end else if (!c[12]) begin               // c.mv (rd=0: HINT)
            ref_hint = (rd == 5'd0);
            ref_insn = enc_r(7'd0, rs2, 5'd0, 3'b000, rd, 7'(OPCODE_OP));
          end else if (rs2 == 5'd0 && rd == 5'd0) begin
            ref_insn = 32'h0010_0073;              // c.ebreak
          end else if (rs2 == 5'd0) begin          // c.jalr
            ref_insn = enc_i(12'd0, rd, 3'b000, 5'd1, 7'(OPCODE_JALR));
          end else begin                           // c.add (rd=0: HINT)
            ref_hint = (rd == 5'd0);
            ref_insn = enc_r(7'd0, rs2, rd, 3'b000, rd, 7'(OPCODE_OP));
          end
        end
        3'b110: ref_insn = enc_s({4'd0, c[8:7], c[12:9], 2'b00}, rs2, 5'd2, 3'b010,
                                 7'(OPCODE_STORE));                                  // c.swsp
        3'b111: if (pm) ref_insn = enc_s({3'd0, c[9:7], c[12:10], 3'b000}, rs2, 5'd2, 3'b011,
                                         7'(OPCODE_STORE));                          // c.cscsp
                else    ref_ill  = 1'b1;
        default: ref_ill = 1'b1;                   // 001/101: c.fldsp/c.fsdsp
      endcase

      default: ;  // 32-bit instruction
    endcase
  end

  // rtl/compressed_decoder.sv:50-359: illegal_c_insn matches the RVC/CHERIoT reference
  AssertCdecIllegalRef: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !$isunknown(c) |-> kudu_fcov_pkg::sva_xok(instr_o.errs.illegal_c_insn == ref_ill))
    else $error("SVA_IF: compressed_decoder illegal_c_insn differs from the RVC reference");

  // rtl/compressed_decoder.sv:53-359: legal non-HINT RVC expands to the spec 32-bit instruction
  AssertCdecExpandRef: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !$isunknown(c) && !ref_ill && !ref_hint |-> kudu_fcov_pkg::sva_xok(instr_o.insn == ref_insn))
    else $error("SVA_IF: compressed_decoder expansion differs from the RVC reference");

  // rtl/compressed_decoder.sv:126: HINTs expand to an rd=x0 OP/OP-IMM/LUI (no effect)
  AssertCdecHintNop: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !$isunknown(c) && !ref_ill && ref_hint |->
      instr_o.insn[11:7] == 5'd0 &&
      (instr_o.insn[6:0] inside {7'(OPCODE_OP), 7'(OPCODE_OP_IMM), 7'(OPCODE_LUI)}))
    else $error("SVA_IF: compressed HINT expands to an instruction with an effect");

  // rtl/compressed_decoder.sv:35-36: 32-bit instructions pass unchanged
  AssertCdecPassthrough32: assert property (@(posedge clk_i) disable iff (!rst_ni)
    instr_i.insn[1:0] == 2'b11 |-> instr_o.insn == instr_i.insn)
    else $error("SVA_IF: 32-bit instruction altered by compressed_decoder");

  // rtl/compressed_decoder.sv:35-39: only insn, c_insn and illegal_c_insn are changed
  AssertCdecFieldsPass: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_fcov_pkg::sva_xok(instr_o.c_insn == c && instr_o.pc == instr_i.pc &&
    instr_o.errs.fetch_err == instr_i.errs.fetch_err &&
    instr_o.errs.illegal_insn == instr_i.errs.illegal_insn &&
    {instr_o.errs.asr_vio, instr_o.errs.perm_vio, instr_o.errs.bound_vio} ==
      {instr_i.errs.asr_vio, instr_i.errs.perm_vio, instr_i.errs.bound_vio} &&
    {instr_o.ferr2w, instr_o.is_comp, instr_o.is_branch, instr_o.is_jal, instr_o.is_jalr,
     instr_o.ptaken, instr_o.ptarget, instr_o.alt_valid, instr_o.alt_id} ==
    {instr_i.ferr2w, instr_i.is_comp, instr_i.is_branch, instr_i.is_jal, instr_i.is_jalr,
     instr_i.ptaken, instr_i.ptarget, instr_i.alt_valid, instr_i.alt_id}))
    else $error("SVA_IF: compressed_decoder altered a pass-through field");

`endif  // KUDU_FCOV_OFF

endmodule

// ============================================================================
// FV helper lemmas: formal only, compiled only with +define+KUDU_FV_HELPERS.
//
// Auxiliary invariants that JasperGold proves and then assumes (run_fcov_clean
// in fv/fv_kudu_fcov.tcl) so that the harder assertions above become
// inductive. No covergroups; simulation never defines KUDU_FV_HELPERS. They
// are bound only in the KUDU_FV_HELPERS block at the end of kudu_fcov_bind.sv,
// which sits inside its KUDU_FCOV_OFF and CHERIoT guards. They read the fcov
// instances bound there and were proven only with CHERIoTEn=1, so the
// definitions carry the same guards: an unbound copy would become an extra
// top-level module with unresolvable kudu_top.* references.
// ============================================================================
`ifdef KUDU_FV_HELPERS
`ifdef CHERIoT
`ifndef KUDU_FCOV_OFF

// kudu_fvh_front_pc (was fv/fv_help_front_pc.sv, bound into kudu_top as
// u_fvh_front_pc). Supports the front-end pc-chain targets:
// kudu_sva_if AssertFifoAddrCoherent / AssertAltApplyNeedsExPcSet, the s0
// dual_fifo u_ref AssertFifoRdData0/1, kudu_sva_id AssertIrPcContinuity /
// AssertIrSlotOrder and kudu_sva_issue AssertIr0PcTracksNxtPc /
// AssertIr1PcFollowsIr0 / AssertTrapPcIsNxtPc.
//
// front_pc helper lemmas (FV only)
module kudu_fvh_front_pc import super_pkg::*; (
  input logic clk_i,
  input logic rst_ni
);

  localparam int unsigned RW = $bits(ir_reg_t);

  function automatic logic [15:0] fold(logic [RW-1:0] d);
    logic [15:0] f; f = '0;
    for (int unsigned b = 0; b < RW; b++) f[b % 16] = f[b % 16] ^ d[b];
    return f;
  endfunction

  function automatic logic [31:0] succ0(ir_reg_t e);
    return e.ptaken ? e.ptarget : (e.pc + (e.is_comp ? 32'd2 : 32'd4));
  endfunction
  function automatic logic [31:0] succ1(ir_dec_t d);
    return d.ptaken ? d.ptarget[31:0] : d.pc_nxt;
  endfunction
  function automatic logic unk1(ir_dec_t d);
    return d.is_jalr && !d.ptaken;
  endfunction
  function automatic logic [31:0] rnxt(ir_dec_t d);
    return ((d.is_branch | d.is_jal | d.is_jalr) & d.ptaken) ? d.ptarget[31:0] : d.pc_nxt;
  endfunction

  // ---------------- state taps
  logic [31:0] nxt;
  assign nxt = kudu_top.issuer_i.ir0_nxt_pc_q;

  ir_reg_t     s0m [4];
  logic [2:0]  s0_rp, s0_wp, s0_cnt;
  ir_reg_t     s0e [4];
  for (genvar i = 0; i < 4; i++) begin : g_s0
    assign s0m[i] = kudu_top.ir_stage_i.gen_stage0_buffer.s0_fifo.fifo_mem[i];
  end
  assign s0_rp  = kudu_top.ir_stage_i.gen_stage0_buffer.s0_fifo.rd_ptr_q;
  assign s0_wp  = kudu_top.ir_stage_i.gen_stage0_buffer.s0_fifo.wr_ptr_q;
  assign s0_cnt = s0_wp - s0_rp;
  for (genvar j = 0; j < 4; j++) begin : g_s0e
    logic [1:0] ix;
    assign ix = s0_rp[1:0] + 2'(j);
    assign s0e[j] = s0m[ix];
  end

  ir_dec_t     s1m [2];
  logic        s1_rp, s1_wp, s1_full;
  logic [1:0]  s1_cnt;
  ir_dec_t     s1e0, s1e1, s1t;
  assign s1m[0]  = kudu_top.ir_stage_i.gen_stage1.s1_fifo.fifo_mem[0];
  assign s1m[1]  = kudu_top.ir_stage_i.gen_stage1.s1_fifo.fifo_mem[1];
  assign s1_rp   = kudu_top.ir_stage_i.gen_stage1.s1_fifo.rd_ptr_q;
  assign s1_wp   = kudu_top.ir_stage_i.gen_stage1.s1_fifo.wr_ptr_q;
  assign s1_full = kudu_top.ir_stage_i.gen_stage1.s1_fifo.full_stat_q;
  assign s1_cnt  = s1_full ? 2'd2 : (s1_wp != s1_rp) ? 2'd1 : 2'd0;
  assign s1e0    = s1m[s1_rp];
  assign s1e1    = s1m[~s1_rp];
  assign s1t     = (s1_cnt == 2'd2) ? s1e1 : s1e0;

  ir_reg_t     s0last;
  assign s0last = s0e[2'(s0_cnt - 3'd1)];

  logic [31:0] if_pc;
  assign if_pc = {kudu_top.if_stage_i.prefetch_buffer_i.fifo_i.instr_addr_q, 1'b0};

  // ---------------- PC chain
  // s1 entries carry pc_nxt = pc + len
  AssertHelpFpcS1PcNxt0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (s1_cnt != 0) |-> s1e0.pc_nxt == s1e0.pc + (s1e0.is_comp ? 32'd2 : 32'd4));
  AssertHelpFpcS1PcNxt1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (s1_cnt == 2) |-> s1e1.pc_nxt == s1e1.pc + (s1e1.is_comp ? 32'd2 : 32'd4));
  // s1 entry1 follows entry0 (unless entry0 is a revoked cjalr prediction)
  AssertHelpFpcS1Chain: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (s1_cnt == 2) && !unk1(s1e0) |-> s1e1.pc == succ1(s1e0));
  // s1 head is ir0_nxt_pc_q
  AssertHelpFpcS1Head: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (s1_cnt != 0) |-> s1e0.pc == nxt);
  // s0 head follows s1 tail (or is ir0_nxt_pc_q when s1 empty)
  AssertHelpFpcS0Head: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (s0_cnt != 0) && !((s1_cnt != 0) && unk1(s1t)) |->
      s0e[0].pc == ((s1_cnt == 0) ? nxt : succ1(s1t)));
  // s0 internal chain
  for (genvar j = 1; j < 4; j++) begin : g_s0chain
    AssertHelpFpcS0Chain: assert property (@(posedge clk_i) disable iff (!rst_ni)
      (s0_cnt > j) |-> s0e[j].pc == succ0(s0e[j-1]));
  end
  // IF fetch pc follows the youngest IR entry
  AssertHelpFpcIfPc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !((s0_cnt == 0) && (s1_cnt != 0) && unk1(s1t)) |->
      if_pc == ((s0_cnt != 0) ? succ0(s0last) : (s1_cnt != 0) ? succ1(s1t) : nxt));
  // fcov_id shadow agrees with the issuer
  AssertHelpFpcIdExp: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.ir_stage_i.u_fcov_sva_id.exp_valid |-> kudu_top.ir_stage_i.u_fcov_sva_id.exp_pc == nxt);
  // ptaken non-CTI never in s1
  AssertHelpFpcS1PtakenCti0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (s1_cnt != 0) && s1e0.ptaken |-> (s1e0.is_branch | s1e0.is_jal | s1e0.is_jalr));
  AssertHelpFpcS1PtakenCti1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (s1_cnt == 2) && s1e1.ptaken |-> (s1e1.is_branch | s1e1.is_jal | s1e1.is_jalr));

  // ---------------- s0 dual_fifo vs reference model
  for (genvar i = 0; i < 4; i++) begin : g_ref
    logic [1:0] off;
    assign off = 2'(i) - s0_rp[1:0];
    AssertHelpFpcRefMem: assert property (@(posedge clk_i) disable iff (!rst_ni)
      (3'(off) < s0_cnt) |->
        kudu_top.ir_stage_i.gen_stage0_buffer.s0_fifo.u_fcov_sva_dual_fifo.u_ref.mem_q[i] == fold(s0m[i]));
  end
  AssertHelpFpcRefPtr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.ir_stage_i.gen_stage0_buffer.s0_fifo.u_fcov_sva_dual_fifo.u_ref.rp_q == s0_rp[1:0]) &&
    (kudu_top.ir_stage_i.gen_stage0_buffer.s0_fifo.u_fcov_sva_dual_fifo.u_ref.wp_q == s0_wp[1:0]));

  // ---------------- issuer special cases
  AssertHelpFpcSpecValid: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL] &&
    (kudu_top.issuer_i.special_case_q inside {EXEC, SYSCTL, CMPLX, STEP}) |-> kudu_top.issuer_i.ir_valid_i[0]);
  AssertHelpFpcStepSetpc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL] && (kudu_top.issuer_i.special_case_q == STEP) |->
      kudu_top.issuer_i.special_setpc_q == kudu_top.issuer_i.mispredict[0]);
  AssertHelpFpcSpecNoMnt: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL] &&
    (kudu_top.issuer_i.special_case_q inside {SYSCTL, CMPLX}) |-> !kudu_top.issuer_i.branch_info_i.mis_not_taken[0]);
  AssertHelpFpcSpecApply: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ir0_special_issued && kudu_top.issuer_i.ir0_dec.alt_valid &&
    kudu_top.issuer_i.branch_info_i.mis_not_taken[0] |-> kudu_top.issuer_i.special_setpc_q);

  // ---------------- ALT table entries referenced from IR
  logic [31:0] alt_na0, alt_na1;
  logic [2:0]  alt_v0, alt_v1;
  assign alt_na0 = kudu_top.if_stage_i.prefetch_buffer_i.fifo_i.gen_alt.alt_table[0].nxt_addr;
  assign alt_na1 = kudu_top.if_stage_i.prefetch_buffer_i.fifo_i.gen_alt.alt_table[1].nxt_addr;
  assign alt_v0  = kudu_top.if_stage_i.prefetch_buffer_i.fifo_i.gen_alt.alt_table[0].valid;
  assign alt_v1  = kudu_top.if_stage_i.prefetch_buffer_i.fifo_i.gen_alt.alt_table[1].valid;
  function automatic logic alt_ok(logic [31:0] spc, logic [1:0] id, logic [31:0] na0, logic [31:0] na1,
                                  logic [2:0] v0, logic [2:0] v1);
    logic [31:0] na; logic [2:0] v;
    na = id[0] ? na1 : na0;
    v  = id[0] ? v1 : v0;
    return (na[2:0] == 3'b000) && (na[31:3] == spc[31:3] + 29'($countones(v)));
  endfunction
  for (genvar j = 0; j < 4; j++) begin : g_alt0
    AssertHelpFpcAltS0: assert property (@(posedge clk_i) disable iff (!rst_ni)
      (s0_cnt > j) && s0e[j].alt_valid |->
        alt_ok(s0e[j].pc + (s0e[j].is_comp ? 32'd2 : 32'd4), s0e[j].alt_id, alt_na0, alt_na1, alt_v0, alt_v1));
  end
  AssertHelpFpcAltS1e0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (s1_cnt != 0) && s1e0.alt_valid |-> alt_ok(s1e0.pc_nxt, s1e0.alt_id, alt_na0, alt_na1, alt_v0, alt_v1));
  AssertHelpFpcAltS1e1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (s1_cnt == 2) && s1e1.alt_valid |-> alt_ok(s1e1.pc_nxt, s1e1.alt_id, alt_na0, alt_na1, alt_v0, alt_v1));

  // ---------------- conjunctions (inductive as a whole)
  logic chain_ok, ref_ok, alt_ok_all;
  always_comb begin
    chain_ok = 1'b1;
    if (s1_cnt != 0) chain_ok &= (s1e0.pc_nxt == s1e0.pc + (s1e0.is_comp ? 32'd2 : 32'd4)) && (s1e0.pc == nxt);
    if (s1_cnt == 2) chain_ok &= (s1e1.pc_nxt == s1e1.pc + (s1e1.is_comp ? 32'd2 : 32'd4));
    if ((s1_cnt == 2) && !unk1(s1e0)) chain_ok &= (s1e1.pc == succ1(s1e0));
    if ((s0_cnt != 0) && !((s1_cnt != 0) && unk1(s1t)))
      chain_ok &= (s0e[0].pc == ((s1_cnt == 0) ? nxt : succ1(s1t)));
    for (int j = 1; j < 4; j++) if (s0_cnt > j) chain_ok &= (s0e[j].pc == succ0(s0e[j-1]));
    if (!((s0_cnt == 0) && (s1_cnt != 0) && unk1(s1t)))
      chain_ok &= (if_pc == ((s0_cnt != 0) ? succ0(s0last) : (s1_cnt != 0) ? succ1(s1t) : nxt));
    if (kudu_top.ir_stage_i.u_fcov_sva_id.exp_valid) chain_ok &= (kudu_top.ir_stage_i.u_fcov_sva_id.exp_pc == nxt);
  end
  AssertHelpFpcChainAll: assert property (@(posedge clk_i) disable iff (!rst_ni) chain_ok);

  always_comb begin
    ref_ok = (kudu_top.ir_stage_i.gen_stage0_buffer.s0_fifo.u_fcov_sva_dual_fifo.u_ref.rp_q == s0_rp[1:0]) &&
             (kudu_top.ir_stage_i.gen_stage0_buffer.s0_fifo.u_fcov_sva_dual_fifo.u_ref.wp_q == s0_wp[1:0]);
    for (int i = 0; i < 4; i++)
      if (3'(2'(i) - s0_rp[1:0]) < s0_cnt)
        ref_ok &= (kudu_top.ir_stage_i.gen_stage0_buffer.s0_fifo.u_fcov_sva_dual_fifo.u_ref.mem_q[i] == fold(s0m[i]));
  end
  AssertHelpFpcRefAll: assert property (@(posedge clk_i) disable iff (!rst_ni) ref_ok);

  always_comb begin
    alt_ok_all = 1'b1;
    for (int j = 0; j < 4; j++)
      if ((s0_cnt > j) && s0e[j].alt_valid)
        alt_ok_all &= alt_ok(s0e[j].pc + (s0e[j].is_comp ? 32'd2 : 32'd4), s0e[j].alt_id, alt_na0, alt_na1, alt_v0, alt_v1);
    if ((s1_cnt != 0) && s1e0.alt_valid) alt_ok_all &= alt_ok(s1e0.pc_nxt, s1e0.alt_id, alt_na0, alt_na1, alt_v0, alt_v1);
    if ((s1_cnt == 2) && s1e1.alt_valid) alt_ok_all &= alt_ok(s1e1.pc_nxt, s1e1.alt_id, alt_na0, alt_na1, alt_v0, alt_v1);
  end
  AssertHelpFpcAltAll: assert property (@(posedge clk_i) disable iff (!rst_ni) alt_ok_all);

  // ---------------- single-step special issue: decision inputs stable since WAIT_CMT0
  logic [31:0] h0_a, h0_b;
  assign h0_a = kudu_top.issuer_i.ira_is0_i ? kudu_top.ira_full_data2_fwd.d0[31:0] : kudu_top.irb_full_data2_fwd.d0[31:0];
  assign h0_b = kudu_top.issuer_i.ira_is0_i ? kudu_top.ira_full_data2_fwd.d1[31:0] : kudu_top.irb_full_data2_fwd.d1[31:0];
  AssertHelpFpcStepPast: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL] && (kudu_top.issuer_i.special_case_q == STEP) |->
      $past(kudu_top.issuer_i.ctrl_fsm_cs[CSM_WAIT_CMT0]) &&
      (kudu_top.issuer_i.special_setpc_q == $past(kudu_top.issuer_i.mispredict[0])));
  AssertHelpFpcStepOpStable: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL] && (kudu_top.issuer_i.special_case_q == STEP) |->
      $stable(kudu_top.issuer_i.ira_is0_i) && $stable(h0_a) && $stable(h0_b));
  AssertHelpFpcStepMntStable: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL] && (kudu_top.issuer_i.special_case_q == STEP) |->
      $stable(kudu_top.issuer_i.branch_info_i.mis_not_taken[0]));

  // ---------------- ALT ownership: each busy ALT entry is referenced by exactly one IR branch
  logic [1:0] alt_st;
  assign alt_st = kudu_top.if_stage_i.prefetch_buffer_i.fifo_i.alt_status;
  logic [2:0] own_cnt [2];
  logic       own_ok;
  always_comb begin
    own_cnt[0] = '0; own_cnt[1] = '0; own_ok = 1'b1;
    for (int j = 0; j < 4; j++)
      if ((s0_cnt > j) && s0e[j].alt_valid) begin
        own_ok &= (s0e[j].alt_id < 2'd2) && s0e[j].is_branch && s0e[j].ptaken;
        own_cnt[s0e[j].alt_id[0]] += 3'd1;
      end
    if ((s1_cnt != 0) && s1e0.alt_valid) begin
      own_ok &= (s1e0.alt_id < 2'd2);
      own_cnt[s1e0.alt_id[0]] += 3'd1;
    end
    if ((s1_cnt == 2) && s1e1.alt_valid) begin
      own_ok &= (s1e1.alt_id < 2'd2);
      own_cnt[s1e1.alt_id[0]] += 3'd1;
    end
    own_ok &= (own_cnt[0] == 3'(alt_st[0])) && (own_cnt[1] == 3'(alt_st[1]));
  end
  AssertHelpFpcAltOwn: assert property (@(posedge clk_i) disable iff (!rst_ni) own_ok);
  AssertHelpFpcAltOwnOk: assert property (@(posedge clk_i) disable iff (!rst_ni) own_ok && alt_ok_all);

  // ---------------- ALT apply: restored FIFO image matches the redirect target
  AssertHelpFpcApplyOk: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.if_stage_i.prefetch_buffer_i.fifo_i.apply_alt |->
      alt_ok({kudu_top.if_stage_i.ex_pc_target_i[31:1], 1'b0}, kudu_top.if_stage_i.prefetch_buffer_i.fifo_i.alt_apply_id,
             alt_na0, alt_na1, alt_v0, alt_v1));

  // ---------------- drained special issue: operands come straight from the (stable) register file
  AssertHelpFpcFwdIdle: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.issuer_i.ctrl_fsm_cs[CSM_WAIT_CMT0] && !kudu_top.issuer_i.sbdfifo_rd_valid_i[0] &&
     !kudu_top.issuer_i.trvk_outstanding_i) || kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL] |->
      (kudu_top.issuer_i.ira_op_data2_fwd == kudu_top.issuer_i.ira_op_rdata2_i) &&
      (kudu_top.issuer_i.irb_op_data2_fwd == kudu_top.issuer_i.irb_op_rdata2_i));
  AssertHelpFpcRfStable: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL] && (kudu_top.issuer_i.special_case_q == STEP) |->
      $stable(kudu_top.regfile_i.rf_reg_q));
  AssertHelpFpcRdStable: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL] && (kudu_top.issuer_i.special_case_q == STEP) |->
      $stable(kudu_top.issuer_i.ira_is0_i) && $stable(kudu_top.issuer_i.ira_op_rdata2_i) &&
      $stable(kudu_top.issuer_i.irb_op_rdata2_i));

  logic [31:0] ra0, ra1, rb0, rb1;
  assign ra0 = kudu_top.ir_stage_i.ira_rf_rdata2_q.d0[31:0];
  assign ra1 = kudu_top.ir_stage_i.ira_rf_rdata2_q.d1[31:0];
  assign rb0 = kudu_top.ir_stage_i.irb_rf_rdata2_q.d0[31:0];
  assign rb1 = kudu_top.ir_stage_i.irb_rf_rdata2_q.d1[31:0];
  AssertHelpFpcRdLoStable: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL] && (kudu_top.issuer_i.special_case_q == STEP) |->
      $stable(kudu_top.issuer_i.ira_is0_i) &&
      $stable(kudu_top.issuer_i.ira_is0_i ? ra0 : rb0) && $stable(kudu_top.issuer_i.ira_is0_i ? ra1 : rb1));
  AssertHelpFpcFwdLoIdle: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.issuer_i.ctrl_fsm_cs[CSM_WAIT_CMT0] && !kudu_top.issuer_i.sbdfifo_rd_valid_i[0] &&
     !kudu_top.issuer_i.trvk_outstanding_i) || kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL] |->
      (kudu_top.ira_full_data2_fwd.d0[31:0] == ra0) && (kudu_top.ira_full_data2_fwd.d1[31:0] == ra1) &&
      (kudu_top.irb_full_data2_fwd.d0[31:0] == rb0) && (kudu_top.irb_full_data2_fwd.d1[31:0] == rb1));

  // per-entry ALT ownership (alloc/cancel/flush of entry i only depend on alt_status[i])
  logic own_id_ok;
  always_comb begin
    own_id_ok = 1'b1;
    for (int j = 0; j < 4; j++) if ((s0_cnt > j) && s0e[j].alt_valid) own_id_ok &= (s0e[j].alt_id < 2'd2);
    if ((s1_cnt != 0) && s1e0.alt_valid) own_id_ok &= (s1e0.alt_id < 2'd2);
    if ((s1_cnt == 2) && s1e1.alt_valid) own_id_ok &= (s1e1.alt_id < 2'd2);
  end
  AssertHelpFpcAltIdOk: assert property (@(posedge clk_i) disable iff (!rst_ni) own_id_ok);
  for (genvar i = 0; i < 2; i++) begin : g_own
    AssertHelpFpcAltOwnI: assert property (@(posedge clk_i) disable iff (!rst_ni) own_cnt[i] == 3'(alt_st[i]));
  end

  // drained issuer: no pipeline forwards a result
  logic drained;
  assign drained = (kudu_top.issuer_i.ctrl_fsm_cs[CSM_WAIT_CMT0] && !kudu_top.issuer_i.sbdfifo_rd_valid_i[0] &&
                    !kudu_top.issuer_i.trvk_outstanding_i) || kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL];
  AssertHelpFpcFwdNone0: assert property (@(posedge clk_i) disable iff (!rst_ni) drained |-> kudu_top.issuer_i.alupl0_fwd_info_i.valid == 2'b00);
  AssertHelpFpcFwdNone1: assert property (@(posedge clk_i) disable iff (!rst_ni) drained |-> kudu_top.issuer_i.alupl1_fwd_info_i.valid == 2'b00);
  AssertHelpFpcFwdNone2: assert property (@(posedge clk_i) disable iff (!rst_ni) drained |-> kudu_top.issuer_i.lspl_fwd_info_i.valid == 2'b00);
  AssertHelpFpcFwdNone3: assert property (@(posedge clk_i) disable iff (!rst_ni) drained |-> kudu_top.issuer_i.multpl_fwd_info_i.valid == 2'b00);
  // drained issuer: an LSU/dcache forward still valid carries exactly the RF value (harmless)
  AssertHelpFpcFwdLsRf0: assert property (@(posedge clk_i) disable iff (!rst_ni) drained && kudu_top.issuer_i.lspl_fwd_info_i.valid[0] &&
      (kudu_top.issuer_i.lspl_fwd_info_i.addr0 != 0) |-> kudu_top.issuer_i.lspl_fwd_info_i.data0[31:0] == kudu_top.regfile_i.rf_reg_q[kudu_top.issuer_i.lspl_fwd_info_i.addr0][31:0]);
  AssertHelpFpcFwdLsRf1: assert property (@(posedge clk_i) disable iff (!rst_ni) drained && kudu_top.issuer_i.lspl_fwd_info_i.valid[1] &&
      (kudu_top.issuer_i.lspl_fwd_info_i.addr1 != 0) |-> kudu_top.issuer_i.lspl_fwd_info_i.data1[31:0] == kudu_top.regfile_i.rf_reg_q[kudu_top.issuer_i.lspl_fwd_info_i.addr1][31:0]);
  // drained issuer: LSU pipeline-stage forward (slot 0) is idle
  AssertHelpFpcFwdNone2v0: assert property (@(posedge clk_i) disable iff (!rst_ni) drained |-> !kudu_top.issuer_i.lspl_fwd_info_i.valid[0]);

endmodule

`endif  // KUDU_FCOV_OFF
`endif  // CHERIoT
`endif  // KUDU_FV_HELPERS
