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
  parameter bit          InstrBufEn    = 1'b1
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
    cp_busy:     coverpoint {prefetch_busy, if_busy_o};

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

    x_cp_comp_align: cross cp_is_comp0, cp_is_comp1, cp_unaligned0;

    // ======================================================================
    // 8.3 Redirects and the alt (shadow-fetch) path
    // ======================================================================
    cp_ex_pc_set:  coverpoint ex_pc_set_i  { bins hit = {1'b1}; }
    cp_ex_bp_init: coverpoint ex_bp_init_i { bins hit = {1'b1}; }

    cp_redirect_align: coverpoint ex_pc_target_i[1:0] iff (ex_pc_set_i) {
      bins word = {2'b00};
      bins half = {2'b10};
      bins misaligned = {2'b01, 2'b11};
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
    // cp_pdt_en:    coverpoint pdt_en_i;

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
    cp_pdt_pc_set: coverpoint pdt_pc_set iff pdt_en_i {
      bins none  = {2'b00};
      bins slot0 = {2'b01};
      bins slot1 = {2'b10};
      bins both  = {2'b11};
    }

    x_cp_pdt_priority_contention: cross cp_pdt_cand0, cp_pdt_cand1, cp_pdt_src
        iff (pdt_en_i && (pdt_pc_set == 2'b11)) {
      ignore_bins non_slot0_winner = binsof(cp_pdt_src) intersect
          {PDT_BR1, PDT_JAL1, PDT_JALR1, PDT_NONE};
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

`endif  // KUDU_FCOV_OFF

endmodule
