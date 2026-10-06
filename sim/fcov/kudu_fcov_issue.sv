// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// FC_MA_ISSUE -- issue control, hazards, forwarding, controller FSM and
// trap / IRQ / debug arbitration.  Bound to rtl/issuer.sv.
//
// See doc/functional_coverage_plan.md section 10.

// Shared trap/control coverage remains active in both hardware report domains,
// including both runtime modes of CHERI-capable hardware.
// CHERI-only coverage requires both hardware support and runtime CHERI mode.

module kudu_fcov_issue
  import super_pkg::*;
  import cheri_pkg::*;
  import csr_pkg::*;
  import kudu_fcov_pkg::*;
(
  input logic        clk_i,
  input logic        rst_ni,

  // --- issue arbitration -----------------------------------------------------
  input logic        ira_is0_i,
  input logic [1:0]  ir_valid_i,
  input logic [1:0]  ir_any_err,
  input logic [1:0]  ir_hazard,
  input logic        ir0_issued,
  input logic        ir1_issued,
  input logic [4:0]  ir0_pl_sel,
  input logic [4:0]  ir1_pl_sel,
  input logic [4:0]  ex_valid_o,
  input logic        ir1_ooo_rdy_event,
  input logic [1:0]  sbdfifo_wr_rdy_i,
  input logic [1:0]  mispredict,
  input logic [1:0]  branch_mispredict_event,

  // --- hazards and forwarding ------------------------------------------------
  input logic [1:0]  ir_raw_hazard,
  input logic [1:0]  ir_waw_hazard,
  input logic [1:0]  ir_cheri_hazard,
  input logic        wr_req_conflict,
  input logic [4:0]  ir0_raw_cause,
  input logic [4:0]  ir1_raw_cause,
  input logic        ir1_raw_by_ir0_event,
  input logic        ir0_stall_nohaz_event,
  input logic        ir1_stall_nohaz_event,
  input logic [31:1] reg_wrsv_q,
  input logic [15:1] reg_cheri_trsv_q,
  input logic [31:0] ir0_pl_fwd_act,
  input logic [31:0] ir1_pl_fwd_act,
  input logic        alupl0_fwd_act_i_any,
  input logic        alupl1_fwd_act_i_any,
  input logic        lspl_fwd_act_i_any,
  input logic        multpl_fwd_act_i_any,

  // --- controller FSM --------------------------------------------------------
  input logic [15:0] ctrl_fsm_cs,
  input logic [15:0] ctrl_fsm_ns,
  input special_case_e special_case_q,
  input logic        handle_err,
  input logic        handle_sysctl,
  input logic        handle_cmplx,
  input logic        handle_irq,
  input logic        handle_debug,
  input logic        cmt_flush_o,
  input logic        cmt_err_i,

  // --- decode context (for the suppression reason and the cross axes) --------
  input ir_dec_t     ir0_dec,
  input ir_dec_t     ir1_dec,
  input logic [1:0]  ir_sysctl,
  input logic [1:0]  ir_cmplx,
  input logic        cheri_pmode_i,

  // --- trap / interrupt / debug ---------------------------------------------
  input exc_info_t   csr_exc_info_o,
  input logic        csr_save_cause_o,
  input logic        debug_csr_save_o,
  input logic        irq_pending_i,
  input logic        csr_mstatus_mie_i,
  input logic [14:0] irq_fast,
  input logic        debug_req_i,
  input logic        debug_mode_q,
  input logic        debug_single_step_i,
  input logic        single_step_trap_q,
  input dbg_cause_e  debug_cause_o,
  input logic        intr_event,
  input logic        ir0_trap_event
);

`ifndef KUDU_FCOV_OFF

  // ==========================================================================
  // Derived sample values
  // ==========================================================================
  ctrl_fsm_e      fsm_cs, fsm_ns;
  logic           fsm_onehot;
  logic [1:0]     issue_pair;
  logic [1:0]     any_err_q;        // ir_any_err masked by ir_valid, see below
  logic [1:0]     hazard_q;
  fcov_suppress_e suppress1;
  logic           slot1_present;
  logic           cheri_active;
  assign cheri_active = issuer.CHERIoTEn && cheri_pmode_i;

  typedef enum logic [0:0] {
    FCOV_IR0, FCOV_IR1
  } fcov_issue_slot_e;

  typedef enum logic [0:0] {
    FCOV_RS1, FCOV_RS2
  } fcov_issue_operand_e;

  typedef enum logic [1:0] {
    FWD_READY, FWD_RESCUED, FWD_RAW_STALL, FWD_SAME_BUNDLE
  } fcov_fwd_outcome_e;

  typedef enum logic [2:0] {
    FWD_SRC_NONE, FWD_SRC_ALU0, FWD_SRC_ALU1, FWD_SRC_LS, FWD_SRC_MULT, FWD_SRC_MULTI
  } fcov_fwd_src_e;

  typedef enum logic [1:0] {
    BP_KIND_BRANCH, BP_KIND_JAL, BP_KIND_JALR
  } fcov_bp_kind_e;

  typedef enum logic [1:0] {
    BP_REC_NONE, BP_REC_PC_SET, BP_REC_ALT_APPLY, BP_REC_ALT_CANCEL_FLUSH
  } fcov_bp_recovery_e;

  assign fsm_cs     = fcov_fsm_dec(ctrl_fsm_cs);
  assign fsm_ns     = fcov_fsm_dec(ctrl_fsm_ns);

  assign issue_pair = {ir1_issued, ir0_issued};

  // ir_any_err and ir_hazard are NOT qualified by ir_valid_i: both are
  // combinational decodes of whatever the IR FIFO happens to present
  // (issuer.sv:719-720, :423-429).  Every *consumer* qualifies -- for example
  // handle_err = ir_valid_i[0] & ir_any_err[0] at :730 -- so the design is
  // correct, but sampling the raw buses fills the invalid-slot bins with noise.
  // Mask here; anyone crossing these with cp_ir_valid should mark the
  // unqualified cells ignore_bins, not illegal_bins: they are meaningless, not
  // erroneous.
  assign any_err_q = ir_any_err & ir_valid_i;
  assign hazard_q  = ir_hazard  & ir_valid_i;

  assign slot1_present = ir_valid_i[1] & ~ir1_issued;

  function automatic fcov_fwd_src_e fcov_fwd_src(logic [4:0] rs);
    logic [3:0] src;
    src = {issuer.multpl_fwd_act_i[rs], issuer.lspl_fwd_act_i[rs],
           issuer.alupl1_fwd_act_i[rs], issuer.alupl0_fwd_act_i[rs]};
    unique case (src)
      4'b0000: return FWD_SRC_NONE;
      4'b0001: return FWD_SRC_ALU0;
      4'b0010: return FWD_SRC_ALU1;
      4'b0100: return FWD_SRC_LS;
      4'b1000: return FWD_SRC_MULT;
      default: return FWD_SRC_MULTI;
    endcase
  endfunction

  function automatic fcov_fwd_outcome_e fcov_operand_outcome(
      fcov_issue_slot_e slot, logic [4:0] rs);
    logic reserved, forwarded, same_bundle;
    reserved = reg_wrsv_q[rs];
    forwarded = (slot == FCOV_IR0) ? ir0_pl_fwd_act[rs] : ir1_pl_fwd_act[rs];
    same_bundle = (slot == FCOV_IR1) && ir_valid_i[0] && ir0_dec.rf_we &&
        (ir0_dec.rd == rs) && (rs != 5'd0);
    if (same_bundle) return FWD_SAME_BUNDLE;
    if (reserved && forwarded) return FWD_RESCUED;
    if (reserved) return FWD_RAW_STALL;
    return FWD_READY;
  endfunction

  function automatic fcov_bp_kind_e fcov_bp_kind(ir_dec_t d);
    if (d.is_jalr) return BP_KIND_JALR;
    if (d.is_jal)  return BP_KIND_JAL;
    return BP_KIND_BRANCH;
  endfunction

  function automatic fcov_bp_recovery_e fcov_recovery_path(fcov_issue_slot_e slot);
    logic slot_cancel;
    slot_cancel = (slot == FCOV_IR0) ? issuer.ex_alt_ctrl_o.cancel[0] :
                                      issuer.ex_alt_ctrl_o.cancel[1];
    if (issuer.ex_alt_ctrl_o.apply) return BP_REC_ALT_APPLY;
    if (slot_cancel || issuer.ex_alt_ctrl_o.flush) return BP_REC_ALT_CANCEL_FLUSH;
    if (issuer.pc_set_o) return BP_REC_PC_SET;
    return BP_REC_NONE;
  endfunction

  covergroup cg_ma_issue_operand with function sample(
      fcov_issue_slot_e slot, fcov_issue_operand_e operand,
      fcov_fwd_outcome_e outcome, fcov_fwd_src_e producer,
      kudu_instr_scat_e consumer_class, logic issued);
    option.per_instance = 1;
    option.name         = "FC_MA_ISSUE.forwarding";

    cp_consumer_slot: coverpoint slot {
      bins ir0 = {FCOV_IR0};
      bins ir1 = {FCOV_IR1};
    }
    cp_operand: coverpoint operand {
      bins rs1 = {FCOV_RS1};
      bins rs2 = {FCOV_RS2};
    }
    cp_operand_outcome: coverpoint outcome {
      bins ready = {FWD_READY};
      bins rescued = {FWD_RESCUED};
      bins raw_stall = {FWD_RAW_STALL};
      bins same_bundle_ir0_to_ir1 = {FWD_SAME_BUNDLE};
    }
    cp_producer: coverpoint producer iff (outcome == FWD_RESCUED) {
      bins alu0 = {FWD_SRC_ALU0};
      bins alu1 = {FWD_SRC_ALU1};
      bins ls = {FWD_SRC_LS};
      bins mult = {FWD_SRC_MULT};
      bins multi = {FWD_SRC_MULTI};
    }
    cp_consumer_class: coverpoint consumer_class {
      bins alu = {SC_ALU};
      bins muldiv = {SC_MULDIV};
      bins ctrl = {SC_CTRL};
      bins mem = {SC_MEM};
      bins atomic = {SC_ATOMIC};
      bins sysreg = {SC_SYSREG};
      bins cheri = {SC_CHERI};
      bins bad = {SC_BAD};
    }
    cp_issued: coverpoint issued {
      bins stalled = {1'b0};
      bins issued = {1'b1};
    }

    x_operand_outcome_issue:
      cross cp_consumer_slot, cp_operand, cp_operand_outcome, cp_issued {
        // fcov_operand_outcome() returns FWD_SAME_BUNDLE only for IR1.
        ignore_bins same_bundle_ir0 = binsof(cp_consumer_slot.ir0) &&
            binsof(cp_operand_outcome.same_bundle_ir0_to_ir1);
      }
    x_fwd_producer_consumer:
      cross cp_producer, cp_consumer_slot, cp_consumer_class;
  endgroup

  covergroup cg_ma_issue_bp_resolution with function sample(
      fcov_issue_slot_e slot, fcov_bp_kind_e kind, logic predicted_taken,
      logic actual_taken, fcov_bp_recovery_e recovery);
    option.per_instance = 1;
    option.name         = "FC_MA_ISSUE.bp_resolution";

    cp_resolution_slot: coverpoint slot {
      bins ir0 = {FCOV_IR0};
      bins ir1 = {FCOV_IR1};
    }
    cp_resolution_kind: coverpoint kind {
      bins branch = {BP_KIND_BRANCH};
      bins jal = {BP_KIND_JAL};
      bins jalr = {BP_KIND_JALR};
    }
    cp_predicted_taken: coverpoint predicted_taken {
      bins not_taken = {1'b0};
      bins taken = {1'b1};
    }
    cp_actual_taken: coverpoint actual_taken {
      bins not_taken = {1'b0};
      bins taken = {1'b1};
    }
    cp_recovery: coverpoint recovery {
      bins none_correct = {BP_REC_NONE};
      bins ordinary_pc_set = {BP_REC_PC_SET};
      bins alt_apply = {BP_REC_ALT_APPLY};
      bins alt_cancel_flush = {BP_REC_ALT_CANCEL_FLUSH};
    }

    x_prediction_resolution_recovery:
      cross cp_resolution_slot, cp_resolution_kind, cp_predicted_taken,
            cp_actual_taken, cp_recovery {
        ignore_bins jal_never_not_taken =
          binsof(cp_resolution_kind) intersect {BP_KIND_JAL, BP_KIND_JALR} &&
          binsof(cp_actual_taken.not_taken);
      }
  endgroup

  covergroup cg_ma_issue_cheri_dep with function sample(
      fcov_issue_slot_e slot, logic blocked, logic issued);
    option.per_instance = 1;
    option.name         = "FC_MA_ISSUE.cheri_temporal";
    option.weight       = issuer.CHERIoTEn ? 1 : 0;

    cp_cheri_slot: coverpoint slot {
      bins ir0 = {FCOV_IR0};
      bins ir1 = {FCOV_IR1};
    }
    cp_cheri_temporal_outcome: coverpoint blocked {
      bins clear = {1'b0};
      bins temporal_stall = {1'b1};
    }
    cp_cheri_temporal_issued: coverpoint issued {
      bins stalled = {1'b0};
      bins issued = {1'b1};
    }
    x_cheri_temporal_issue:
      cross cp_cheri_slot, cp_cheri_temporal_outcome, cp_cheri_temporal_issued
      iff (cheri_active && issuer.LoadFiltEn) {
        option.weight = (issuer.CHERIoTEn && issuer.LoadFiltEn) ? 1 : 0;
      }
  endgroup

  typedef enum logic [1:0] {
    RA_EQUAL, RA_PRED_MORE, RA_PRED_LESS, RA_OTHER
  } ra_relation_e;

  function automatic ra_relation_e compare_ra(full_cap_t predicted, full_cap_t actual);
    if (predicted.addr != actual.addr || predicted.valid != actual.valid ||
        predicted.otype != actual.otype || predicted.rsvd != actual.rsvd)
      return RA_OTHER;
    if (predicted.base32 == actual.base32 && predicted.top33 == actual.top33 &&
        predicted.perms == actual.perms)
      return RA_EQUAL;
    if (!predicted.valid || {1'b0, predicted.base32} > predicted.top33 ||
        {1'b0, actual.base32} > actual.top33)
      return RA_OTHER;
    if (predicted.base32 <= actual.base32 && predicted.top33 >= actual.top33 &&
        (predicted.perms & actual.perms) == actual.perms)
      return RA_PRED_MORE;
    if (predicted.base32 >= actual.base32 && predicted.top33 <= actual.top33 &&
        (predicted.perms & actual.perms) == predicted.perms)
      return RA_PRED_LESS;
    return RA_OTHER;
  endfunction

  logic ra_update_start, ra_update_pending, ra_update_sample, ra_consumer_matches;
  logic [31:0] ra_consumer_pc_q, ra_consumer_insn_q;
  reg_cap_t predicted_ra_q;
  full_cap_t predicted_ra, actual_ra;
  ra_relation_e ra_relation;

  // Save the younger prediction before IR0 issues and the JALR becomes IR0.
  assign ra_update_start = issuer.cheri_pmode && ctrl_fsm_cs[CSM_DECODE] &&
      (&ir_valid_i) && ir0_issued && ir0_dec.rf_we && ir0_dec.rd == 5'd1 &&
      ir1_dec.is_jalr && ir1_dec.rs1 == 5'd1 && ir1_dec.rf_ren[0] &&
      ir1_dec.ptaken && ir_raw_hazard[1] && !ir1_issued &&
      !cmt_err_i && !issuer.ir_flush_o;
  assign ra_consumer_matches = ir_valid_i[0] && ir0_dec.is_jalr &&
      ir0_dec.rs1 == 5'd1 && ir0_dec.rf_ren[0] &&
      ir0_dec.pc == ra_consumer_pc_q && ir0_dec.insn == ra_consumer_insn_q;
  assign ra_update_sample = ra_update_pending && issuer.cheri_pmode &&
      ctrl_fsm_cs[CSM_DECODE] && !cmt_err_i && !cmt_flush_o &&
      ra_consumer_matches && !ir_hazard[0];
  assign predicted_ra = op2fullcap(reg2opcap(predicted_ra_q));
  assign actual_ra = full_cap_t'(issuer.ira_is0_i ?
      issuer.ira_full_data2_fwd_o.d0 : issuer.irb_full_data2_fwd_o.d0);
  assign ra_relation = compare_ra(predicted_ra, actual_ra);

  cg_ma_issue_operand u_cg_ma_issue_operand = new();
  cg_ma_issue_bp_resolution u_cg_ma_issue_bp_resolution = new();
  cg_ma_issue_cheri_dep u_cg_ma_issue_cheri_dep = new();

  always_ff @(posedge clk_i) begin
    if (rst_ni) begin
      if (ir_valid_i[0] && ir0_dec.rf_ren[0] && (ir0_dec.rs1 != 5'd0)) begin
        u_cg_ma_issue_operand.sample(
            FCOV_IR0, FCOV_RS1, fcov_operand_outcome(FCOV_IR0, ir0_dec.rs1),
            fcov_fwd_src(ir0_dec.rs1), fcov_instr_scat(fcov_instr_cat(ir0_dec)),
            ir0_issued);
      end
      if (ir_valid_i[0] && ir0_dec.rf_ren[1] && (ir0_dec.rs2 != 5'd0)) begin
        u_cg_ma_issue_operand.sample(
            FCOV_IR0, FCOV_RS2, fcov_operand_outcome(FCOV_IR0, ir0_dec.rs2),
            fcov_fwd_src(ir0_dec.rs2), fcov_instr_scat(fcov_instr_cat(ir0_dec)),
            ir0_issued);
      end
      if (ir_valid_i[1] && ir1_dec.rf_ren[0] && (ir1_dec.rs1 != 5'd0)) begin
        u_cg_ma_issue_operand.sample(
            FCOV_IR1, FCOV_RS1, fcov_operand_outcome(FCOV_IR1, ir1_dec.rs1),
            fcov_fwd_src(ir1_dec.rs1), fcov_instr_scat(fcov_instr_cat(ir1_dec)),
            ir1_issued);
      end
      if (ir_valid_i[1] && ir1_dec.rf_ren[1] && (ir1_dec.rs2 != 5'd0)) begin
        u_cg_ma_issue_operand.sample(
            FCOV_IR1, FCOV_RS2, fcov_operand_outcome(FCOV_IR1, ir1_dec.rs2),
            fcov_fwd_src(ir1_dec.rs2), fcov_instr_scat(fcov_instr_cat(ir1_dec)),
            ir1_issued);
      end

      if (ir0_issued && (ir0_dec.is_branch || ir0_dec.is_jal || ir0_dec.is_jalr)) begin
        u_cg_ma_issue_bp_resolution.sample(
            FCOV_IR0, fcov_bp_kind(ir0_dec), ir0_dec.ptaken,
            ir0_dec.is_branch ? issuer.branch_info_i.branch_taken[0] : 1'b1,
            fcov_recovery_path(FCOV_IR0));
      end
      if (ir1_issued && (ir1_dec.is_branch || ir1_dec.is_jal || ir1_dec.is_jalr)) begin
        u_cg_ma_issue_bp_resolution.sample(
            FCOV_IR1, fcov_bp_kind(ir1_dec), ir1_dec.ptaken,
            ir1_dec.is_branch ? issuer.branch_info_i.branch_taken[1] : 1'b1,
            fcov_recovery_path(FCOV_IR1));
      end

      if (cheri_active && issuer.LoadFiltEn && ir_valid_i[0] && ir0_dec.is_cheri) begin
        u_cg_ma_issue_cheri_dep.sample(FCOV_IR0, ir_cheri_hazard[0], ir0_issued);
      end
      if (cheri_active && issuer.LoadFiltEn && ir_valid_i[1] && ir1_dec.is_cheri) begin
        u_cg_ma_issue_cheri_dep.sample(FCOV_IR1, ir_cheri_hazard[1], ir1_issued);
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ra_update_pending <= 1'b0;
      ra_consumer_pc_q <= '0;
      ra_consumer_insn_q <= '0;
      predicted_ra_q <= NULL_REG_CAP;
    end else begin
      // A resolving JALR may itself redirect; sample before clearing the tracker.
      if (ra_update_sample || issuer.ir_flush_o || cmt_flush_o || cmt_err_i ||
          !issuer.cheri_pmode || (ir_valid_i[0] && !ra_consumer_matches))
        ra_update_pending <= 1'b0;
      if (ra_update_start) begin
        ra_update_pending <= 1'b1;
        ra_consumer_pc_q <= ir1_dec.pc;
        ra_consumer_insn_q <= ir1_dec.insn;
        predicted_ra_q <= reg_cap_t'(ir1_dec.ptarget);
      end
    end
  end

  // Why slot 1 did not issue.  Priority mirrors normal_ex_enable[1]
  // (issuer.sv:740-744).  Note SUP_IR0_NOT_ISSUED is a first-class reason
  // rather than an error: issue is strictly in order, so ir1 can never issue
  // without ir0 (see cp_issue_result).
  always_comb begin
    if (!slot1_present)                          suppress1 = SUP_NONE;
    else if (!ir0_issued)                        suppress1 = SUP_IR0_NOT_ISSUED;
    else if (ir_hazard[1])                       suppress1 = SUP_HAZARD;
    else if (ir_any_err[1])                      suppress1 = SUP_ANY_ERR;
    else if (ir_sysctl[1])                       suppress1 = SUP_SYSCTL;
    else if (ir_cmplx[1])                        suppress1 = SUP_CMPLX;
    else if (ir1_dec.is_brkpt)                   suppress1 = SUP_BRKPT;
    else if (debug_single_step_i)                suppress1 = SUP_SINGLE_STEP;
    else if (cheri_pmode_i & ir0_dec.is_jalr)    suppress1 = SUP_CJALR_SERIALISE;
    else if (mispredict[0])                      suppress1 = SUP_MISPREDICT0;
    else                                         suppress1 = SUP_NONE;
  end

  // ==========================================================================
  // 10.1 Issue arbitration
  // ==========================================================================
  // ==========================================================================
  // 10.4 Trap, interrupt and debug arbitration
  // ==========================================================================
  // The RTL's mfip_id is an automatic variable inside an always_comb block
  // (issuer.sv:917), so it is not reachable from a bind.  Recomputed here with
  // the same priority: the loop runs 14 down to 0 and assigns on every set bit,
  // so the *lowest* set index wins.
  logic [3:0] mfip_id;
  always_comb begin
    mfip_id = 4'd15;                       // 15 == no fast interrupt pending
    for (int i = 14; i >= 0; i--) begin
      if (irq_fast[i]) mfip_id = i[3:0];
    end
  end

  // Observed debug-request pulse width.  Measured on the pin, like the bus
  // delays, rather than read back from whatever the driver was configured to
  // do: a knob proves the knob was set, counted cycles prove the core saw it.
  int unsigned dbg_req_len;
  logic        dbg_req_q, dbg_req_fell;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dbg_req_len  <= 0;
      dbg_req_q    <= 1'b0;
      dbg_req_fell <= 1'b0;
    end else begin
      dbg_req_q    <= debug_req_i;
      dbg_req_fell <= dbg_req_q & ~debug_req_i;
      if (debug_req_i) dbg_req_len <= dbg_req_q ? (dbg_req_len + 1) : 1;
    end
  end

  // ==========================================================================
  // FC_MA_ISSUE - issue stage and control FSM
  // ==========================================================================
  covergroup cg_ma_issue @(posedge clk_i iff rst_ni);
    option.per_instance = 1;
    option.name         = "FC_MA_ISSUE";

    cp_ira_is0: coverpoint ira_is0_i {
      bins irb_is_ir0 = {1'b0};
      bins ira_is_ir0 = {1'b1};
    }

    // ir_valid_i == 2'b10 is illegal: slot 1 valid without slot 0.  Already
    // asserted in RTL by AssertRdOutputLegal in *both* FIFO variants
    // (stage_fifo.sv:240, dual_fifo.sv:208).  This is a second, independent
    // check -- an assertion that is compiled out leaves no trace, a coverage
    // illegal_bin does not.
    cp_ir_valid: coverpoint ir_valid_i {
      bins none    = {2'b00};
      bins ir0     = {2'b01};
      bins dual    = {2'b11};
      illegal_bins slot1_only = {2'b10};
    }

    cp_any_err: coverpoint any_err_q {
      bins none   = {2'b00};
      bins ir0    = {2'b01};
      bins ir1    = {2'b10};   // younger-only error: must defer, not trap
      bins both   = {2'b11};
    }

    // The whole answer to "ir0 stalled by a hazard but ir1 not" is this one
    // coverpoint.  All four values are reachable and meaningful.
    cp_hazard: coverpoint hazard_q {
      bins none = {2'b00};
      bins ir0  = {2'b01};
      bins ir1  = {2'b10};
      bins both = {2'b11};
    }

    // Issue is strictly in order: pl_sel_enable[1] is gated on
    // ir0_normal_issued (issuer.sv:304), which is gated on ~ir_hazard[0]
    // (:312, :736-737).  So ir1_issued implies ir0_issued and the 2'b10 cell
    // cannot occur.  A hit means the issue-enable chain is broken.
    cp_issue_result: coverpoint issue_pair {
      bins none    = {2'b00};
      bins ir0only = {2'b01};
      bins dual    = {2'b11};
      illegal_bins ir1_only = {2'b10};
    }

    // pl_sel is NOT one-hot.  Bit 0 selects the branch unit and bits 4:1 are a
    // one-hot execution-pipeline select; is_issued() splits them exactly that
    // way (issuer.sv:221-222).  select_pl (issuer.sv:133-158) pairs the branch
    // unit with an execution pipe for every jump, so 5'h03, 5'h05 and 5'h11 are
    // normal encodings, not errors.  The only structural invariant is that bits
    // 4:1 are one-hot-zero.  The values select_pl cannot produce are listed
    // explicitly instead of using 'default' so that X samples match no bin.
    cp_pl_sel_ir0: coverpoint ir0_pl_sel {
      bins idle       = {5'h00};
      bins local_     = {5'h01};   // branch unit alone (PL_LOCAL)
      bins alu0       = {5'h02};
      bins alu1       = {5'h04};
      bins ls         = {5'h08};
      bins mult       = {5'h10};
      bins jump_alu0  = {5'h03};   // JAL/JALR on ira: branch unit + alu0
      bins jump_alu1  = {5'h05};   // JAL/JALR on irb: branch unit + alu1
      bins cjalr_mult = {5'h11} iff (cheri_active); // CHERIoT CJALR: branch + mult
      illegal_bins bad = {[5'h06:5'h07], [5'h09:5'h0f], [5'h12:5'h1f]};
    }

    cp_pl_sel_ir1: coverpoint ir1_pl_sel {
      bins idle       = {5'h00};
      bins local_     = {5'h01};
      bins alu0       = {5'h02};
      bins alu1       = {5'h04};
      bins ls         = {5'h08};
      bins mult       = {5'h10};
      bins jump_alu0  = {5'h03};
      bins jump_alu1  = {5'h05};
      bins cjalr_mult = {5'h11} iff (cheri_active);
      illegal_bins bad = {[5'h06:5'h07], [5'h09:5'h0f], [5'h12:5'h1f]};
    }

    cp_ex_valid: coverpoint $countones(ex_valid_o) {
      bins zero = {0};
      bins one  = {1};
      bins two  = {2};
      bins three  = {3};
      illegal_bins too_many = {[4:5]};   // at most two instructions issue
    }

    // NOT an out-of-order issue -- the design has none.  ir1_pl_sel_enable_ooo
    // deliberately omits ir0_normal_issued (issuer.sv:1085) and ir1_pl_sel_ooo
    // passes ira_is0_i where the real ir1_pl_sel passes ~ira_is0_i (:1086 vs
    // :306).  This counts dual-issue slots *lost* to the in-order rule, so it
    // is a throughput coverpoint.  The RTL name is misleading (finding F-10).
    cp_ir1_ooo_lost: coverpoint ir1_ooo_rdy_event {
      bins lost = {1'b1};
    }

    cp_suppress1: coverpoint suppress1
        iff (slot1_present && (cheri_active || suppress1 != SUP_CJALR_SERIALISE));

    cp_sbd_full: coverpoint sbdfifo_wr_rdy_i {
      bins both_rdy = {2'b11};
      bins one_rdy  = {2'b01};
      bins none_rdy = {2'b00};
      illegal_bins slot1_only = {2'b10};
    }

    // ======================================================================
    // 10.2 Hazards and forwarding
    // ======================================================================
    cp_raw_hazard:   coverpoint (ir_raw_hazard   & ir_valid_i) { bins v[] = {[0:3]}; }
    cp_waw_hazard:   coverpoint (ir_waw_hazard   & ir_valid_i) { bins v[] = {[0:3]}; }
    cp_cheri_hazard: coverpoint (ir_cheri_hazard & ir_valid_i) iff (cheri_active) {
      option.weight = issuer.CHERIoTEn ? 1 : 0;
      bins v[] = {[0:3]};
    }

    // ir_waw_hazard[1] carries an extra "| wr_req_conflict" term that slot 0
    // does not (issuer.sv:424-426): two instructions in one bundle targeting
    // the same rd.  It is a slot-1-only condition with no slot-0 counterpart,
    // so this is the only place it is observable.
    cp_wr_req_conflict: coverpoint wr_req_conflict { bins hit = {1'b1}; }

    // ir0_raw_cause / ir1_raw_cause are NOT register indices.  reg_wrsv_cause[]
    // stores the *pl_sel of the producing instruction* (issuer.sv:1108-1121),
    // and the cause is the bitwise OR of the entries for rs1 and rs2
    // (issuer.sv:1126-1127 and 1134-1135), so it is a mask of the pipelines a
    // consumer is waiting on, not a single encoding.  When both sources are
    // reserved by different pipelines the result is multi-hot (alu0 + alu1 gives
    // 5'h06), which is why nothing here can be an illegal bin: the one-hot-zero
    // invariant belongs on cp_pl_sel_ir0/ir1, where the value is produced.
    //
    // Each of bits 4:1 is therefore binned both set and clear: what matters is
    // whether a given pipeline is holding the consumer up, independently of the
    // others.  The bins overlap by construction — one sample increments the set
    // bin of every pipeline in the mask and the clear bin of every pipeline that
    // is not.  All four clear is the "no producer recorded yet" case, reachable
    // on slot 1 because ir1_raw_st adds the combinational ir0_reg_wr_req term
    // (issuer.sv:415-416): the same-bundle RaW from slot 0 is visible a cycle
    // before reg_wrsv_cause[] latches that producer's pl_sel.  Bit 0 (branch
    // unit) is left to cp_pl_sel_ir0/ir1; it never gates a RaW hazard on its own.
    cp_raw_cause_ir0: coverpoint ir0_raw_cause iff (ir_raw_hazard[0] & ir_valid_i[0]) {
      wildcard bins alu0_set = {5'b???1?};
      wildcard bins alu0_clr = {5'b???0?};
      wildcard bins alu1_set = {5'b??1??};
      wildcard bins alu1_clr = {5'b??0??};
      wildcard bins ls_set   = {5'b?1???};
      wildcard bins ls_clr   = {5'b?0???};
      wildcard bins mult_set = {5'b1????};
      wildcard bins mult_clr = {5'b0????};
    }
    cp_raw_cause_ir1: coverpoint ir1_raw_cause iff (ir_raw_hazard[1] & ir_valid_i[1]) {
      wildcard bins alu0_set = {5'b???1?};
      wildcard bins alu0_clr = {5'b???0?};
      wildcard bins alu1_set = {5'b??1??};
      wildcard bins alu1_clr = {5'b??0??};
      wildcard bins ls_set   = {5'b?1???};
      wildcard bins ls_clr   = {5'b?0???};
      wildcard bins mult_set = {5'b1????};
      wildcard bins mult_clr = {5'b0????};
    }

    cp_ir1_raw_by_ir0: coverpoint ir1_raw_by_ir0_event { bins hit = {1'b1}; }
    cp_ra_update_jalr: coverpoint ra_relation iff (ra_update_sample) {
      option.weight = issuer.CHERIoTEn ? 1 : 0;
      bins actual_equals_predicted = {RA_EQUAL};
      bins predicted_more_permissive = {RA_PRED_MORE};
      bins predicted_less_permissive = {RA_PRED_LESS};
      bins other = {RA_OTHER};
    }
    cp_stall_nohaz0:   coverpoint ir0_stall_nohaz_event { bins hit = {1'b1}; }
    cp_stall_nohaz1:   coverpoint ir1_stall_nohaz_event { bins hit = {1'b1}; }

    // Overlapping wildcard bins count every set register bit in a multi-hot mask.
    // Pad bit zero so wildcard positions retain the RTL's register numbering.
    cp_reg_wrsv_q: coverpoint {reg_wrsv_q, 1'b0} {
      wildcard bins r1  = {32'b????_????_????_????_????_????_????_??1?};
      wildcard bins r2  = {32'b????_????_????_????_????_????_????_?1??};
      wildcard bins r3  = {32'b????_????_????_????_????_????_????_1???};
      wildcard bins r4  = {32'b????_????_????_????_????_????_???1_????};
      wildcard bins r5  = {32'b????_????_????_????_????_????_??1?_????};
      wildcard bins r6  = {32'b????_????_????_????_????_????_?1??_????};
      wildcard bins r7  = {32'b????_????_????_????_????_????_1???_????};
      wildcard bins r8  = {32'b????_????_????_????_????_???1_????_????};
      wildcard bins r9  = {32'b????_????_????_????_????_??1?_????_????};
      wildcard bins r10 = {32'b????_????_????_????_????_?1??_????_????};
      wildcard bins r11 = {32'b????_????_????_????_????_1???_????_????};
      wildcard bins r12 = {32'b????_????_????_????_???1_????_????_????};
      wildcard bins r13 = {32'b????_????_????_????_??1?_????_????_????};
      wildcard bins r14 = {32'b????_????_????_????_?1??_????_????_????};
      wildcard bins r15 = {32'b????_????_????_????_1???_????_????_????};
      wildcard bins r16 = {32'b????_????_????_???1_????_????_????_????};
      wildcard bins r17 = {32'b????_????_????_??1?_????_????_????_????};
      wildcard bins r18 = {32'b????_????_????_?1??_????_????_????_????};
      wildcard bins r19 = {32'b????_????_????_1???_????_????_????_????};
      wildcard bins r20 = {32'b????_????_???1_????_????_????_????_????};
      wildcard bins r21 = {32'b????_????_??1?_????_????_????_????_????};
      wildcard bins r22 = {32'b????_????_?1??_????_????_????_????_????};
      wildcard bins r23 = {32'b????_????_1???_????_????_????_????_????};
      wildcard bins r24 = {32'b????_???1_????_????_????_????_????_????};
      wildcard bins r25 = {32'b????_??1?_????_????_????_????_????_????};
      wildcard bins r26 = {32'b????_?1??_????_????_????_????_????_????};
      wildcard bins r27 = {32'b????_1???_????_????_????_????_????_????};
      wildcard bins r28 = {32'b???1_????_????_????_????_????_????_????};
      wildcard bins r29 = {32'b??1?_????_????_????_????_????_????_????};
      wildcard bins r30 = {32'b?1??_????_????_????_????_????_????_????};
      wildcard bins r31 = {32'b1???_????_????_????_????_????_????_????};
    }
    cp_reg_cheri_trsv_q: coverpoint {16'b0, reg_cheri_trsv_q, 1'b0}
        iff (cheri_active && issuer.LoadFiltEn) {
      option.weight = (issuer.CHERIoTEn && issuer.LoadFiltEn) ? 1 : 0;
      wildcard bins r1  = {32'b????_????_????_????_????_????_????_??1?};
      wildcard bins r2  = {32'b????_????_????_????_????_????_????_?1??};
      wildcard bins r3  = {32'b????_????_????_????_????_????_????_1???};
      wildcard bins r4  = {32'b????_????_????_????_????_????_???1_????};
      wildcard bins r5  = {32'b????_????_????_????_????_????_??1?_????};
      wildcard bins r6  = {32'b????_????_????_????_????_????_?1??_????};
      wildcard bins r7  = {32'b????_????_????_????_????_????_1???_????};
      wildcard bins r8  = {32'b????_????_????_????_????_???1_????_????};
      wildcard bins r9  = {32'b????_????_????_????_????_??1?_????_????};
      wildcard bins r10 = {32'b????_????_????_????_????_?1??_????_????};
      wildcard bins r11 = {32'b????_????_????_????_????_1???_????_????};
      wildcard bins r12 = {32'b????_????_????_????_???1_????_????_????};
      wildcard bins r13 = {32'b????_????_????_????_??1?_????_????_????};
      wildcard bins r14 = {32'b????_????_????_????_?1??_????_????_????};
      wildcard bins r15 = {32'b????_????_????_????_1???_????_????_????};
    }
    x_cp_reg_wrsv_q: cross cp_hazard, cp_reg_wrsv_q;
    x_cp_reg_cheri_trsv_q: cross cp_hazard, cp_reg_cheri_trsv_q
        iff (cheri_active && issuer.LoadFiltEn) {
      option.weight = (issuer.CHERIoTEn && issuer.LoadFiltEn) ? 1 : 0;
    }

    // Pair order is {forwarding active, write reserved}, including all four states.
    cp_fwd_wrsv_r1: coverpoint {ir0_pl_fwd_act[1], reg_wrsv_q[1]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r2: coverpoint {ir0_pl_fwd_act[2], reg_wrsv_q[2]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r3: coverpoint {ir0_pl_fwd_act[3], reg_wrsv_q[3]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r4: coverpoint {ir0_pl_fwd_act[4], reg_wrsv_q[4]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r5: coverpoint {ir0_pl_fwd_act[5], reg_wrsv_q[5]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r6: coverpoint {ir0_pl_fwd_act[6], reg_wrsv_q[6]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r7: coverpoint {ir0_pl_fwd_act[7], reg_wrsv_q[7]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r8: coverpoint {ir0_pl_fwd_act[8], reg_wrsv_q[8]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r9: coverpoint {ir0_pl_fwd_act[9], reg_wrsv_q[9]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r10: coverpoint {ir0_pl_fwd_act[10], reg_wrsv_q[10]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r11: coverpoint {ir0_pl_fwd_act[11], reg_wrsv_q[11]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r12: coverpoint {ir0_pl_fwd_act[12], reg_wrsv_q[12]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r13: coverpoint {ir0_pl_fwd_act[13], reg_wrsv_q[13]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r14: coverpoint {ir0_pl_fwd_act[14], reg_wrsv_q[14]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r15: coverpoint {ir0_pl_fwd_act[15], reg_wrsv_q[15]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r16: coverpoint {ir0_pl_fwd_act[16], reg_wrsv_q[16]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r17: coverpoint {ir0_pl_fwd_act[17], reg_wrsv_q[17]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r18: coverpoint {ir0_pl_fwd_act[18], reg_wrsv_q[18]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r19: coverpoint {ir0_pl_fwd_act[19], reg_wrsv_q[19]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r20: coverpoint {ir0_pl_fwd_act[20], reg_wrsv_q[20]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r21: coverpoint {ir0_pl_fwd_act[21], reg_wrsv_q[21]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r22: coverpoint {ir0_pl_fwd_act[22], reg_wrsv_q[22]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r23: coverpoint {ir0_pl_fwd_act[23], reg_wrsv_q[23]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r24: coverpoint {ir0_pl_fwd_act[24], reg_wrsv_q[24]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r25: coverpoint {ir0_pl_fwd_act[25], reg_wrsv_q[25]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r26: coverpoint {ir0_pl_fwd_act[26], reg_wrsv_q[26]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r27: coverpoint {ir0_pl_fwd_act[27], reg_wrsv_q[27]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r28: coverpoint {ir0_pl_fwd_act[28], reg_wrsv_q[28]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r29: coverpoint {ir0_pl_fwd_act[29], reg_wrsv_q[29]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r30: coverpoint {ir0_pl_fwd_act[30], reg_wrsv_q[30]} {
      bins pair[] = {[0:3]};
    }
    cp_fwd_wrsv_r31: coverpoint {ir0_pl_fwd_act[31], reg_wrsv_q[31]} {
      bins pair[] = {[0:3]};
    }

    cp_fwd_source: coverpoint {multpl_fwd_act_i_any, lspl_fwd_act_i_any,
                               alupl1_fwd_act_i_any, alupl0_fwd_act_i_any} {
      bins none  = {4'b0000};
      bins alu0  = {4'b0001};
      bins alu1  = {4'b0010};
      bins ls    = {4'b0100};
      bins mult  = {4'b1000};
      bins multi = {[0:15]} with ($countones(item) > 1);
    }

    cp_fwd_to_slot: coverpoint {|ir1_pl_fwd_act, |ir0_pl_fwd_act} {
      bins none = {2'b00};
      bins ir0  = {2'b01};
      bins ir1  = {2'b10};
      bins both = {2'b11};
    }

    // ======================================================================
    // 10.3 Controller FSM and special cases
    // ======================================================================

    // Sampled as a raw 4-bit value: an enum coverpoint only accepts enum
    // members in its bins, and the unused encodings are not enum members.
    cp_fsm_state: coverpoint 4'(fsm_cs) {
      bins reset         = {CSM_RESET};
      bins boot_set      = {CSM_BOOT_SET};
      bins decode        = {CSM_DECODE};
      bins cmt_flush     = {CSM_CMT_FLUSH};
      bins wait_trvk     = {CSM_WAIT_TRVK};
      bins wait_cmt0     = {CSM_WAIT_CMT0};
      bins issue_special = {CSM_ISSUE_SPECIAL};
      bins wait_final    = {CSM_WAIT_FINAL};
      bins wait_cmplx    = {CSM_WAIT_CMPLX};
      bins sleep         = {CSM_SLEEP};
      // 4'h5, 4'h7 and 4'hc-4'hf are not states.  Listed explicitly instead of
      // using 'default' so that X samples match no bin.
      illegal_bins unused = {4'h5, 4'h7, [4'hc:4'hf]};
    }

    cp_fsm_trans: coverpoint fsm_cs {
      bins t_reset_boot   = (CSM_RESET         => CSM_BOOT_SET);
      bins t_boot_decode  = (CSM_BOOT_SET      => CSM_DECODE);
      bins t_dec_flush    = (CSM_DECODE        => CSM_CMT_FLUSH);
      bins t_dec_cmt0     = (CSM_DECODE        => CSM_WAIT_CMT0);
      bins t_flush_trvk   = (CSM_CMT_FLUSH     => CSM_WAIT_TRVK);
      bins t_trvk_dec     = (CSM_WAIT_TRVK     => CSM_DECODE);
      bins t_cmt0_flush   = (CSM_WAIT_CMT0     => CSM_CMT_FLUSH);
      bins t_cmt0_special = (CSM_WAIT_CMT0     => CSM_ISSUE_SPECIAL);
      bins t_special_cplx = (CSM_ISSUE_SPECIAL => CSM_WAIT_CMPLX);
      bins t_special_fin  = (CSM_ISSUE_SPECIAL => CSM_WAIT_FINAL);
      bins t_cmplx_dec    = (CSM_WAIT_CMPLX    => CSM_DECODE);
      bins t_fin_dec      = (CSM_WAIT_FINAL    => CSM_DECODE);
      bins t_sleep_in     = (CSM_WAIT_FINAL    => CSM_SLEEP),
                            (CSM_DECODE        => CSM_SLEEP);
      bins t_sleep_out    = (CSM_SLEEP         => CSM_DECODE),
                            (CSM_SLEEP         => CSM_WAIT_CMT0);
    }

    cp_special_case: coverpoint special_case_q iff (ctrl_fsm_cs[CSM_ISSUE_SPECIAL]) {
      bins exec   = {EXEC};
      bins sysctl = {SYSCTL};
      bins cmplx  = {CMPLX};
      bins irq    = {IRQ};
      bins debug  = {DEBUG};
    }

    // handle_* are five separately-computed conditions (issuer.sv:726-731) that
    // arbitrate into one special case.  Covering only the resulting
    // special_case_q loses which condition produced it when more than one is
    // asserted, which is exactly the interesting situation.
    cp_special_source: coverpoint {handle_debug, handle_irq, handle_cmplx,
                                   handle_sysctl, handle_err} {
      bins none     = {5'b00000};
      bins err      = {5'b00001};
      bins sysctl   = {5'b00010};
      bins cmplx    = {5'b00100};
      bins irq      = {5'b01000};
      bins debug    = {5'b10000};
      bins multiple = {[0:31]} with ($countones(item) > 1);
    }

    cp_cmt_flush:  coverpoint cmt_flush_o { bins hit = {1'b1}; }
    cp_cmt_err:    coverpoint cmt_err_i   { bins hit = {1'b1}; }
    cp_mispredict: coverpoint mispredict  { bins v[] = {[0:3]}; }
    cp_branch_mispredict_event: coverpoint branch_mispredict_event {
      wildcard bins ir0 = {2'b?1};
      wildcard bins ir1 = {2'b1?};
    }
    cp_slot1_suppressed_by_mispredict0: coverpoint
        (ir_valid_i[1] && ir0_issued && !ir1_issued && mispredict[0]) {
      bins hit = {1'b1};
    }

    cp_handle_irq: coverpoint handle_irq { bins hit = {1'b1}; }

    x_cp_irq_valid: cross cp_handle_irq, cp_ir_valid;

    cp_irq_masked: coverpoint (irq_pending_i & ~csr_mstatus_mie_i) {
      bins masked = {1'b1};
    }

    // irq_fast_i is [14:0], so a fast-interrupt id only ever spans 0..14 and
    // the generated cause tops out at 6'd62.  mfip_id is a don't-care when the
    // pending interrupt is software / timer / external, hence the bin rather
    // than an illegal_bin.  There is no NMI in this design (WV-05).
    cp_mfip_id: coverpoint mfip_id iff (irq_pending_i) {
      bins id[] = {[0:14]};
      bins not_fast = {4'd15};
    }

    cp_intr_event:      coverpoint intr_event     { bins hit = {1'b1}; }
    cp_ir0_trap_event:  coverpoint ir0_trap_event { bins hit = {1'b1}; }

    // Debug entry asserts save_cause too, but does not write mcause.
    cp_mcause: coverpoint csr_exc_info_o.mcause
        iff (csr_save_cause_o && !debug_csr_save_o) {
      bins instr_access = {EXC_CAUSE_INSTR_ACCESS_FAULT};
      bins illegal_insn = {EXC_CAUSE_ILLEGAL_INSN};
      bins cheri_fault = {EXC_CAUSE_CHERI_FAULT} iff (cheri_active);
      bins breakpoint = {EXC_CAUSE_BREAKPOINT};
      bins ecall_u = {EXC_CAUSE_ECALL_UMODE};
      bins ecall_m = {EXC_CAUSE_ECALL_MMODE};
      bins irq_software = {EXC_CAUSE_IRQ_SOFTWARE_M};
      bins irq_timer = {EXC_CAUSE_IRQ_TIMER_M};
      bins irq_external = {EXC_CAUSE_IRQ_EXTERNAL_M};
      bins irq_fast[] = {[6'h30:6'h3e]};
      // CMT_FLUSH forwards cmt_err_info_i, including these LSU causes.
      bins load_misalign = {EXC_CAUSE_LOAD_ADDR_MISALIGN};
      bins store_misalign = {EXC_CAUSE_STORE_ADDR_MISALIGN};
      bins load_fault = {EXC_CAUSE_LOAD_ACCESS_FAULT};
      bins other = default;
    }

    cp_handle_debug: coverpoint handle_debug { bins hit = {1'b1}; }
    cp_debug_mode:   coverpoint debug_mode_q { bins in_debug = {1'b1}; }

    cp_dbg_entry_src: coverpoint {single_step_trap_q, ir0_dec.is_brkpt, debug_req_i}
                      iff (handle_debug) {
      bins req      = {3'b001};
      bins ebreak   = {3'b010};
      bins step     = {3'b100};
      bins multiple = {[0:7]} with ($countones(item) > 1);
    }

    // debug_cause_o is only driven while the control FSM is issuing the debug
    // special case (issuer.sv:940-952); handle_debug is the request that leads
    // to that state, so sampling on it reads the default DBG_CAUSE_NONE.
    //
    // debug_cause_o misreports a HALTREQ that arrives while dcsr.step is set as
    // DBG_CAUSE_STEP (issuer.sv:945-952).  Needs a spec-conformance ruling
    // (finding F-06); until then all four values are covered, not waived.
    // DBG_CAUSE_NONE is reachable rather than illegal: entry is latched from
    // handle_debug, so a halt request that has already deasserted by the time
    // the FSM issues the special case leaves every cause term low. It is
    // tracked in its own bin instead of aborting the simulation.
    cp_dbg_cause_sel: coverpoint debug_cause_o
                      iff (ctrl_fsm_cs[CSM_ISSUE_SPECIAL] & (special_case_q == DEBUG)) {
      bins ebreak  = {DBG_CAUSE_EBREAK};
      bins trigger = {DBG_CAUSE_TRIGGER};
      bins haltreq = {DBG_CAUSE_HALTREQ};
      bins step    = {DBG_CAUSE_STEP};
      bins none    = {DBG_CAUSE_NONE};
    }

    cp_single_step: coverpoint debug_single_step_i { bins hit = {1'b1}; }

    cp_dbg_req_hold: coverpoint dbg_req_len iff (dbg_req_fell) {
      bins one   = {1};
      bins two   = {2};
      bins three = {3};
      bins more  = {[4:$]};
    }

    cp_sleep_entry: coverpoint ((fsm_ns == CSM_SLEEP) && (fsm_cs != CSM_SLEEP)) {
      bins entered = {1'b1};
    }

    // Tripwire for finding F-02.  The wake condition at issuer.sv:597-600 does
    // not include debug_req_i, so a debugger cannot halt a core sitting in WFI.
    // The bin is kept rather than waived: if it ever fills, the RTL was fixed
    // and this comment should go.
    cp_sleep_wake: coverpoint {debug_req_i, irq_pending_i}
                   iff ((fsm_cs == CSM_SLEEP) && (fsm_ns != CSM_SLEEP)) {
      bins by_irq          = {2'b01};
      bins by_debug        = {2'b10};   // expected unreachable, see F-02
      bins by_both         = {2'b11};
      bins by_other        = {2'b00};
    }
  endgroup

  cg_ma_issue u_cg_ma_issue = new();

  // ==========================================================================
  // Structural assertions backing the illegal_bins above.  These state the same
  // facts to the formal / simulation checker, so a coverage build and a
  // no-coverage build both catch the violation.
  // ==========================================================================
  AssertInOrderIssue: assert property (
    @(posedge clk_i) disable iff (!rst_ni) ir1_issued |-> ir0_issued)
    else $error("FCOV: out-of-order issue -- ir1 issued without ir0 (see F-09)");

  AssertIrValidLegal: assert property (
    @(posedge clk_i) disable iff (!rst_ni) ir_valid_i[1] |-> ir_valid_i[0])
    else $error("FCOV: ir_valid_i == 2'b10");

  AssertFsmOnehot: assert property (
    @(posedge clk_i) disable iff (!rst_ni) $onehot(ctrl_fsm_cs))
    else $error("FCOV: ctrl_fsm_cs is not one-hot");

`endif  // KUDU_FCOV_OFF

endmodule
