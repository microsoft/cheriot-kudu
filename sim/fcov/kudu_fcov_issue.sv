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
  input logic        ir0_trap_event,

  // --- trap context (bug cross-check, sim/testplan/fcov_bug_crosscheck.md) ----
  input priv_lvl_e   priv_mode_i,
  input logic        csr_mstatus_tw_i,
  input logic        ebreak_enter_debug,
  input logic        ir0_mode_err
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

  typedef enum logic [1:0] {
    ISSUE_CYCLE, ISSUE_OPERAND, ISSUE_BP_RESOLUTION, ISSUE_CHERI_DEP
  } fcov_issue_event_e;

  typedef struct packed {
    fcov_issue_slot_e slot;
    fcov_issue_operand_e operand;
    fcov_fwd_outcome_e outcome;
    fcov_fwd_src_e producer;
    kudu_instr_scat_e consumer_class;
    logic issued;
    fcov_bp_kind_e kind;
    logic predicted_taken;
    logic actual_taken;
    fcov_bp_recovery_e recovery;
    logic blocked;
  } fcov_issue_sample_t;

  localparam fcov_issue_sample_t EMPTY_ISSUE_SAMPLE = '{
    FCOV_IR0, FCOV_RS1, FWD_READY, FWD_SRC_NONE, SC_ALU, 1'b0,
    BP_KIND_BRANCH, 1'b0, 1'b0, BP_REC_NONE, 1'b0
  };

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

  // Trap context. One trap decision per csr_save_cause_o cycle, classified
  // with the same priority as the csr_exc_info_o mux (issuer.sv:965-1028).
  typedef enum logic [3:0] {
    TC_NONE, TC_IRQ, TC_DBG, TC_ECALL, TC_EBREAK, TC_ILLEGAL, TC_MODE_ERR,
    TC_FETCH_ERR, TC_CHERI, TC_CMT_ERR
  } fcov_trap_class_e;

  typedef enum logic [1:0] {
    MTVAL_ZERO, MTVAL_PC, MTVAL_INSN, MTVAL_OTHER
  } fcov_mtval_class_e;

  fcov_trap_class_e  trap_cls;
  fcov_mtval_class_e mtval_cls;
  logic              mtval_unexpected;
  logic              sysctl_ev;
  logic [3:0]        dbg_src, dbg_src_q;

  always_comb begin
    trap_cls = TC_NONE;
    if (ctrl_fsm_cs[CSM_CMT_FLUSH] && cmt_err_i) begin
      trap_cls = TC_CMT_ERR;
    end else if (ctrl_fsm_cs[CSM_ISSUE_SPECIAL]) begin
      case (special_case_q)
        DEBUG: trap_cls = TC_DBG;
        IRQ:   trap_cls = TC_IRQ;
        SYSCTL: begin
          if (csr_exc_info_o.mcause == EXC_CAUSE_BREAKPOINT)
            trap_cls = TC_EBREAK;
          else if (csr_exc_info_o.mcause == EXC_CAUSE_ECALL_UMODE ||
                   csr_exc_info_o.mcause == EXC_CAUSE_ECALL_MMODE)
            trap_cls = TC_ECALL;
        end
        EXEC: begin
          if (ir0_dec.errs.perm_vio || ir0_dec.errs.bound_vio)          trap_cls = TC_CHERI;
          else if (ir0_dec.errs.fetch_err)                              trap_cls = TC_FETCH_ERR;
          else if (ir0_dec.errs.illegal_insn || ir0_dec.errs.illegal_c_insn) trap_cls = TC_ILLEGAL;
          else if (ir0_mode_err)                                        trap_cls = TC_MODE_ERR;
          else                                                          trap_cls = TC_CHERI;
        end
        default: ;
      endcase
    end
  end

  always_comb begin
    if (csr_exc_info_o.mtval == 32'h0)
      mtval_cls = MTVAL_ZERO;
    else if (csr_exc_info_o.mtval == csr_exc_info_o.pc)
      mtval_cls = MTVAL_PC;
    else if (csr_exc_info_o.mtval ==
             (ir0_dec.is_comp ? {16'h0, ir0_dec.c_insn} : ir0_dec.insn))
      mtval_cls = MTVAL_INSN;
    else
      mtval_cls = MTVAL_OTHER;
  end

  // Class-level mtval policy (KUDU-005, 010, 041). Fetch errors may report
  // pc + 2 (ferr2w), which classifies as OTHER. A CHERI mtval is an encoded
  // cause and may coincide with an instruction word, so only PC is wrong.
  always_comb begin
    case (trap_cls)
      TC_IRQ, TC_ECALL:        mtval_unexpected = (mtval_cls != MTVAL_ZERO);
      TC_EBREAK:               mtval_unexpected = (mtval_cls != MTVAL_PC);
      TC_ILLEGAL, TC_MODE_ERR: mtval_unexpected = (mtval_cls inside {MTVAL_PC, MTVAL_OTHER});
      TC_FETCH_ERR:            mtval_unexpected = (mtval_cls inside {MTVAL_ZERO, MTVAL_INSN});
      TC_CHERI:                mtval_unexpected = (mtval_cls == MTVAL_PC);
      default:                 mtval_unexpected = 1'b0;
    endcase
  end

  // A privileged sysctl instruction reaching the special-case state, whether
  // it executes (SYSCTL) or traps (EXEC). ir0 still holds it in that cycle.
  assign sysctl_ev = ctrl_fsm_cs[CSM_ISSUE_SPECIAL] &&
                     (special_case_q == SYSCTL || special_case_q == EXEC) &&
                     ir_valid_i[0] && ir0_dec.sysctl.valid;

  // The four terms of handle_debug (issuer.sv:738-739). is_brkpt is the
  // trigger match, not an ebreak instruction. Latched up to the special-case
  // state so the source can be compared with the cause reported there.
  assign dbg_src = {single_step_trap_q, ebreak_enter_debug,
                    ir_valid_i[0] & ir0_dec.is_brkpt, debug_req_i};

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dbg_src_q <= '0;
    end else if (handle_debug && !ctrl_fsm_cs[CSM_ISSUE_SPECIAL]) begin
      dbg_src_q <= dbg_src;
    end
  end

  // ==========================================================================
  // FC_MA_ISSUE - issue stage and control FSM
  // ==========================================================================
  // Sample arguments are values, not shared mutable event state. Each point
  // and cross accepts only its own event kind, including cycle transitions.
  covergroup cg_ma_issue with function sample(
      fcov_issue_event_e event_kind, fcov_issue_sample_t event_data);
    option.per_instance = 1;
    option.name         = "FC_MA_ISSUE";

    cp_consumer_slot: coverpoint event_data.slot iff (event_kind == ISSUE_OPERAND) {
      bins ir0 = {FCOV_IR0};
      bins ir1 = {FCOV_IR1};
    }
    cp_operand: coverpoint event_data.operand iff (event_kind == ISSUE_OPERAND) {
      bins rs1 = {FCOV_RS1};
      bins rs2 = {FCOV_RS2};
    }
    cp_operand_outcome: coverpoint event_data.outcome iff (event_kind == ISSUE_OPERAND) {
      bins ready = {FWD_READY};
      bins rescued = {FWD_RESCUED};
      bins raw_stall = {FWD_RAW_STALL};
      bins same_bundle_ir0_to_ir1 = {FWD_SAME_BUNDLE};
    }
    cp_producer: coverpoint event_data.producer
        iff (event_kind == ISSUE_OPERAND && event_data.outcome == FWD_RESCUED) {
      bins alu0 = {FWD_SRC_ALU0};
      bins alu1 = {FWD_SRC_ALU1};
      bins ls = {FWD_SRC_LS};
      bins mult = {FWD_SRC_MULT};
      bins multi = {FWD_SRC_MULTI};
    }
    cp_consumer_class: coverpoint event_data.consumer_class iff (event_kind == ISSUE_OPERAND) {
      bins alu = {SC_ALU};
      bins muldiv = {SC_MULDIV};
      bins ctrl = {SC_CTRL};
      bins mem = {SC_MEM};
      bins atomic = {SC_ATOMIC};
      bins sysreg = {SC_SYSREG};
      bins cheri = {SC_CHERI};
      bins bad = {SC_BAD};
    }
    cp_issued: coverpoint event_data.issued iff (event_kind == ISSUE_OPERAND) {
      bins stalled = {1'b0};
      bins issued = {1'b1};
    }

    x_operand_outcome_issue:
      cross cp_consumer_slot, cp_operand, cp_operand_outcome, cp_issued
      iff (event_kind == ISSUE_OPERAND) {
        // fcov_operand_outcome() returns FWD_SAME_BUNDLE only for IR1.
        ignore_bins same_bundle_ir0 = binsof(cp_consumer_slot.ir0) &&
            binsof(cp_operand_outcome.same_bundle_ir0_to_ir1);
      }
    x_fwd_producer_consumer:
      cross cp_producer, cp_consumer_slot, cp_consumer_class
      iff (event_kind == ISSUE_OPERAND);

    cp_resolution_slot: coverpoint event_data.slot iff (event_kind == ISSUE_BP_RESOLUTION) {
      bins ir0 = {FCOV_IR0};
      bins ir1 = {FCOV_IR1};
    }
    cp_resolution_kind: coverpoint event_data.kind iff (event_kind == ISSUE_BP_RESOLUTION) {
      bins branch = {BP_KIND_BRANCH};
      bins jal = {BP_KIND_JAL};
      bins jalr = {BP_KIND_JALR};
    }
    cp_predicted_taken: coverpoint event_data.predicted_taken
        iff (event_kind == ISSUE_BP_RESOLUTION) {
      bins not_taken = {1'b0};
      bins taken = {1'b1};
    }
    cp_actual_taken: coverpoint event_data.actual_taken iff (event_kind == ISSUE_BP_RESOLUTION) {
      bins not_taken = {1'b0};
      bins taken = {1'b1};
    }
    cp_recovery: coverpoint event_data.recovery iff (event_kind == ISSUE_BP_RESOLUTION) {
      bins none_correct = {BP_REC_NONE};
      bins ordinary_pc_set = {BP_REC_PC_SET};
      bins alt_apply = {BP_REC_ALT_APPLY};
      bins alt_cancel_flush = {BP_REC_ALT_CANCEL_FLUSH};
    }

    x_prediction_resolution_recovery:
      cross cp_resolution_slot, cp_resolution_kind, cp_predicted_taken,
            cp_actual_taken, cp_recovery iff (event_kind == ISSUE_BP_RESOLUTION) {
        ignore_bins jal_never_not_taken =
          binsof(cp_resolution_kind) intersect {BP_KIND_JAL, BP_KIND_JALR} &&
          binsof(cp_actual_taken.not_taken);
      }

    cp_cheri_slot: coverpoint event_data.slot iff (event_kind == ISSUE_CHERI_DEP) {
      option.weight = issuer.CHERIoTEn ? 1 : 0;
      bins ir0 = {FCOV_IR0};
      bins ir1 = {FCOV_IR1};
    }
    cp_cheri_temporal_outcome: coverpoint event_data.blocked iff (event_kind == ISSUE_CHERI_DEP) {
      option.weight = issuer.CHERIoTEn ? 1 : 0;
      bins clear = {1'b0};
      bins temporal_stall = {1'b1};
    }
    cp_cheri_temporal_issued: coverpoint event_data.issued iff (event_kind == ISSUE_CHERI_DEP) {
      option.weight = issuer.CHERIoTEn ? 1 : 0;
      bins stalled = {1'b0};
      bins issued = {1'b1};
    }
    x_cheri_temporal_issue:
      cross cp_cheri_slot, cp_cheri_temporal_outcome, cp_cheri_temporal_issued
      iff (event_kind == ISSUE_CHERI_DEP && cheri_active && issuer.LoadFiltEn) {
        option.weight = (issuer.CHERIoTEn && issuer.LoadFiltEn) ? 1 : 0;
      }

    // KUDU-051: LR/SC skipped the load-barrier hazard after a CLC. Which kind
    // of instruction consumed a capability operand, stalled or not.
    cp_cheri_dep_class: coverpoint event_data.consumer_class
        iff (event_kind == ISSUE_CHERI_DEP) {
      option.weight = issuer.CHERIoTEn ? 1 : 0;
      bins ctrl = {SC_CTRL};
      bins mem = {SC_MEM};
      bins atomic = {SC_ATOMIC};
      bins sysreg = {SC_SYSREG};
      bins cheri = {SC_CHERI};
    }
    x_cheri_dep_consumer:
      cross cp_cheri_temporal_outcome, cp_cheri_dep_class
      iff (event_kind == ISSUE_CHERI_DEP && cheri_active && issuer.LoadFiltEn) {
        option.weight = (issuer.CHERIoTEn && issuer.LoadFiltEn) ? 1 : 0;
      }

    cp_ira_is0: coverpoint ira_is0_i iff (event_kind == ISSUE_CYCLE) {
      bins irb_is_ir0 = {1'b0};
      bins ira_is_ir0 = {1'b1};
    }

    // ir_valid_i == 2'b10 is illegal: slot 1 valid without slot 0.  Already
    // asserted in RTL by AssertRdOutputLegal in *both* FIFO variants
    // (stage_fifo.sv:240, dual_fifo.sv:208).  This is a second, independent
    // check -- an assertion that is compiled out leaves no trace, a coverage
    // illegal_bin does not.
    cp_ir_valid: coverpoint ir_valid_i iff (event_kind == ISSUE_CYCLE) {
      bins none    = {2'b00};
      bins ir0     = {2'b01};
      bins dual    = {2'b11};
      illegal_bins slot1_only = {2'b10};
    }

    cp_any_err: coverpoint any_err_q iff (event_kind == ISSUE_CYCLE) {
      bins none   = {2'b00};
      bins ir0    = {2'b01};
      bins ir1    = {2'b10};   // younger-only error: must defer, not trap
      bins both   = {2'b11};
    }

    // The whole answer to "ir0 stalled by a hazard but ir1 not" is this one
    // coverpoint.  All four values are reachable and meaningful.
    cp_hazard: coverpoint hazard_q iff (event_kind == ISSUE_CYCLE) {
      bins none = {2'b00};
      bins ir0  = {2'b01};
      bins ir1  = {2'b10};
      bins both = {2'b11};
    }

    // Issue is strictly in order: pl_sel_enable[1] is gated on
    // ir0_normal_issued (issuer.sv:304), which is gated on ~ir_hazard[0]
    // (:312, :736-737).  So ir1_issued implies ir0_issued and the 2'b10 cell
    // cannot occur.  A hit means the issue-enable chain is broken.
    cp_issue_result: coverpoint issue_pair iff (event_kind == ISSUE_CYCLE) {
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
    cp_pl_sel_ir0: coverpoint ir0_pl_sel iff (event_kind == ISSUE_CYCLE) {
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

    cp_pl_sel_ir1: coverpoint ir1_pl_sel iff (event_kind == ISSUE_CYCLE) {
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

    cp_ex_valid: coverpoint $countones(ex_valid_o) iff (event_kind == ISSUE_CYCLE) {
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
    cp_ir1_ooo_lost: coverpoint ir1_ooo_rdy_event iff (event_kind == ISSUE_CYCLE) {
      bins lost = {1'b1};
    }

    cp_suppress1: coverpoint suppress1
        iff (event_kind == ISSUE_CYCLE &&
             slot1_present && (cheri_active || suppress1 != SUP_CJALR_SERIALISE));

    cp_sbd_full: coverpoint sbdfifo_wr_rdy_i iff (event_kind == ISSUE_CYCLE) {
      bins both_rdy = {2'b11};
      bins one_rdy  = {2'b01};
      bins none_rdy = {2'b00};
      illegal_bins slot1_only = {2'b10};
    }

    // ======================================================================
    // 10.2 Hazards and forwarding
    // ======================================================================
    cp_raw_hazard: coverpoint (ir_raw_hazard & ir_valid_i)
        iff (event_kind == ISSUE_CYCLE) { bins v[] = {[0:3]}; }
    cp_waw_hazard: coverpoint (ir_waw_hazard & ir_valid_i)
        iff (event_kind == ISSUE_CYCLE) { bins v[] = {[0:3]}; }
    cp_cheri_hazard: coverpoint (ir_cheri_hazard & ir_valid_i)
        iff (event_kind == ISSUE_CYCLE && cheri_active) {
      option.weight = issuer.CHERIoTEn ? 1 : 0;
      bins v[] = {[0:3]};
    }

    // ir_waw_hazard[1] carries an extra "| wr_req_conflict" term that slot 0
    // does not (issuer.sv:424-426): two instructions in one bundle targeting
    // the same rd.  It is a slot-1-only condition with no slot-0 counterpart,
    // so this is the only place it is observable.
    cp_wr_req_conflict: coverpoint wr_req_conflict
        iff (event_kind == ISSUE_CYCLE) { bins hit = {1'b1}; }

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
    cp_raw_cause_ir0: coverpoint ir0_raw_cause
        iff (event_kind == ISSUE_CYCLE && (ir_raw_hazard[0] & ir_valid_i[0])) {
      wildcard bins alu0_set = {5'b???1?};
      wildcard bins alu0_clr = {5'b???0?};
      wildcard bins alu1_set = {5'b??1??};
      wildcard bins alu1_clr = {5'b??0??};
      wildcard bins ls_set   = {5'b?1???};
      wildcard bins ls_clr   = {5'b?0???};
      wildcard bins mult_set = {5'b1????};
      wildcard bins mult_clr = {5'b0????};
    }
    cp_raw_cause_ir1: coverpoint ir1_raw_cause
        iff (event_kind == ISSUE_CYCLE && (ir_raw_hazard[1] & ir_valid_i[1])) {
      wildcard bins alu0_set = {5'b???1?};
      wildcard bins alu0_clr = {5'b???0?};
      wildcard bins alu1_set = {5'b??1??};
      wildcard bins alu1_clr = {5'b??0??};
      wildcard bins ls_set   = {5'b?1???};
      wildcard bins ls_clr   = {5'b?0???};
      wildcard bins mult_set = {5'b1????};
      wildcard bins mult_clr = {5'b0????};
    }

    cp_ir1_raw_by_ir0: coverpoint ir1_raw_by_ir0_event
        iff (event_kind == ISSUE_CYCLE) { bins hit = {1'b1}; }
    cp_ra_update_jalr: coverpoint ra_relation
        iff (event_kind == ISSUE_CYCLE && ra_update_sample) {
      option.weight = issuer.CHERIoTEn ? 1 : 0;
      bins actual_equals_predicted = {RA_EQUAL};
      bins predicted_more_permissive = {RA_PRED_MORE};
      bins predicted_less_permissive = {RA_PRED_LESS};
      bins other = {RA_OTHER};
    }
    cp_stall_nohaz0: coverpoint ir0_stall_nohaz_event
        iff (event_kind == ISSUE_CYCLE) { bins hit = {1'b1}; }
    cp_stall_nohaz1: coverpoint ir1_stall_nohaz_event
        iff (event_kind == ISSUE_CYCLE) { bins hit = {1'b1}; }

    // Overlapping wildcard bins count every set register bit in a multi-hot mask.
    // Pad bit zero so wildcard positions retain the RTL's register numbering.
    cp_reg_wrsv_q: coverpoint {reg_wrsv_q, 1'b0} iff (event_kind == ISSUE_CYCLE) {
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
        iff (event_kind == ISSUE_CYCLE && cheri_active && issuer.LoadFiltEn) {
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
    x_cp_reg_wrsv_q: cross cp_hazard, cp_reg_wrsv_q iff (event_kind == ISSUE_CYCLE);
    x_cp_reg_cheri_trsv_q: cross cp_hazard, cp_reg_cheri_trsv_q
        iff (event_kind == ISSUE_CYCLE && cheri_active && issuer.LoadFiltEn) {
      option.weight = (issuer.CHERIoTEn && issuer.LoadFiltEn) ? 1 : 0;
    }

    // Pair order is {forwarding active, write reserved}.
    cp_fwd_wrsv_r1: coverpoint {ir0_pl_fwd_act[1], reg_wrsv_q[1]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r2: coverpoint {ir0_pl_fwd_act[2], reg_wrsv_q[2]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r3: coverpoint {ir0_pl_fwd_act[3], reg_wrsv_q[3]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r4: coverpoint {ir0_pl_fwd_act[4], reg_wrsv_q[4]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r5: coverpoint {ir0_pl_fwd_act[5], reg_wrsv_q[5]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r6: coverpoint {ir0_pl_fwd_act[6], reg_wrsv_q[6]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r7: coverpoint {ir0_pl_fwd_act[7], reg_wrsv_q[7]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r8: coverpoint {ir0_pl_fwd_act[8], reg_wrsv_q[8]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r9: coverpoint {ir0_pl_fwd_act[9], reg_wrsv_q[9]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r10: coverpoint {ir0_pl_fwd_act[10], reg_wrsv_q[10]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r11: coverpoint {ir0_pl_fwd_act[11], reg_wrsv_q[11]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r12: coverpoint {ir0_pl_fwd_act[12], reg_wrsv_q[12]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r13: coverpoint {ir0_pl_fwd_act[13], reg_wrsv_q[13]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r14: coverpoint {ir0_pl_fwd_act[14], reg_wrsv_q[14]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r15: coverpoint {ir0_pl_fwd_act[15], reg_wrsv_q[15]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r16: coverpoint {ir0_pl_fwd_act[16], reg_wrsv_q[16]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r17: coverpoint {ir0_pl_fwd_act[17], reg_wrsv_q[17]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r18: coverpoint {ir0_pl_fwd_act[18], reg_wrsv_q[18]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r19: coverpoint {ir0_pl_fwd_act[19], reg_wrsv_q[19]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r20: coverpoint {ir0_pl_fwd_act[20], reg_wrsv_q[20]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r21: coverpoint {ir0_pl_fwd_act[21], reg_wrsv_q[21]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r22: coverpoint {ir0_pl_fwd_act[22], reg_wrsv_q[22]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r23: coverpoint {ir0_pl_fwd_act[23], reg_wrsv_q[23]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r24: coverpoint {ir0_pl_fwd_act[24], reg_wrsv_q[24]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r25: coverpoint {ir0_pl_fwd_act[25], reg_wrsv_q[25]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r26: coverpoint {ir0_pl_fwd_act[26], reg_wrsv_q[26]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r27: coverpoint {ir0_pl_fwd_act[27], reg_wrsv_q[27]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r28: coverpoint {ir0_pl_fwd_act[28], reg_wrsv_q[28]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r29: coverpoint {ir0_pl_fwd_act[29], reg_wrsv_q[29]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r30: coverpoint {ir0_pl_fwd_act[30], reg_wrsv_q[30]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }
    cp_fwd_wrsv_r31: coverpoint {ir0_pl_fwd_act[31], reg_wrsv_q[31]} iff (event_kind == ISSUE_CYCLE) {
      bins pair_0 = {2'b00};
      bins pair_1 = {2'b01};
      bins pair_3 = {2'b11};
      bins pair_2 = {2'b10};
    }

    cp_fwd_source: coverpoint {multpl_fwd_act_i_any, lspl_fwd_act_i_any,
                               alupl1_fwd_act_i_any, alupl0_fwd_act_i_any}
        iff (event_kind == ISSUE_CYCLE) {
      bins none  = {4'b0000};
      bins alu0  = {4'b0001};
      bins alu1  = {4'b0010};
      bins ls    = {4'b0100};
      bins mult  = {4'b1000};
      bins multi = {[0:15]} with ($countones(item) > 1);
    }

    cp_fwd_to_slot: coverpoint {|ir1_pl_fwd_act, |ir0_pl_fwd_act}
        iff (event_kind == ISSUE_CYCLE) {
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
    cp_fsm_state: coverpoint 4'(fsm_cs) iff (event_kind == ISSUE_CYCLE) {
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

    cp_fsm_trans: coverpoint fsm_cs iff (event_kind == ISSUE_CYCLE) {
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

    cp_special_case: coverpoint special_case_q
        iff (event_kind == ISSUE_CYCLE && ctrl_fsm_cs[CSM_ISSUE_SPECIAL]) {
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
                                   handle_sysctl, handle_err} iff (event_kind == ISSUE_CYCLE) {
      bins none     = {5'b00000};
      bins err      = {5'b00001};
      bins sysctl   = {5'b00010};
      bins cmplx    = {5'b00100};
      bins irq      = {5'b01000};
      bins debug    = {5'b10000};
      bins multiple = {[0:31]} with ($countones(item) > 1);
    }

    cp_cmt_flush: coverpoint cmt_flush_o iff (event_kind == ISSUE_CYCLE) { bins hit = {1'b1}; }
    cp_cmt_err: coverpoint cmt_err_i iff (event_kind == ISSUE_CYCLE) { bins hit = {1'b1}; }
    cp_mispredict: coverpoint mispredict iff (event_kind == ISSUE_CYCLE) { bins v[] = {[0:3]}; }
    cp_branch_mispredict_event: coverpoint branch_mispredict_event iff (event_kind == ISSUE_CYCLE) {
      wildcard bins ir0 = {2'b?1};
      wildcard bins ir1 = {2'b1?};
    }
    cp_slot1_suppressed_by_mispredict0: coverpoint
        (ir_valid_i[1] && ir0_issued && !ir1_issued && mispredict[0])
        iff (event_kind == ISSUE_CYCLE) {
      bins hit = {1'b1};
    }

    cp_handle_irq: coverpoint handle_irq iff (event_kind == ISSUE_CYCLE) { bins hit = {1'b1}; }

    x_cp_irq_valid: cross cp_handle_irq, cp_ir_valid iff (event_kind == ISSUE_CYCLE);

    cp_irq_masked: coverpoint (irq_pending_i & ~csr_mstatus_mie_i) iff (event_kind == ISSUE_CYCLE) {
      bins masked = {1'b1};
    }

    // irq_fast_i is [14:0], so a fast-interrupt id only ever spans 0..14 and
    // the generated cause tops out at 6'd62.  mfip_id is a don't-care when the
    // pending interrupt is software / timer / external, hence the bin rather
    // than an illegal_bin.  There is no NMI in this design (WV-05).
    cp_mfip_id: coverpoint mfip_id iff (event_kind == ISSUE_CYCLE && irq_pending_i) {
      bins id[] = {[0:14]};
      bins not_fast = {4'd15};
    }

    cp_intr_event: coverpoint intr_event iff (event_kind == ISSUE_CYCLE) { bins hit = {1'b1}; }
    cp_ir0_trap_event: coverpoint ir0_trap_event iff (event_kind == ISSUE_CYCLE) { bins hit = {1'b1}; }

    // Debug entry asserts save_cause too, but does not write mcause.
    cp_mcause: coverpoint csr_exc_info_o.mcause
        iff (event_kind == ISSUE_CYCLE && csr_save_cause_o && !debug_csr_save_o) {
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

    cp_handle_debug: coverpoint handle_debug iff (event_kind == ISSUE_CYCLE) { bins hit = {1'b1}; }
    cp_debug_mode: coverpoint debug_mode_q iff (event_kind == ISSUE_CYCLE) { bins in_debug = {1'b1}; }

    // {step_req_q, ebreak_enter_debug, trigger match, debug_req_i}: the four
    // terms of handle_debug. The races are KUDU-030, 040 and 071.
    cp_dbg_entry_src: coverpoint dbg_src
                      iff (event_kind == ISSUE_CYCLE && handle_debug) {
      bins req            = {4'b0001};
      bins trigger        = {4'b0010};
      bins ebreak         = {4'b0100};
      bins step           = {4'b1000};
      bins step_req       = {4'b1001};
      bins step_trigger   = {4'b1010};
      bins step_ebreak    = {4'b1100};
      bins trigger_req    = {4'b0011};
      bins ebreak_req     = {4'b0101};
      bins trigger_ebreak = {4'b0110};
      bins other_multiple = {[0:15]} with ($countones(item) > 2);
    }

    // KUDU-026: halt request with an empty IR.
    x_dbg_ir_valid: cross cp_handle_debug, cp_ir_valid iff (event_kind == ISSUE_CYCLE);

    // debug_cause_o is only driven while the control FSM is issuing the debug
    // special case (issuer.sv:940-952); handle_debug is the request that leads
    // to that state, so sampling on it reads the default DBG_CAUSE_NONE.
    //
    // HALTREQ during a single step was reported as STEP (finding F-06,
    // KUDU-040, fixed in d290cd0: HALTREQ is now tested first).
    // DBG_CAUSE_NONE is reachable rather than illegal: entry is latched from
    // handle_debug, so a halt request that has already deasserted by the time
    // the FSM issues the special case leaves every cause term low. That is
    // KUDU-073, waived (debug_req_i must be held until acknowledged; see
    // bug_logs_3.md). It is tracked in its own bin instead of aborting.
    cp_dbg_cause_sel: coverpoint debug_cause_o
                      iff (event_kind == ISSUE_CYCLE &&
                           (ctrl_fsm_cs[CSM_ISSUE_SPECIAL] & (special_case_q == DEBUG))) {
      bins ebreak  = {DBG_CAUSE_EBREAK};
      bins trigger = {DBG_CAUSE_TRIGGER};
      bins haltreq = {DBG_CAUSE_HALTREQ};
      bins step    = {DBG_CAUSE_STEP};
      bins none    = {DBG_CAUSE_NONE};
    }

    cp_single_step: coverpoint debug_single_step_i
        iff (event_kind == ISSUE_CYCLE) { bins hit = {1'b1}; }

    cp_dbg_req_hold: coverpoint dbg_req_len iff (event_kind == ISSUE_CYCLE && dbg_req_fell) {
      bins one   = {1};
      bins two   = {2};
      bins three = {3};
      bins more  = {[4:$]};
    }

    cp_sleep_entry: coverpoint ((fsm_ns == CSM_SLEEP) && (fsm_cs != CSM_SLEEP))
        iff (event_kind == ISSUE_CYCLE) {
      bins entered = {1'b1};
    }

    // Finding F-02 (KUDU-003): the WFI wake condition did not include
    // debug_req_i, so a debugger could not halt a core in WFI. Fixed; by_debug
    // and by_both are now expected to fill.
    cp_sleep_wake: coverpoint {debug_req_i, irq_pending_i}
                   iff (event_kind == ISSUE_CYCLE &&
                        (fsm_cs == CSM_SLEEP) && (fsm_ns != CSM_SLEEP)) {
      bins by_irq          = {2'b01};
      bins by_debug        = {2'b10};
      bins by_both         = {2'b11};
      bins by_other        = {2'b00};
    }

    // Entry source latched before the special-case state, against the cause
    // reported there. Diagnostic only (weight 0): the cells follow from the
    // cause priority, and KUDU-071 (open) shows up as step_ebreak / step_trigger
    // reporting EBREAK / TRIGGER instead of STEP.
    cp_dbg_src_q: coverpoint dbg_src_q
                  iff (event_kind == ISSUE_CYCLE &&
                       (ctrl_fsm_cs[CSM_ISSUE_SPECIAL] & (special_case_q == DEBUG))) {
      option.weight = 0;
      bins none           = {4'b0000};
      bins req            = {4'b0001};
      bins trigger        = {4'b0010};
      bins ebreak         = {4'b0100};
      bins step           = {4'b1000};
      bins step_req       = {4'b1001};
      bins step_trigger   = {4'b1010};
      bins step_ebreak    = {4'b1100};
      bins other_multiple = {[0:15]} with ($countones(item) > 1 &&
                                          !(item inside {4'b1001, 4'b1010, 4'b1100}));
    }
    x_dbg_src_cause: cross cp_dbg_src_q, cp_dbg_cause_sel
        iff (event_kind == ISSUE_CYCLE &&
             (ctrl_fsm_cs[CSM_ISSUE_SPECIAL] & (special_case_q == DEBUG))) {
      option.weight = 0;
    }

    // ======================================================================
    // Trap context: one sample per trap decision (csr_save_cause_o)
    // ======================================================================
    cp_tc: coverpoint trap_cls iff (event_kind == ISSUE_CYCLE && csr_save_cause_o) {
      bins irq       = {TC_IRQ};
      bins dbg       = {TC_DBG};
      bins ecall     = {TC_ECALL};
      bins ebreak    = {TC_EBREAK};
      bins illegal   = {TC_ILLEGAL};
      bins mode_err  = {TC_MODE_ERR};
      bins fetch_err = {TC_FETCH_ERR};
      bins cheri     = {TC_CHERI};
      bins cmt_err   = {TC_CMT_ERR};
    }
    cp_trap_dm: coverpoint debug_mode_q iff (event_kind == ISSUE_CYCLE && csr_save_cause_o) {
      bins normal = {1'b0};
      bins debug  = {1'b1};
    }
    cp_trap_priv: coverpoint priv_mode_i iff (event_kind == ISSUE_CYCLE && csr_save_cause_o) {
      bins m = {PRIV_LVL_M};
      bins u = {PRIV_LVL_U};
    }
    cp_trap_mie: coverpoint csr_mstatus_mie_i
        iff (event_kind == ISSUE_CYCLE && csr_save_cause_o) {
      bins off = {1'b0};
      bins on  = {1'b1};
    }
    cp_trap_step: coverpoint debug_single_step_i
        iff (event_kind == ISSUE_CYCLE && csr_save_cause_o) {
      bins off = {1'b0};
      bins on  = {1'b1};
    }

    // KUDU-004, 021, 022, 023, 035: every trap class inside and outside debug
    // mode. Interrupts and debug entry cannot happen in debug mode, decoder and
    // CJALR CHERI errors are suppressed there (AssertDebugSuppressesCheriErrors
    // in kudu_fcov_id.sv), and debug mode runs in M-mode, where no mode error
    // is possible except DRET, which is legal in debug mode.
    x_trap_dm: cross cp_tc, cp_trap_dm iff (event_kind == ISSUE_CYCLE && csr_save_cause_o) {
      ignore_bins not_in_debug = binsof(cp_tc) intersect {TC_IRQ, TC_DBG, TC_CHERI, TC_MODE_ERR} &&
                                 binsof(cp_trap_dm.debug);
    }
    // KUDU-036, 038: trap class against the interrupt enable and privilege.
    // An interrupt in M-mode needs MIE (issuer.sv:736).
    x_trap_mie: cross cp_tc, cp_trap_mie, cp_trap_priv
        iff (event_kind == ISSUE_CYCLE && csr_save_cause_o) {
      ignore_bins irq_m_masked = binsof(cp_tc) intersect {TC_IRQ} &&
                                 binsof(cp_trap_mie.off) && binsof(cp_trap_priv.m);
    }
    // KUDU-028: a stepped instruction that itself traps. Interrupts are masked
    // while stepping (cp_irq_block).
    x_step_trap: cross cp_tc, cp_trap_step iff (event_kind == ISSUE_CYCLE && csr_save_cause_o) {
      ignore_bins no_irq_step = binsof(cp_tc) intersect {TC_IRQ} && binsof(cp_trap_step.on);
    }

    // KUDU-039: mepc/dpc must be even (IALIGN = 16). Backed by AssertTrapPcEven.
    cp_trap_pc_odd: coverpoint csr_exc_info_o.pc[0]
        iff (event_kind == ISSUE_CYCLE && csr_save_cause_o) {
      bins even = {1'b0};
      illegal_bins odd = {1'b1};
    }

    // mtval written for each trap class (debug entry does not write mtval).
    // KUDU-005, 010, 015, 041, 052. The values themselves are checked by the
    // trace diff; the goals are the expected class pairs, and anything else
    // fills the weight-0 tripwire cp_mtval_unexpected.
    cp_mtval: coverpoint mtval_cls
        iff (event_kind == ISSUE_CYCLE && csr_save_cause_o && !debug_csr_save_o) {
      bins zero  = {MTVAL_ZERO};
      bins pc    = {MTVAL_PC};
      bins insn  = {MTVAL_INSN};
      bins other = {MTVAL_OTHER};
    }
    x_cause_mtval: cross cp_tc, cp_mtval
        iff (event_kind == ISSUE_CYCLE && csr_save_cause_o && !debug_csr_save_o) {
      ignore_bins zero_only = binsof(cp_tc) intersect {TC_IRQ, TC_ECALL} &&
                              !binsof(cp_mtval) intersect {MTVAL_ZERO};
      ignore_bins pc_only = binsof(cp_tc) intersect {TC_EBREAK} &&
                            !binsof(cp_mtval) intersect {MTVAL_PC};
      ignore_bins insn_or_zero = binsof(cp_tc) intersect {TC_ILLEGAL, TC_MODE_ERR} &&
                                 binsof(cp_mtval) intersect {MTVAL_PC, MTVAL_OTHER};
      ignore_bins fetch_pc = binsof(cp_tc) intersect {TC_FETCH_ERR} &&
                             binsof(cp_mtval) intersect {MTVAL_ZERO, MTVAL_INSN};
      ignore_bins encoded = binsof(cp_tc) intersect {TC_CHERI, TC_CMT_ERR} &&
                            !binsof(cp_mtval) intersect {MTVAL_OTHER};
    }
    cp_mtval_unexpected: coverpoint mtval_unexpected
        iff (event_kind == ISSUE_CYCLE && csr_save_cause_o && !debug_csr_save_o) {
      option.weight = 0;
      bins hit = {1'b1};
    }

    // KUDU-004, 010, 034, 035: privileged sysctl instructions against the
    // privilege, debug mode and CHERI mode they run in, executed or trapped.
    cp_sysctl: coverpoint {ir0_dec.sysctl.mret, ir0_dec.sysctl.dret, ir0_dec.sysctl.wfi,
                           ir0_dec.sysctl.ecall, ir0_dec.sysctl.ebrk}
               iff (event_kind == ISSUE_CYCLE && sysctl_ev) {
      bins mret  = {5'b10000};
      bins dret  = {5'b01000};
      bins wfi   = {5'b00100};
      bins ecall = {5'b00010};
      bins ebrk  = {5'b00001};
    }
    cp_sysctl_priv: coverpoint priv_mode_i iff (event_kind == ISSUE_CYCLE && sysctl_ev) {
      bins m = {PRIV_LVL_M};
      bins u = {PRIV_LVL_U};
    }
    cp_sysctl_dm: coverpoint debug_mode_q iff (event_kind == ISSUE_CYCLE && sysctl_ev) {
      bins normal = {1'b0};
      bins debug  = {1'b1};
    }
    cp_sysctl_pmode: coverpoint cheri_pmode_i iff (event_kind == ISSUE_CYCLE && sysctl_ev) {
      option.weight = issuer.CHERIoTEn ? 1 : 0;
      bins rv32   = {1'b0};
      bins cheri  = {1'b1};
    }
    x_sysctl_mode: cross cp_sysctl, cp_sysctl_priv, cp_sysctl_dm, cp_sysctl_pmode
        iff (event_kind == ISSUE_CYCLE && sysctl_ev) {
      option.weight = issuer.CHERIoTEn ? 1 : 0;
      ignore_bins debug_is_m = binsof(cp_sysctl_dm.debug) && binsof(cp_sysctl_priv.u);
    }
    // KUDU-034: WFI against mstatus.TW and privilege.
    cp_sysctl_tw: coverpoint csr_mstatus_tw_i
        iff (event_kind == ISSUE_CYCLE && sysctl_ev && ir0_dec.sysctl.wfi) {
      bins off = {1'b0};
      bins on  = {1'b1};
    }
    x_wfi_tw: cross cp_sysctl_tw, cp_sysctl_priv
        iff (event_kind == ISSUE_CYCLE && sysctl_ev && ir0_dec.sysctl.wfi);
    // KUDU-010: MRET with and without ASR permission in PCC.
    cp_mret_asr: coverpoint ir0_dec.errs.asr_vio
        iff (event_kind == ISSUE_CYCLE && sysctl_ev && ir0_dec.sysctl.mret && cheri_active) {
      option.weight = issuer.CHERIoTEn ? 1 : 0;
      bins asr    = {1'b0};
      bins no_asr = {1'b1};
    }

    // KUDU-038: a pending interrupt in each privilege / MIE combination. In
    // U-mode an M-level interrupt is taken whatever MIE is.
    cp_irq_priv: coverpoint priv_mode_i
        iff (event_kind == ISSUE_CYCLE && irq_pending_i && !debug_mode_q &&
             !debug_single_step_i) {
      bins m = {PRIV_LVL_M};
      bins u = {PRIV_LVL_U};
    }
    cp_irq_mie: coverpoint csr_mstatus_mie_i
        iff (event_kind == ISSUE_CYCLE && irq_pending_i && !debug_mode_q &&
             !debug_single_step_i) {
      bins off = {1'b0};
      bins on  = {1'b1};
    }
    x_irq_priv_mie: cross cp_irq_priv, cp_irq_mie
        iff (event_kind == ISSUE_CYCLE && irq_pending_i && !debug_mode_q &&
             !debug_single_step_i);

    // KUDU-012, 029: no interrupt is taken in debug mode or while stepping
    // (issuer.sv:736-737). Backed by AssertNoIrqInDebug / AssertNoIrqWhileStepping.
    cp_irq_block: coverpoint {debug_mode_q, debug_single_step_i}
        iff (event_kind == ISSUE_CYCLE && handle_irq) {
      bins normal = {2'b00};
      illegal_bins in_debug = {2'b10, 2'b11};
      illegal_bins stepping = {2'b01};
    }

    // KUDU-072 (waived): the interrupt line dropped between the decision and
    // the special-case state. Integration requires interrupts to be held
    // until acknowledged, so this is informational (weight 0).
    cp_irq_withdrawn: coverpoint irq_pending_i
        iff (event_kind == ISSUE_CYCLE &&
             (ctrl_fsm_cs[CSM_ISSUE_SPECIAL] & (special_case_q == IRQ))) {
      option.weight = 0;
      bins held      = {1'b1};
      bins withdrawn = {1'b0};
    }
  endgroup

  cg_ma_issue u_cg_ma_issue = new();

  function automatic void sample_operand(
      fcov_issue_slot_e slot, fcov_issue_operand_e operand,
      fcov_fwd_outcome_e outcome, fcov_fwd_src_e producer,
      kudu_instr_scat_e consumer_class, logic issued);
    fcov_issue_sample_t data = EMPTY_ISSUE_SAMPLE;
    data.slot = slot;
    data.operand = operand;
    data.outcome = outcome;
    data.producer = producer;
    data.consumer_class = consumer_class;
    data.issued = issued;
    u_cg_ma_issue.sample(ISSUE_OPERAND, data);
  endfunction

  function automatic void sample_bp_resolution(
      fcov_issue_slot_e slot, fcov_bp_kind_e kind, logic predicted_taken,
      logic actual_taken, fcov_bp_recovery_e recovery);
    fcov_issue_sample_t data = EMPTY_ISSUE_SAMPLE;
    data.slot = slot;
    data.kind = kind;
    data.predicted_taken = predicted_taken;
    data.actual_taken = actual_taken;
    data.recovery = recovery;
    u_cg_ma_issue.sample(ISSUE_BP_RESOLUTION, data);
  endfunction

  function automatic void sample_cheri_dep(
      fcov_issue_slot_e slot, logic blocked, logic issued,
      kudu_instr_scat_e consumer_class);
    fcov_issue_sample_t data = EMPTY_ISSUE_SAMPLE;
    data.slot = slot;
    data.blocked = blocked;
    data.issued = issued;
    data.consumer_class = consumer_class;
    u_cg_ma_issue.sample(ISSUE_CHERI_DEP, data);
  endfunction

  always @(posedge clk_i) begin
    if (rst_ni) begin
      u_cg_ma_issue.sample(ISSUE_CYCLE, EMPTY_ISSUE_SAMPLE);
      if (ir_valid_i[0] && ir0_dec.rf_ren[0] && (ir0_dec.rs1 != 5'd0)) begin
        sample_operand(
            FCOV_IR0, FCOV_RS1, fcov_operand_outcome(FCOV_IR0, ir0_dec.rs1),
            fcov_fwd_src(ir0_dec.rs1), fcov_instr_scat(fcov_instr_cat(ir0_dec)),
            ir0_issued);
      end
      if (ir_valid_i[0] && ir0_dec.rf_ren[1] && (ir0_dec.rs2 != 5'd0)) begin
        sample_operand(
            FCOV_IR0, FCOV_RS2, fcov_operand_outcome(FCOV_IR0, ir0_dec.rs2),
            fcov_fwd_src(ir0_dec.rs2), fcov_instr_scat(fcov_instr_cat(ir0_dec)),
            ir0_issued);
      end
      if (ir_valid_i[1] && ir1_dec.rf_ren[0] && (ir1_dec.rs1 != 5'd0)) begin
        sample_operand(
            FCOV_IR1, FCOV_RS1, fcov_operand_outcome(FCOV_IR1, ir1_dec.rs1),
            fcov_fwd_src(ir1_dec.rs1), fcov_instr_scat(fcov_instr_cat(ir1_dec)),
            ir1_issued);
      end
      if (ir_valid_i[1] && ir1_dec.rf_ren[1] && (ir1_dec.rs2 != 5'd0)) begin
        sample_operand(
            FCOV_IR1, FCOV_RS2, fcov_operand_outcome(FCOV_IR1, ir1_dec.rs2),
            fcov_fwd_src(ir1_dec.rs2), fcov_instr_scat(fcov_instr_cat(ir1_dec)),
            ir1_issued);
      end

      if (ir0_issued && (ir0_dec.is_branch || ir0_dec.is_jal || ir0_dec.is_jalr)) begin
        sample_bp_resolution(
            FCOV_IR0, fcov_bp_kind(ir0_dec), ir0_dec.ptaken,
            ir0_dec.is_branch ? issuer.branch_info_i.branch_taken[0] : 1'b1,
            fcov_recovery_path(FCOV_IR0));
      end
      if (ir1_issued && (ir1_dec.is_branch || ir1_dec.is_jal || ir1_dec.is_jalr)) begin
        sample_bp_resolution(
            FCOV_IR1, fcov_bp_kind(ir1_dec), ir1_dec.ptaken,
            ir1_dec.is_branch ? issuer.branch_info_i.branch_taken[1] : 1'b1,
            fcov_recovery_path(FCOV_IR1));
      end

      if (cheri_active && issuer.LoadFiltEn && ir_valid_i[0] && ir0_dec.rs_cheri) begin
        sample_cheri_dep(FCOV_IR0, ir_cheri_hazard[0], ir0_issued,
                         fcov_instr_scat(fcov_instr_cat(ir0_dec)));
      end
      if (cheri_active && issuer.LoadFiltEn && ir_valid_i[1] && ir1_dec.rs_cheri) begin
        sample_cheri_dep(FCOV_IR1, ir_cheri_hazard[1], ir1_issued,
                         fcov_instr_scat(fcov_instr_cat(ir1_dec)));
      end
    end
  end

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

  AssertNoIrqInDebug: assert property (
    @(posedge clk_i) disable iff (!rst_ni) handle_irq |-> !debug_mode_q)
    else $error("FCOV: interrupt taken in debug mode (KUDU-012)");

  AssertNoIrqWhileStepping: assert property (
    @(posedge clk_i) disable iff (!rst_ni) handle_irq |-> !debug_single_step_i)
    else $error("FCOV: interrupt taken while single-stepping (KUDU-029)");

  AssertTrapPcEven: assert property (
    @(posedge clk_i) disable iff (!rst_ni) csr_save_cause_o |-> !csr_exc_info_o.pc[0])
    else $error("FCOV: odd exception pc 0x%08x (KUDU-039)", csr_exc_info_o.pc);

`endif  // KUDU_FCOV_OFF

endmodule

// ============================================================================
// kudu_sva_issue -- design-property assertions for rtl/issuer.sv.
//
// Checks the issuer's redirect targets (boot excluded), trap / interrupt /
// debug entry and exit, the cause/mtval it reports, the IR0 pc tracking that
// mepc/dpc depend on, special-instruction serialization and pipeline drain,
// single-step, and the scoreboard / forwarding hand-off at issue.  No
// assumptions; helper logic only.  Bound into issuer as u_fcov_sva_issue.
// ============================================================================
module kudu_sva_issue
  import super_pkg::*;
  import cheri_pkg::*;
  import csr_pkg::*;
#(
  parameter bit          CHERIoTEn  = 1'b1,
  parameter bit          RV32A      = 1'b1,
  parameter int unsigned DmHaltAddr = 32'h1A110800,
  parameter int unsigned DmExcAddr  = 32'h1A110808
) (
  input logic          clk_i,
  input logic          rst_ni,
  input logic          cheri_pmode_i,

  // IR / issue
  input logic [1:0]    ir_valid_i,
  input logic [1:0]    issuer_rdy_o,
  input ir_dec_t       ir0_dec,
  input ir_dec_t       ir1_dec,
  input logic          ir0_issued,
  input logic          ir1_issued,
  input logic          ir0_normal_issued,
  input logic [4:0]    ir0_pl_sel,
  input logic [4:0]    ir1_pl_sel,
  input logic [4:0]    ex_valid_o,
  input logic [4:0]    ex_rdy,
  input logic [1:0]    ir_any_err,
  input logic          ir0_mode_err,
  input logic [1:0]    mispredict,
  input logic [31:0]   ir0_target,
  input logic [31:0]   ir1_target,

  // hazards / forwarding
  input pl_fwd_t       alupl0_fwd_info_i,
  input pl_fwd_t       alupl1_fwd_info_i,
  input pl_fwd_t       lspl_fwd_info_i,
  input pl_fwd_t       multpl_fwd_info_i,
  input logic [31:1]   reg_wrsv_q,
  input logic [15:1]   reg_cheri_trsv_q,

  // scoreboard / commit / complex unit
  input logic          cmt_err_i,
  input logic [1:0]    sbdfifo_rd_valid_i,
  input logic [1:0]    sbdfifo_wr_rdy_i,
  input logic [1:0]    sbdfifo_wr_valid_o,
  input logic [1:0]    ir_fifo_wr,
  input logic          trvk_outstanding_i,
  input logic          lspl_rdy_i,
  input logic          cmplx_sbd_wr_i,
  input logic          cmplx_instr_start_o,

  // fetch redirect
  input logic          pc_set_o,
  input logic [31:0]   pc_target_o,

  // CSR interface
  input priv_lvl_e     priv_mode_i,
  input logic          irq_pending_i,
  input irqs_t         irqs_i,
  input logic          csr_mstatus_mie_i,
  input logic [31:0]   csr_mtvec_i,
  input logic [31:0]   csr_mepc_i,
  input logic [31:0]   csr_depc_i,
  input logic          csr_save_cause_o,
  input exc_info_t     csr_exc_info_o,
  input logic          csr_restore_mret_o,
  input logic          csr_restore_dret_o,

  // debug
  input logic          debug_req_i,
  input logic          debug_step_i,
  input logic          debug_mode_q,
  input logic          step_req_q,
  input dbg_cause_e    debug_cause_o,
  input logic          debug_csr_save_o,

  // controller
  input logic [15:0]   ctrl_fsm_cs,
  input special_case_e special_case_q,
  input logic          special_setpc_q,
  input sysctl_t       sysctl_q,
  input logic [31:0]   ir0_nxt_pc_q
);

  // --------------------------------------------------------------------------
  // helpers
  // --------------------------------------------------------------------------
  localparam logic [31:0] DmHaltPc = DmHaltAddr;
  localparam logic [31:0] DmExcPc  = DmExcAddr;

  logic st_decode, st_cmt_flush, st_wait_cmt0, st_issue, st_wait_final;
  logic st_wait_cmplx, st_sleep;
  assign st_decode     = ctrl_fsm_cs[CSM_DECODE];
  assign st_cmt_flush  = ctrl_fsm_cs[CSM_CMT_FLUSH];
  assign st_wait_cmt0  = ctrl_fsm_cs[CSM_WAIT_CMT0];
  assign st_issue      = ctrl_fsm_cs[CSM_ISSUE_SPECIAL];
  assign st_wait_final = ctrl_fsm_cs[CSM_WAIT_FINAL];
  assign st_wait_cmplx = ctrl_fsm_cs[CSM_WAIT_CMPLX];
  assign st_sleep      = ctrl_fsm_cs[CSM_SLEEP];

  logic do_exec, do_irq, do_debug, do_sysctl, do_cmplx, do_step;
  assign do_exec   = st_issue && (special_case_q == EXEC);
  assign do_irq    = st_issue && (special_case_q == IRQ);
  assign do_debug  = st_issue && (special_case_q == DEBUG);
  assign do_sysctl = st_issue && (special_case_q == SYSCTL);
  assign do_cmplx  = st_issue && (special_case_q == CMPLX);
  assign do_step   = st_issue && (special_case_q == STEP);

  logic        m_trap;      // trap recorded in mcause/mepc (not debug entry, not in debug mode)
  logic [5:0]  mcause;
  logic [31:0] mtval, epc;
  assign m_trap = csr_save_cause_o && !debug_csr_save_o && !debug_mode_q;
  assign mcause = csr_exc_info_o.mcause;
  assign mtval  = csr_exc_info_o.mtval;
  assign epc    = csr_exc_info_o.pc[31:0];

  // next sequential/predicted pc after an IR entry (mirrors the IF prediction)
  function automatic logic [31:0] pred_nxt_pc(ir_dec_t d);
    if ((d.is_branch || d.is_jal || d.is_jalr) && d.ptaken) return d.ptarget[31:0];
    else                                                    return d.pc_nxt;
  endfunction

  function automatic logic cause_legal(logic [5:0] c);
    if (c[5])
      return (c[4:0] == 5'd3) || (c[4:0] == 5'd7) || (c[4:0] == 5'd11) ||
             (c[4] && (c[3:0] != 4'hf));
    else
      return (c[4:0] inside {5'd1, 5'd2, 5'd3, 5'd4, 5'd5, 5'd6, 5'd7, 5'd8, 5'd11, 5'd28});
  endfunction

  // number of forwarding sources (all pipelines, both stages) matching reg r
  function automatic logic [3:0] fwd_hits(logic [4:0] r, pl_fwd_t f0, pl_fwd_t f1,
                                          pl_fwd_t f2, pl_fwd_t f3);
    return 4'(f0.valid[0] && (f0.addr0 == r)) + 4'(f0.valid[1] && (f0.addr1 == r)) +
           4'(f1.valid[0] && (f1.addr0 == r)) + 4'(f1.valid[1] && (f1.addr1 == r)) +
           4'(f2.valid[0] && (f2.addr0 == r)) + 4'(f2.valid[1] && (f2.addr1 == r)) +
           4'(f3.valid[0] && (f3.addr0 == r)) + 4'(f3.valid[1] && (f3.addr1 == r));
  endfunction

  // source operands actually read by an issued instruction: {ir1.rs2, ir1.rs1, ir0.rs2, ir0.rs1}
  logic [3:0]      opnd_use;
  logic [3:0][4:0] opnd_addr;
  logic [3:0][3:0] opnd_hits;
  logic [3:0]      opnd_rsv;
  logic [31:0]     wrsv_full;
  assign wrsv_full   = {reg_wrsv_q, 1'b0};
  assign opnd_addr   = {ir1_dec.rs2, ir1_dec.rs1, ir0_dec.rs2, ir0_dec.rs1};
  assign opnd_use[0] = ir0_issued && ir0_dec.rf_ren[0] && (ir0_dec.rs1 != 5'd0);
  assign opnd_use[1] = ir0_issued && ir0_dec.rf_ren[1] && (ir0_dec.rs2 != 5'd0);
  assign opnd_use[2] = ir1_issued && ir1_dec.rf_ren[0] && (ir1_dec.rs1 != 5'd0);
  assign opnd_use[3] = ir1_issued && ir1_dec.rf_ren[1] && (ir1_dec.rs2 != 5'd0);
  for (genvar k = 0; k < 4; k++) begin : g_opnd
    assign opnd_hits[k] = fwd_hits(opnd_addr[k], alupl0_fwd_info_i, alupl1_fwd_info_i,
                                   lspl_fwd_info_i, multpl_fwd_info_i);
    assign opnd_rsv[k]  = wrsv_full[opnd_addr[k]];
  end

  // instructions issued since single-stepping resumed (saturating)
  logic [1:0] step_cnt_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)
      step_cnt_q <= 2'd0;
    else if (debug_mode_q || !debug_step_i)
      step_cnt_q <= 2'd0;
    else if (step_cnt_q != 2'd3)
      step_cnt_q <= step_cnt_q + 2'(ir0_issued) + 2'(ir1_issued);
  end

  // --------------------------------------------------------------------------
  // pc tracking and redirects
  // --------------------------------------------------------------------------

  // rtl/issuer.sv:889-899 -- ir0_nxt_pc_q is the address of the next instruction; a valid IR0 must be it (mepc/dpc source)
  AssertIr0PcTracksNxtPc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ir_valid_i[0] |-> (ir0_dec.pc == ir0_nxt_pc_q));

  // rtl/issuer.sv:880-887 -- IR1 is the (predicted) successor of IR0, which resolve_nxt_pc assumes.
  // Excluded: a jalr whose RA prediction was revoked in IR (ir_stage.sv:197-207 clears ptaken but IF already
  // fetched from the stale target); branch_unit.sv:92 always flags it mispredicted, so IR1 is squashed.
  // kudu_sva_id.ir_fifo_x: simulation-only X taint of the IR FIFOs (0 in FV).
  AssertIr1PcFollowsIr0: assert property (@(posedge clk_i)
    disable iff (!rst_ni || $sampled(kudu_top.ir_stage_i.u_fcov_sva_id.ir_fifo_x))
    (ir_valid_i[1] && !$isunknown({ir0_dec.is_branch, ir0_dec.is_jal, ir0_dec.is_jalr, ir0_dec.ptaken}) &&
     !(ir0_dec.is_jalr && !ir0_dec.ptaken)) |-> kudu_fcov_pkg::sva_xok((ir1_dec.pc == pred_nxt_pc(ir0_dec))));

  // rtl/issuer.sv:633-667 -- every fetch redirect (trap vector, mepc, dpc, branch/jalr target) is halfword aligned
  AssertPcTargetEven: assert property (@(posedge clk_i) disable iff (!rst_ni)
    pc_set_o |-> !pc_target_o[0]);

  // rtl/issuer.sv:817-845,961 -- a trap redirects to dm halt (debug entry / ebreak in debug), dm exception (debug mode) or mtvec
  AssertTrapRedirect: assert property (@(posedge clk_i) disable iff (!rst_ni)
    csr_save_cause_o |-> pc_set_o &&
      (pc_target_o == (debug_csr_save_o                    ? DmHaltPc :
                       (debug_mode_q && do_sysctl && sysctl_q.ebrk) ? DmHaltPc :
                       debug_mode_q                        ? DmExcPc  :
                                                             {csr_mtvec_i[31:2], 2'b00})));

  // rtl/issuer.sv:961-1026 -- issuer-side traps save the pc of the next unexecuted instruction (faulting instr / IRQ / debug resume)
  AssertTrapPcIsNxtPc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (csr_save_cause_o && st_issue) |-> (epc == ir0_nxt_pc_q));

  // rtl/issuer.sv:848,933 -- mret only from M-mode and resumes at mepc
  AssertMretRedirect: assert property (@(posedge clk_i) disable iff (!rst_ni)
    csr_restore_mret_o |-> (priv_mode_i == PRIV_LVL_M) && pc_set_o && (pc_target_o == csr_mepc_i) &&
                           !csr_save_cause_o);

  // rtl/issuer.sv:849,934 -- dret only in debug mode and resumes at dpc
  AssertDretRedirect: assert property (@(posedge clk_i) disable iff (!rst_ni)
    csr_restore_dret_o |-> debug_mode_q && pc_set_o && (pc_target_o == csr_depc_i) &&
                           !csr_save_cause_o);

  // rtl/issuer.sv:840-856 -- sysctl redirects exactly for ebreak/ecall/mret/dret/fence.i; fence.i goes to the next pc
  AssertSysctlRedirect: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_sysctl |-> (pc_set_o == (sysctl_q.ebrk || sysctl_q.ecall || sysctl_q.mret ||
                                sysctl_q.dret || sysctl_q.fencei)) &&
                  (!sysctl_q.fencei || (pc_target_o == ir0_dec.pc_nxt)));

  // rtl/issuer.sv:859-864 -- a stepped instruction is resolved like a normal issue (redirect iff mispredicted)
  AssertStepRedirect: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_step |-> (pc_set_o == mispredict[0]) && (!pc_set_o || (pc_target_o == ir0_target)));

  // rtl/issuer.sv:305,640-647 -- an issued mispredicted branch redirects to its resolved target and squashes any younger issue
  AssertMispredictRedirect: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ((ir0_issued && mispredict[0]) |-> pc_set_o && (pc_target_o == ir0_target) && !ir1_issued) and
    ((ir1_issued && mispredict[1]) |-> pc_set_o && (pc_target_o == ir1_target)));

  // --------------------------------------------------------------------------
  // debug entry / exit
  // --------------------------------------------------------------------------

  // rtl/issuer.sv:908-912,963-966 -- debug mode is entered exactly by a debug save (dcsr/dpc written)
  AssertDebugEntry: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (debug_csr_save_o |-> !debug_mode_q ##1 debug_mode_q) and
    ($rose(debug_mode_q) |-> $past(debug_csr_save_o)));

  // rtl/issuer.sv:911-912,934 -- debug mode is left only through dret
  AssertDebugExit: assert property (@(posedge clk_i) disable iff (!rst_ni)
    $fell(debug_mode_q) |-> $past(csr_restore_dret_o));

  // rtl/issuer.sv:968-976 -- debug entry always records a defined dcsr.cause
  AssertDebugCauseValid: assert property (@(posedge clk_i) disable iff (!rst_ni)
    debug_csr_save_o |-> (debug_cause_o inside {DBG_CAUSE_EBREAK, DBG_CAUSE_TRIGGER,
                                                DBG_CAUSE_HALTREQ, DBG_CAUSE_STEP}));

  // rtl/issuer.sv:917-922,968-976 -- a completed step (step_req_q set before the decision) halts with cause STEP unless haltreq
  AssertDebugCauseStep: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (debug_csr_save_o && $past(step_req_q) && !debug_req_i) |-> (debug_cause_o == DBG_CAUSE_STEP));

  // rtl/issuer.sv:735,750-758,917-922 -- with dcsr.step set, at most one instruction issues before debug mode is re-entered
  AssertStepSingleInstr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (debug_step_i && !debug_mode_q) |-> ((3'(step_cnt_q) + 3'(ir0_issued) + 3'(ir1_issued)) <= 3'd1));

  // --------------------------------------------------------------------------
  // trap causes, interrupts
  // --------------------------------------------------------------------------

  // rtl/issuer.sv:961-1026, committer.sv:198-205 -- mcause is a defined cause; ecall cause matches the privilege
  AssertTrapCauseLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_trap |-> cause_legal(mcause) &&
               ((mcause != 6'(EXC_CAUSE_ECALL_UMODE)) || (priv_mode_i == PRIV_LVL_U)) &&
               ((mcause != 6'(EXC_CAUSE_ECALL_MMODE)) || (priv_mode_i == PRIV_LVL_M)));

  // rtl/issuer.sv:979-1026 -- mtval rules: 0 for interrupts, pc for ebreak, pc/pc+2 for fetch faults,
  // 0 for illegal insn in CHERI mode, CHERI fault mtval has a nonzero cause code and no high bits
  AssertTrapMtvalLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_trap |-> (!mcause[5] || (mtval == 32'h0)) &&
               ((mcause != 6'(EXC_CAUSE_BREAKPOINT)) || (mtval == epc)) &&
               ((mcause != 6'(EXC_CAUSE_INSTR_ACCESS_FAULT)) || (mtval == epc) || (mtval == epc + 32'd2)) &&
               ((mcause != 6'(EXC_CAUSE_ILLEGAL_INSN)) || !(CHERIoTEn && cheri_pmode_i) || (mtval == 32'h0)) &&
               ((mcause != 6'(EXC_CAUSE_CHERI_FAULT)) || ((mtval[31:11] == '0) && (mtval[4:0] != 5'h0))));

  // rtl/issuer.sv:1004-1018 -- the reported interrupt cause is a line that is pending and enabled
  AssertIrqCauseIsPending: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_irq |-> mcause[5] &&
      ((mcause[4] && (mcause[3:0] != 4'hf) && irqs_i.irq_fast[mcause[3:0]]) ||
       ((mcause == 6'(EXC_CAUSE_IRQ_EXTERNAL_M)) && irqs_i.irq_external) ||
       ((mcause == 6'(EXC_CAUSE_IRQ_SOFTWARE_M)) && irqs_i.irq_software) ||
       ((mcause == 6'(EXC_CAUSE_IRQ_TIMER_M))    && irqs_i.irq_timer)));

  // rtl/issuer.sv:737-738,833-838 -- an interrupt is taken only if pending, globally enabled for the current
  // privilege, and not in debug mode or stepping
  AssertIrqTakenLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_irq |-> irq_pending_i && (csr_mstatus_mie_i || (priv_mode_i != PRIV_LVL_M)) &&
               !debug_mode_q && !debug_step_i);

  // cs_registers.sv:761-785 via rtl/issuer.sv:939 -- every trap enters M-mode; a recorded trap also clears mstatus.mie
  AssertTrapEntersMmode: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (csr_save_cause_o |=> (priv_mode_i == PRIV_LVL_M)) and
    (m_trap |=> !csr_mstatus_mie_i));

  // --------------------------------------------------------------------------
  // special issue: serialization and drain
  // --------------------------------------------------------------------------

  // rtl/issuer.sv:563-573,817-866 -- the IR0 acted on in ISSUE_SPECIAL is the one the WAIT_CMT0 decision was made on
  AssertSpecialIr0Stable: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (do_exec || do_sysctl || do_cmplx || do_step) |->
      ir_valid_i[0] && $stable(ir0_dec.pc) && $stable(ir0_dec.insn));

  // rtl/issuer.sv:717-747,788-805 -- the latched special case still matches IR0 when it is executed
  AssertSpecialCaseMatchesIr0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (do_exec   |-> (ir_any_err[0] || ir0_mode_err)) and
    (do_sysctl |-> !ir_any_err[0] && !ir0_mode_err && (ir0_dec.sysctl == sysctl_q) && sysctl_q.valid) and
    (do_cmplx  |-> RV32A && !ir_any_err[0] && ir0_dec.is_cmplx) and
    (do_step   |-> !ir_any_err[0] && !ir0_mode_err && !ir0_dec.sysctl.valid &&
                   !(RV32A && ir0_dec.is_cmplx) && debug_step_i && !debug_mode_q));

  // rtl/issuer.sv:563-573,760 -- special issue (no hazard check) happens only with everything older retired:
  // scoreboard empty, no register / load-filter reservation, no revocation in flight, no commit error
  AssertSpecialDrained: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (st_issue || st_sleep) |-> !sbdfifo_rd_valid_i[0] && !trvk_outstanding_i && !cmt_err_i &&
                               (reg_wrsv_q == '0) && (reg_cheri_trsv_q == '0));

  // rtl/issuer.sv:313-316,760 -- an issued instruction is accepted by every EX pipeline it selects
  AssertIssuedPlReady: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (ir0_issued |-> ((ir0_pl_sel[4:1] & ~ex_rdy[4:1]) == 4'h0)) and
    (ir1_issued |-> ((ir1_pl_sel[4:1] & ~ex_rdy[4:1]) == 4'h0)));

  // rtl/issuer.sv:294 -- an EX pipeline only takes (valid & ready) an instruction that is popped from IR
  AssertExAcceptImpliesIssue: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ((ex_valid_o[4:1] & ex_rdy[4:1] &
      ~(({4{ir0_issued}} & ir0_pl_sel[4:1]) | ({4{ir1_issued}} & ir1_pl_sel[4:1]))) == 4'h0));

  // rtl/issuer.sv:349-352,750-758 -- scoreboard FIFO is never written beyond its free space (incl. special/cmplx writes)
  AssertSbdWrNoOverflow: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ((sbdfifo_wr_valid_o & ~sbdfifo_wr_rdy_i) == 2'b00));

  // rtl/issuer.sv:351-356 -- complex-unit scoreboard writes happen only during the AMO and never collide with an issue write
  AssertCmplxSbdWr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cmplx_sbd_wr_i |-> (st_issue || st_wait_cmplx) && (ir_fifo_wr == 2'b00));

  // rtl/issuer.sv:766, cmplx_unit.sv:85-91 -- the cmplx FSM leaves IDLE without checking lspl_rdy, so LSPL must be ready at start
  AssertCmplxStartLsplRdy: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cmplx_instr_start_o |-> lspl_rdy_i);

  // rtl/issuer.sv:535-606,961 -- a commit error is only seen in states that handle it, and CMT_FLUSH always saves it
  AssertCmtErrState: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (cmt_err_i |-> (st_decode || st_wait_cmt0 || st_wait_final || st_wait_cmplx || st_cmt_flush)) and
    (st_cmt_flush |-> cmt_err_i && csr_save_cause_o));

  // rtl/issuer.sv:444-457 -- a register write reservation implies an instruction still in the scoreboard
  AssertWrsvInflight: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (reg_wrsv_q != '0) |-> sbdfifo_rd_valid_i[0] || cmt_err_i);

  // rtl/issuer.sv:480-494 -- a load-filter reservation implies the clc is in the scoreboard or in the revocation pipe
  AssertTrsvInflight: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (reg_cheri_trsv_q != '0) |-> sbdfifo_rd_valid_i[0] || trvk_outstanding_i || cmt_err_i);

  // --------------------------------------------------------------------------
  // dual issue and forwarding
  // --------------------------------------------------------------------------

  // rtl/issuer.sv:411-427 -- IR1 never issues with IR0 if it reads or writes IR0's destination
  AssertIr1NoDepOnIr0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (ir1_issued && ir0_dec.rf_we && (ir0_dec.rd != 5'd0)) |->
      !(ir1_dec.rf_ren[0] && (ir1_dec.rs1 == ir0_dec.rd)) &&
      !(ir1_dec.rf_ren[1] && (ir1_dec.rs2 == ir0_dec.rd)) &&
      !(ir1_dec.rf_we && (ir1_dec.rd == ir0_dec.rd)));

  // rtl/issuer.sv:407-426 -- an issued operand whose register is still reserved is supplied by a forwarding source
  AssertRsvOperandForwarded: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ((opnd_use & opnd_rsv & {opnd_hits[3] == 4'd0, opnd_hits[2] == 4'd0,
                            opnd_hits[1] == 4'd0, opnd_hits[0] == 4'd0}) == 4'h0));

  // rtl/issuer.sv:163-195 -- fwd_lookup ORs all matches, so an issued operand must match at most one source
  AssertFwdSingleSource: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ((opnd_use & {opnd_hits[3] > 4'd1, opnd_hits[2] > 4'd1,
                  opnd_hits[1] > 4'd1, opnd_hits[0] > 4'd1}) == 4'h0));

  // rtl/issuer.sv:318-328 -- the IR1 pop (shadow logic without mispredict[0]) only pops an issued or flushed IR1
  AssertIr1PopIssuedOrFlushed: assert property (@(posedge clk_i) disable iff (!rst_ni)
    issuer_rdy_o[1] |-> issuer_rdy_o[0] && (ir1_issued || pc_set_o));

  // rtl/issuer.sv:729-758 -- normal (hazard-checked) issue never bypasses a pending trap, interrupt, debug event or
  // serializing instruction
  AssertNormalIssueNoPendingEvent: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (ir0_normal_issued |-> st_decode && !cmt_err_i && !ir_any_err[0] && !ir0_mode_err &&
                           !ir0_dec.sysctl.valid && !(RV32A && ir0_dec.is_cmplx) &&
                           (debug_mode_q || !(debug_req_i || debug_step_i || step_req_q || ir0_dec.is_brkpt)) &&
                           !(irq_pending_i && (csr_mstatus_mie_i || (priv_mode_i != PRIV_LVL_M)) &&
                             !debug_mode_q && !debug_step_i)) and
    (ir1_issued |-> !ir_any_err[1] && !ir1_dec.sysctl.valid && !(RV32A && ir1_dec.is_cmplx) &&
                    !ir1_dec.is_brkpt && !debug_step_i));

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

// kudu_fvh_issue_fwd (was fv/help_ifc.sv, bound into kudu_top as
// u_fvh_issue_fwd). Supports the issue/forwarding/complex-unit targets:
// kudu_sva_issue AssertCmplxStartLsplRdy / AssertFwdSingleSource /
// AssertIssuedPlReady / AssertRsvOperandForwarded, kudu_sva_cmplx
// AssertSvaCmplxCapture / RdAccept / WrData and kudu_sva_lsu
// AssertAmoWriteFollowsGoodRead / AssertAmoWriteReturnsReadData.
//
// FV helper lemmas for the issue_fwd_cmplx area (bound into kudu_top).
module kudu_fvh_issue_fwd import super_pkg::*; (
  input logic clk_i,
  input logic rst_ni
);

  // ---------------------------------------------------------------- forwarding
  pl_fwd_t f_a0, f_a1, f_ls, f_mu;
  assign f_a0 = kudu_top.alupl0_fwd_info;
  assign f_a1 = kudu_top.alupl1_fwd_info;
  assign f_ls = kudu_top.lspl_fwd_info;
  assign f_mu = kudu_top.multpl_fwd_info;

  logic       m2_live;
  logic [4:0] m2_rd;
  assign m2_live = kudu_top.mult_pipeline_i.ex2_valid & kudu_top.mult_pipeline_i.ex2_fwd_ok &
                   kudu_top.mult_pipeline_i.ex2_reg.rf_we;
  assign m2_rd   = kudu_top.mult_pipeline_i.ex2_reg.rd;

  // dcache waw-tracking fifo entries that are still live writers
  logic [3:0]      df_live;
  logic [3:0][4:0] df_rd;
  logic [2:0]      df_cnt;
  assign df_cnt = kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.wr_ptr_q -
                  kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.rd_ptr_q;
  for (genvar k = 0; k < 4; k++) begin : g_df
    logic [1:0] idx;
    logic [5:0] e;
    assign idx = kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.rd_ptr_q[1:0] + 2'(k);
    assign e   = kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.fifo_mem[idx];
    assign df_live[k] = (3'(k) < df_cnt) && e[5];
    assign df_rd[k]   = e[4:0];
  end

  // live forwarding/writer slots: a0 wb, a1 wb, mult wb, dcache, mult ex2, dcache fifo[0..3]
  logic [8:0]      lv;
  logic [8:0][4:0] la;
  assign lv = {df_live, m2_live, f_ls.valid[1], f_mu.valid[1], f_a1.valid[1], f_a0.valid[1]};
  assign la = {df_rd, m2_rd, f_ls.addr1, f_mu.addr1, f_a1.addr1, f_a0.addr1};

  logic pair_ok, pair_ok_nf, pair_ok_all;
  always_comb begin
    pair_ok = 1'b1;
    pair_ok_nf = 1'b1;
    pair_ok_all = 1'b1;
    for (int i = 0; i < 9; i++)
      for (int j = i + 1; j < 9; j++)
        if (lv[i] && lv[j] && (la[i] == la[j]) && (la[i] != 5'd0) && !((i >= 5) && (j >= 5))) begin
          pair_ok = 1'b0;
          if (j < 5) pair_ok_nf = 1'b0;
        end
    for (int i = 0; i < 9; i++)
      for (int j = i + 1; j < 9; j++)
        if (lv[i] && lv[j] && (la[i] == la[j]) && (la[i] != 5'd0)) pair_ok_all = 1'b0;
  end

  // only the stage-1 (wb) forwarding slot is ever used
  HlpFwdV0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !f_a0.valid[0] && !f_a1.valid[0] && !f_ls.valid[0] && !f_mu.valid[0]);

  // no two live writers (fwd slots, mult ex2, dcache waw fifo) of the same rd
  HlpFwdPair: assert property (@(posedge clk_i) disable iff (!rst_ni) pair_ok);

  // weaker: only among the forwarding slots + mult ex2
  HlpFwdPairNf: assert property (@(posedge clk_i) disable iff (!rst_ni) pair_ok_nf);

  // RsvOperandForwarded restricted to the hazard-checked (normal) issue path
  logic [3:0] use_n;
  assign use_n = kudu_top.issuer_i.u_fcov_sva_issue.opnd_use &
                 {2'b11, {2{~kudu_top.issuer_i.ir0_special_issued}}};
  HlpRsvNormal: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ((use_n & kudu_top.issuer_i.u_fcov_sva_issue.opnd_rsv &
      {kudu_top.issuer_i.u_fcov_sva_issue.opnd_hits[3] == 4'd0,
       kudu_top.issuer_i.u_fcov_sva_issue.opnd_hits[2] == 4'd0,
       kudu_top.issuer_i.u_fcov_sva_issue.opnd_hits[1] == 4'd0,
       kudu_top.issuer_i.u_fcov_sva_issue.opnd_hits[0] == 4'd0}) == 4'h0));

  // special issue never sees a register reservation
  HlpRsvSpecial: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ir0_special_issued |-> kudu_top.issuer_i.reg_wrsv_q == '0);

  // special issue: every EX pipeline is ready
  logic [4:0] exr;
  assign exr = kudu_top.issuer_i.ex_rdy;
  HlpSpecialRdy: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ir0_special_issued |-> exr[4:1] == 4'hf);

  // ---------------------------------------------------------------- cmplx
  logic [1:0] cfsm;
  logic       c_busy, c_rdok;
  assign cfsm   = 2'(kudu_top.comlx_unit_i.cmplx_fsm_cs);
  assign c_busy = kudu_top.comlx_unit_i.u_fcov_sva_cmplx.busy_q;
  assign c_rdok = kudu_top.comlx_unit_i.u_fcov_sva_cmplx.rd_ok_q;

  HlpCmplxBusy: assert property (@(posedge clk_i) disable iff (!rst_ni)
    c_busy == (cfsm != 2'd0));
  HlpCmplxRdOk: assert property (@(posedge clk_i) disable iff (!rst_ni)
    c_rdok == (cfsm[1]));
  HlpCmplxTrk: assert property (@(posedge clk_i) disable iff (!rst_ni)
    c_busy |->
      kudu_top.comlx_unit_i.ir_dec_q.insn[31:27] == kudu_top.comlx_unit_i.u_fcov_sva_cmplx.t_op_q &&
      kudu_top.comlx_unit_i.ir_dec_q.rd == kudu_top.comlx_unit_i.u_fcov_sva_cmplx.t_rd_q &&
      kudu_top.comlx_unit_i.ir_full_data2_q.d0[31:0] == kudu_top.comlx_unit_i.u_fcov_sva_cmplx.t_addr_q &&
      kudu_top.comlx_unit_i.ir_full_data2_q.d1[31:0] == kudu_top.comlx_unit_i.u_fcov_sva_cmplx.t_rs2_q);
  HlpCmplxRdata: assert property (@(posedge clk_i) disable iff (!rst_ni)
    c_rdok |-> kudu_top.comlx_unit_i.amo_rdata_q == kudu_top.comlx_unit_i.u_fcov_sva_cmplx.t_rdata_q);

  // ---------------------------------------------------------------- lsu / amo
  logic [2:0]    lsif;
  logic          dly_v, outst, csrq;
  lsu_req_info_t dly_q, hold_q, lq;
  assign lsif  = 3'(kudu_top.ls_pipeline_i.lsu_if_i.lsif_fsm_q);
  assign dly_v = kudu_top.ls_pipeline_i.lsu_if_i.req_dly_valid;
  assign dly_q = kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q;
  assign hold_q = kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q;
  assign lq    = kudu_top.ls_pipeline_i.load_store_unit_i.lsu_req_info_q;
  assign outst = kudu_top.ls_pipeline_i.load_store_unit_i.outstanding_resp_q;
  assign csrq  = kudu_top.ls_pipeline_i.load_store_unit_i.csr_go_q;

  logic          m_ok;
  logic [31:0]   m_ra, m_rdat;
  assign m_ok  = kudu_top.ls_pipeline_i.u_fcov_sva_lsu.m_amo_rd_ok;
  assign m_ra  = kudu_top.ls_pipeline_i.u_fcov_sva_lsu.m_amo_rd_addr;
  assign m_rdat = kudu_top.ls_pipeline_i.u_fcov_sva_lsu.m_amo_rd_data;

  logic          pend_dly, pend_hold;
  assign pend_dly  = (lsif == 3'd2) && dly_v;
  assign pend_hold = (lsif == 3'd1) || (lsif == 3'd3);
  // a held request the LSU has not yet taken (ls_go only happens with the LSU FSM idle)
  logic ls_idle, pend_hng;
  assign ls_idle  = kudu_top.ls_pipeline_i.load_store_unit_i.ls_fsm_cs == '0;
  assign pend_hng = pend_hold && ls_idle;

  HlpLsuShadow: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.ls_pipeline_i.u_fcov_sva_lsu.m_amo == lq.amo_flag &&
    kudu_top.ls_pipeline_i.u_fcov_sva_lsu.m_is_load == lq.is_load &&
    kudu_top.ls_pipeline_i.u_fcov_sva_lsu.m_addr == lq.addr);
  HlpAmoOkIdle: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_ok |-> !outst);
  HlpAmoOkData: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_ok |-> kudu_top.ls_pipeline_i.load_store_unit_i.amo_rdata_q == m_rdat);
  HlpAmoWrOutData: assert property (@(posedge clk_i) disable iff (!rst_ni)
    outst && !csrq && lq.amo_flag[3] |->
      kudu_top.ls_pipeline_i.load_store_unit_i.amo_rdata_q == m_rdat);

  // a pending AMO write request in lsu_if comes after a good AMO read of the same address
  HlpAmoWrPendDly: assert property (@(posedge clk_i) disable iff (!rst_ni)
    pend_dly && dly_q.amo_flag[3] |-> m_ok && (m_ra == dly_q.addr));
  HlpAmoWrPendHold: assert property (@(posedge clk_i) disable iff (!rst_ni)
    pend_hng && hold_q.amo_flag[3] |-> m_ok && (m_ra == hold_q.addr));
  // cmplx in AMO_WRITE: good read of rs1 recorded, nothing else pending in lsu_if / LSU
  HlpAmoWrState: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cfsm == 2'd2 |-> m_ok && (m_ra == kudu_top.comlx_unit_i.ir_full_data2_q.d0[31:0]) &&
                     !outst && !pend_hold && !pend_dly);
  // AMO write requests only exist while the cmplx unit is writing
  HlpAmoWrSrc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ((pend_dly && dly_q.amo_flag[3]) || (pend_hng && hold_q.amo_flag[3])) |-> cfsm == 2'd3);

  // lsu_if wait-for-grant states only with a scoreboard entry or an AMO in flight
  HlpLsifWgnt: assert property (@(posedge clk_i) disable iff (!rst_ni)
    pend_hold |-> kudu_top.sbdfifo_rd_valid[0] || (cfsm != 2'd0));


  // ---------------------------------------------------------------- register write reservations
  // ls_pipeline waw fifo (Depth 8): live LS writers between issue and commit
  logic [3:0]      lw_cnt;
  logic [7:0]      lw_live;
  logic [7:0][4:0] lw_rd;
  assign lw_cnt = kudu_top.ls_pipeline_i.waw_fifo_i.wr_ptr_q - kudu_top.ls_pipeline_i.waw_fifo_i.rd_ptr_q;
  for (genvar k = 0; k < 8; k++) begin : g_lw
    logic [2:0] idx;
    logic [5:0] e;
    assign idx = kudu_top.ls_pipeline_i.waw_fifo_i.rd_ptr_q[2:0] + 3'(k);
    assign e   = kudu_top.ls_pipeline_i.waw_fifo_i.fifo_mem[idx];
    assign lw_live[k] = (4'(k) < lw_cnt) && e[5];
    assign lw_rd[k]   = e[4:0];
  end

  logic [31:1] wr_live;
  always_comb begin
    for (int r = 1; r < 32; r++) begin
      wr_live[r] = (f_a0.valid[1] && f_a0.addr1 == 5'(r)) || (f_a1.valid[1] && f_a1.addr1 == 5'(r)) ||
                   (f_mu.valid[1] && f_mu.addr1 == 5'(r)) || (m2_live && m2_rd == 5'(r));
      for (int k = 0; k < 8; k++)
        if (lw_live[k] && lw_rd[k] == 5'(r)) wr_live[r] = 1'b1;
    end
  end

  // a reserved register has a live (not WAW-cancelled) writer in some pipeline
  HlpWrsvLive: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ((kudu_top.issuer_i.reg_wrsv_q & ~wr_live) == '0) || kudu_top.issuer_i.cmt_err_i);

  // ---------------------------------------------------------------- scoreboard occupancy per pipeline
  logic [3:0] sbd_n;
  logic [4:0][3:0] cnt;
  assign sbd_n = kudu_top.sbd_fifo_i.wr_ptr_q - kudu_top.sbd_fifo_i.rd_ptr_q;
  always_comb begin
    sbd_fifo_t e;
    logic [2:0] idx;
    cnt = '0;
    for (int unsigned k = 0; k < 8; k++) begin
      idx = kudu_top.sbd_fifo_i.rd_ptr_q[2:0] + k[2:0];
      e   = sbd_fifo_t'(kudu_top.sbd_fifo_i.fifo_mem[idx]);
      if (k < 32'(sbd_n))
        for (int j = 0; j < 5; j++) cnt[j] = cnt[j] + 4'(e.pl[j]);
    end
  end

  logic a0_wbv, a1_wbv, m_ex2v, m_wbv, ls_busy;
  assign a0_wbv = kudu_top.alu_pipeline0_i.wb_valid;
  assign a1_wbv = kudu_top.alu_pipeline1_i.wb_valid;
  assign m_ex2v = kudu_top.mult_pipeline_i.ex2_valid;
  assign m_wbv  = kudu_top.mult_pipeline_i.wb_valid;
  assign ls_busy = pend_dly || pend_hold || outst || kudu_top.lspl_valid ||
                   (kudu_top.ls_pipeline_i.load_store_unit_i.ls_fsm_cs != '0) || (lw_cnt != 4'd0);

  HlpSbdA0: assert property (@(posedge clk_i) disable iff (!rst_ni) cnt[1] == 4'(a0_wbv));
  HlpSbdA1: assert property (@(posedge clk_i) disable iff (!rst_ni) cnt[2] == 4'(a1_wbv));
  HlpSbdM:  assert property (@(posedge clk_i) disable iff (!rst_ni) cnt[4] == 4'(m_ex2v) + 4'(m_wbv));
  HlpSbdMge: assert property (@(posedge clk_i) disable iff (!rst_ni) (m_ex2v || m_wbv) |-> cnt[4] != 0);
  HlpSbdA0ge: assert property (@(posedge clk_i) disable iff (!rst_ni) a0_wbv |-> cnt[1] != 0);
  HlpSbdA1ge: assert property (@(posedge clk_i) disable iff (!rst_ni) a1_wbv |-> cnt[2] != 0);
  HlpSbdLs: assert property (@(posedge clk_i) disable iff (!rst_ni) ls_busy |-> cnt[3] != 0);
  // the cmplx unit is only busy while the issuer waits for it
  HlpCmplxIssuer: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (cfsm != 2'd0) |-> kudu_top.issuer_i.u_fcov_sva_issue.st_wait_cmplx ||
                       kudu_top.issuer_i.u_fcov_sva_issue.st_cmt_flush);

  // ---------------------------------------------------------------- drain / operand stability
  logic sbd_v, st_w0, st_is;
  assign sbd_v = kudu_top.sbdfifo_rd_valid[0];
  assign st_w0 = kudu_top.issuer_i.u_fcov_sva_issue.st_wait_cmt0;
  assign st_is = kudu_top.issuer_i.u_fcov_sva_issue.st_issue;

  // register file writes only come from committing scoreboard entries
  HlpRfWeSbd: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.rf_we0 || kudu_top.rf_we1 || kudu_top.rf_we2) |-> sbd_v);
  // a valid dcache (LS) forwarding slot belongs to an LS instruction still in the scoreboard
  HlpDcFwdLs: assert property (@(posedge clk_i) disable iff (!rst_ni)
    f_ls.valid[1] |-> cnt[3] != 4'd0);
  // empty scoreboard: no forwarding source is valid
  HlpNoFwdEmpty: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !sbd_v |-> !f_a0.valid[1] && !f_a1.valid[1] && !f_mu.valid[1] && !f_ls.valid[1]);
  logic c_start;
  assign c_start = kudu_top.comlx_unit_i.cmplx_instr_start_i;
  // cmplx start: the scoreboard was and still is empty
  HlpStartSbdEmpty: assert property (@(posedge clk_i) disable iff (!rst_ni)
    c_start |-> !sbd_v && $past(!sbd_v));
  // WAIT_CMT0 -> ISSUE_SPECIAL(CMPLX) keeps the IR0 instruction
  HlpCapIr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    c_start |->
      $stable(kudu_top.comlx_unit_i.u_fcov_sva_cmplx.cur_dec.insn) &&
      $stable(kudu_top.comlx_unit_i.u_fcov_sva_cmplx.cur_dec.pc) &&
      $stable(kudu_top.comlx_unit_i.u_fcov_sva_cmplx.cur_dec.rd));
  // WAIT_CMT0 -> ISSUE_SPECIAL(CMPLX) keeps the IR0 operand values
  HlpCapData: assert property (@(posedge clk_i) disable iff (!rst_ni)
    c_start |->
      $stable(kudu_top.comlx_unit_i.u_fcov_sva_cmplx.cur_dat.d0[31:0]) &&
      $stable(kudu_top.comlx_unit_i.u_fcov_sva_cmplx.cur_dat.d1[31:0]));
  // cmplx start only happens in ISSUE_SPECIAL entered from WAIT_CMT0
  HlpStartIs: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.comlx_unit_i.cmplx_instr_start_i |-> st_is && $past(st_w0) && $past(cfsm == 2'd0) &&
                                                  !$past(kudu_top.comlx_unit_i.cmplx_instr_start_i));

  // ---------------------------------------------------------------- joint (mutually inductive) forms
  logic j_wrstate, j_wrsrc, j_pdly, j_phold, j_wgnt, j_a0, j_a1, j_m, j_ls, j_dc, j_ci, j_wl;
  assign j_wrstate = !(cfsm == 2'd2) || (m_ok && (m_ra == kudu_top.comlx_unit_i.ir_full_data2_q.d0[31:0]) &&
                                         !outst && !pend_hold && !pend_dly);
  assign j_wrsrc   = !((pend_dly && dly_q.amo_flag[3]) || (pend_hng && hold_q.amo_flag[3])) || (cfsm == 2'd3);
  assign j_pdly    = !(pend_dly && dly_q.amo_flag[3]) || (m_ok && (m_ra == dly_q.addr));
  assign j_phold   = !(pend_hng && hold_q.amo_flag[3]) || (m_ok && (m_ra == hold_q.addr));
  logic j_wout;
  assign j_wout    = !(outst && !csrq && lq.amo_flag[3]) ||
                     (kudu_top.ls_pipeline_i.load_store_unit_i.amo_rdata_q == m_rdat);
  assign j_wgnt    = !pend_hold || sbd_v || (cfsm != 2'd0);
  assign j_a0      = cnt[1] == 4'(a0_wbv);
  assign j_a1      = cnt[2] == 4'(a1_wbv);
  assign j_m       = cnt[4] == 4'(m_ex2v) + 4'(m_wbv);
  assign j_ls      = !ls_busy || (cnt[3] != 4'd0);
  assign j_dc      = !f_ls.valid[1] || (cnt[3] != 4'd0);
  assign j_ci      = (cfsm == 2'd0) || kudu_top.issuer_i.u_fcov_sva_issue.st_wait_cmplx ||
                     kudu_top.issuer_i.u_fcov_sva_issue.st_cmt_flush;
  assign j_wl      = ((kudu_top.issuer_i.reg_wrsv_q & ~wr_live) == '0) || kudu_top.issuer_i.cmt_err_i;
  // LS occupancy: scoreboard LS entries == ls waw-fifo entries + cmplx LS op in flight
  //               == requests in lsu_if not yet taken + LSU outstanding + wb fifo entries
  logic [3:0] cm_n, lsif_n, wbf_n;
  logic       j_lscnt, j_lsitems;
  assign cm_n   = 4'((cfsm == 2'd1) || (cfsm == 2'd3));
  assign lsif_n = 4'((lsif == 3'd2) && dly_v) + 4'(pend_hng) + 4'((lsif == 3'd3) && dly_v);
  assign wbf_n  = 4'(3'(kudu_top.ls_pipeline_i.wb_fifo_i.wr_ptr_q - kudu_top.ls_pipeline_i.wb_fifo_i.rd_ptr_q));
  assign j_lscnt   = cnt[3] == lw_cnt + cm_n;
  assign j_lsitems = lw_cnt + cm_n == lsif_n + 4'(outst) + wbf_n;
  // scoreboard LS entries match ls waw fifo + cmplx op
  HlpLsCnt: assert property (@(posedge clk_i) disable iff (!rst_ni) j_lscnt);
  // ls waw fifo + cmplx op match the physical LS items in lsu_if / LSU / wb fifo
  HlpLsItems: assert property (@(posedge clk_i) disable iff (!rst_ni) j_lsitems);
  // jointly with the other scoreboard occupancy facts
  HlpJLs: assert property (@(posedge clk_i) disable iff (!rst_ni) j_a0 && j_a1 && j_m && j_lscnt && j_lsitems);

  // a busy LSU FSM always has its response outstanding
  logic j_lbo, j_lw0;
  assign j_lbo = ls_idle || outst;
  HlpLsBusyOut: assert property (@(posedge clk_i) disable iff (!rst_ni) j_lbo);
  // no normal LS instruction in flight while the cmplx unit is busy
  assign j_lw0 = (cfsm == 2'd0) || (lw_cnt == 4'd0);
  HlpCmplxLw0: assert property (@(posedge clk_i) disable iff (!rst_ni) j_lw0);
  // AMO write-path invariants + LS drain facts, jointly
  HlpJAmo2: assert property (@(posedge clk_i) disable iff (!rst_ni)
    j_wrstate && j_wrsrc && j_pdly && j_phold && j_wout && j_lw0 && j_lbo);
  // LS items in age order (wb fifo, LSU outstanding, lsu_if held, lsu_if delayed) and their rd
  logic [7:0][4:0] it_rd;
  logic            j_lsrd;
  always_comb begin
    logic [3:0] n;
    logic [1:0] wi;
    pl_out_t    wo;
    it_rd = '0;
    n     = '0;
    for (int unsigned k = 0; k < 4; k++) begin
      wi = kudu_top.ls_pipeline_i.wb_fifo_i.rd_ptr_q[1:0] + k[1:0];
      wo = pl_out_t'(kudu_top.ls_pipeline_i.wb_fifo_i.fifo_mem[wi]);
      if (4'(k) < wbf_n) begin it_rd[n[2:0]] = wo.waddr; n = n + 4'd1; end
    end
    if (outst)    begin it_rd[n[2:0]] = lq.rd;     n = n + 4'd1; end
    if (pend_hng) begin it_rd[n[2:0]] = hold_q.rd; n = n + 4'd1; end
    if (((lsif == 3'd2) || (lsif == 3'd3)) && dly_v) begin it_rd[n[2:0]] = dly_q.rd; n = n + 4'd1; end
    j_lsrd = 1'b1;
    if (cfsm == 2'd0)
      for (int unsigned k = 0; k < 8; k++)
        if ((4'(k) < lw_cnt) && (lw_rd[k] != it_rd[k])) j_lsrd = 1'b0;
  end
  // the ls waw fifo entries track the rd of the LS items in flight, in order
  HlpLsRd: assert property (@(posedge clk_i) disable iff (!rst_ni) j_lsrd);
  // LS items in flight with a nonzero rd write the register file
  logic [7:0] it_we;
  logic       j_lswe, j_fwb;
  always_comb begin
    logic [3:0] n;
    logic [1:0] wi;
    pl_out_t    wo;
    it_we = '0;
    n     = '0;
    for (int unsigned k = 0; k < 4; k++) begin
      wi = kudu_top.ls_pipeline_i.wb_fifo_i.rd_ptr_q[1:0] + k[1:0];
      wo = pl_out_t'(kudu_top.ls_pipeline_i.wb_fifo_i.fifo_mem[wi]);
      if (4'(k) < wbf_n) begin it_we[n[2:0]] = wo.we; n = n + 4'd1; end
    end
    if (outst)    begin it_we[n[2:0]] = lq.rf_we;     n = n + 4'd1; end
    if (pend_hng) begin it_we[n[2:0]] = hold_q.rf_we; n = n + 4'd1; end
    if (((lsif == 3'd2) || (lsif == 3'd3)) && dly_v) begin it_we[n[2:0]] = dly_q.rf_we; n = n + 4'd1; end
    j_lswe = 1'b1;
    if (cfsm == 2'd0)
      for (int unsigned k = 0; k < 8; k++)
        if ((4'(k) < lw_cnt) && (lw_rd[k] != 5'd0) && !it_we[k]) j_lswe = 1'b0;
  end
  // a valid ALU / mult wb forwarding slot belongs to a valid wb-stage instruction
  assign j_fwb = (!f_a0.valid[1] || a0_wbv) && (!f_a1.valid[1] || a1_wbv) && (!f_mu.valid[1] || m_wbv);
  HlpLsWe: assert property (@(posedge clk_i) disable iff (!rst_ni) j_lswe);
  HlpFwdWb: assert property (@(posedge clk_i) disable iff (!rst_ni) j_fwb);
  // live-writer reservation invariant jointly with LS rd/we alignment and wb-slot validity
  HlpJWl2: assert property (@(posedge clk_i) disable iff (!rst_ni) j_wl && j_lsrd && j_lswe && j_fwb);
  // every live scoreboard entry targets at most one pipeline
  logic j_oh;
  always_comb begin
    sbd_fifo_t e;
    logic [2:0] idx;
    j_oh = 1'b1;
    for (int unsigned k = 0; k < 8; k++) begin
      idx = kudu_top.sbd_fifo_i.rd_ptr_q[2:0] + k[2:0];
      e   = sbd_fifo_t'(kudu_top.sbd_fifo_i.fifo_mem[idx]);
      if ((k < 32'(sbd_n)) && !$onehot0(e.pl[4:1])) j_oh = 1'b0;
    end
  end
  // converse: every live writer of a nonzero rd holds its reservation
  logic j_wlc;
  assign j_wlc = ((wr_live & ~kudu_top.issuer_i.reg_wrsv_q) == '0) || kudu_top.issuer_i.cmt_err_i;
  HlpSbdOh: assert property (@(posedge clk_i) disable iff (!rst_ni) j_oh);
  HlpWrsvConv: assert property (@(posedge clk_i) disable iff (!rst_ni) j_wlc);
  HlpJWl3: assert property (@(posedge clk_i) disable iff (!rst_ni) j_wl && j_lsrd && j_lswe && j_fwb && j_oh);
  HlpJWl4: assert property (@(posedge clk_i) disable iff (!rst_ni) j_wl && j_wlc && j_lsrd && j_lswe && j_fwb && j_oh);
  // live-writer reservation invariant jointly with LS rd alignment
  HlpJWl: assert property (@(posedge clk_i) disable iff (!rst_ni) j_wl && j_lsrd);

  // dcache waw fifo entries track the LS requests not yet done in lsu_if (held, then delayed), in order
  logic [1:0][4:0] dit_rd;
  logic [2:0]      dit_n;
  logic            j_dfrd;
  always_comb begin
    dit_rd = '0;
    dit_n  = '0;
    if (pend_hold) begin dit_rd[0] = hold_q.rd; dit_n = 3'd1; end
    if (((lsif == 3'd2) || (lsif == 3'd3)) && dly_v) begin dit_rd[dit_n[0]] = dly_q.rd; dit_n = dit_n + 3'd1; end
    j_dfrd = (df_cnt == ((cfsm == 2'd0) ? dit_n : 3'd0));
    for (int unsigned k = 0; k < 2; k++)
      if ((3'(k) < df_cnt) && (df_rd[k] != dit_rd[k])) j_dfrd = 1'b0;
  end
  HlpDfRd: assert property (@(posedge clk_i) disable iff (!rst_ni) j_dfrd);
  // forwarding-slot uniqueness jointly with dcache waw fifo alignment
  HlpJFwd: assert property (@(posedge clk_i) disable iff (!rst_ni) pair_ok && j_dfrd);
  // as HlpJFwd, also requiring distinct live dcache waw fifo entries
  HlpJFwd2: assert property (@(posedge clk_i) disable iff (!rst_ni) pair_ok_all && j_dfrd);

  // AMO write-path invariants, jointly
  HlpJAmo: assert property (@(posedge clk_i) disable iff (!rst_ni) j_wrstate && j_wrsrc && j_pdly && j_phold && j_wout);
  // scoreboard occupancy invariants, jointly
  HlpJSbd: assert property (@(posedge clk_i) disable iff (!rst_ni) j_a0 && j_a1 && j_m && j_ls && j_dc && j_wgnt);
  // scoreboard occupancy + live-writer reservation invariants, jointly
  HlpJSbdW: assert property (@(posedge clk_i) disable iff (!rst_ni) j_a0 && j_a1 && j_m && j_ls && j_dc && j_wgnt && j_wl);

endmodule


// kudu_fvh_wrsv (was fv/fv_help_wrsv.sv, bound into kudu_top as u_fvh_wrsv).
// Supports the kudu_sva_issue reservation targets AssertWrsvInflight /
// AssertTrsvInflight (with kudu_fvh_issue_ctrl).
//
// FV helper lemmas: issuer register-write / load-filter reservations vs. in-flight writers.
// Scoreboard-ordered view: sbd position p (0 = oldest) is mapped to the pipeline slot holding it
//   pl[1] -> ALU0 wb, pl[2] -> ALU1 wb, pl[4] -> 1st: mult wb (if valid) else ex2, 2nd: mult ex2,
//   pl[3] -> n-th LS sbd entry == n-th LS waw-fifo entry (only while the cmplx unit is idle).
module kudu_fvh_wrsv import super_pkg::*; (
  input logic clk_i,
  input logic rst_ni
);

  logic [31:1] wrsv;
  logic [15:1] trsv;
  logic        cerr;
  assign wrsv = kudu_top.issuer_i.reg_wrsv_q;
  assign trsv = kudu_top.issuer_i.reg_cheri_trsv_q;
  assign cerr = kudu_top.issuer_i.cmt_err_i;

  logic [1:0] cfsm;
  assign cfsm = 2'(kudu_top.comlx_unit_i.cmplx_fsm_cs);

  // ---------------- pipeline slots
  logic       a0_v, a0_w, a0_l;  logic [4:0] a0_rd;
  logic       a1_v, a1_w, a1_l;  logic [4:0] a1_rd;
  logic       mw_v, mw_w, mw_l;  logic [4:0] mw_rd;
  logic       m2_v, m2_w, m2_l;  logic [4:0] m2_rd;
  assign a0_v  = kudu_top.alu_pipeline0_i.wb_valid;
  assign a0_rd = kudu_top.alu_pipeline0_i.wb_reg.rd;
  assign a0_w  = kudu_top.alu_pipeline0_i.wb_reg.rf_we && (a0_rd != 5'd0);
  assign a0_l  = a0_v && a0_w && kudu_top.alu_pipeline0_i.wb_fwd_valid_q;
  assign a1_v  = kudu_top.alu_pipeline1_i.wb_valid;
  assign a1_rd = kudu_top.alu_pipeline1_i.wb_reg.rd;
  assign a1_w  = kudu_top.alu_pipeline1_i.wb_reg.rf_we && (a1_rd != 5'd0);
  assign a1_l  = a1_v && a1_w && kudu_top.alu_pipeline1_i.wb_fwd_valid_q;
  assign mw_v  = kudu_top.mult_pipeline_i.wb_valid;
  assign mw_rd = kudu_top.mult_pipeline_i.wb_reg.rd;
  assign mw_w  = kudu_top.mult_pipeline_i.wb_reg.rf_we && (mw_rd != 5'd0);
  assign mw_l  = mw_v && mw_w && kudu_top.mult_pipeline_i.wb_fwd_valid_q;
  assign m2_v  = kudu_top.mult_pipeline_i.ex2_valid;
  assign m2_rd = kudu_top.mult_pipeline_i.ex2_reg.rd;
  assign m2_w  = kudu_top.mult_pipeline_i.ex2_reg.rf_we && (m2_rd != 5'd0);
  assign m2_l  = m2_v && m2_w && kudu_top.mult_pipeline_i.ex2_fwd_ok;

  // ls waw fifo (Depth 8), entry k = k-th oldest LS instruction
  logic [3:0]      lw_cnt;
  logic [7:0]      lw_l;
  logic [7:0][4:0] lw_rd;
  assign lw_cnt = kudu_top.ls_pipeline_i.waw_fifo_i.wr_ptr_q - kudu_top.ls_pipeline_i.waw_fifo_i.rd_ptr_q;
  for (genvar k = 0; k < 8; k++) begin : g_lw
    logic [2:0] idx;
    logic [5:0] e;
    assign idx      = kudu_top.ls_pipeline_i.waw_fifo_i.rd_ptr_q[2:0] + 3'(k);
    assign e        = kudu_top.ls_pipeline_i.waw_fifo_i.fifo_mem[idx];
    assign lw_rd[k] = e[4:0];
    assign lw_l[k]  = e[5] && (e[4:0] != 5'd0);
  end

  // ---------------- scoreboard-ordered view
  logic [3:0]      sbd_n;
  logic [7:0]      pv, pw, pl;
  logic [7:0][4:0] prd;
  assign sbd_n = kudu_top.sbd_fifo_i.wr_ptr_q - kudu_top.sbd_fifo_i.rd_ptr_q;
  always_comb begin
    sbd_fifo_t  e;
    logic [2:0] idx;
    logic [3:0] n3, n4;
    n3 = '0; n4 = '0;
    pv = '0; pw = '0; pl = '0; prd = '0;
    for (int unsigned k = 0; k < 8; k++) begin
      idx   = kudu_top.sbd_fifo_i.rd_ptr_q[2:0] + k[2:0];
      e     = sbd_fifo_t'(kudu_top.sbd_fifo_i.fifo_mem[idx]);
      pv[k] = (4'(k) < sbd_n);
      if (e.pl[1]) begin
        pw[k] = a0_w; pl[k] = a0_l; prd[k] = a0_rd;
      end else if (e.pl[2]) begin
        pw[k] = a1_w; pl[k] = a1_l; prd[k] = a1_rd;
      end else if (e.pl[4]) begin
        if ((n4 == 4'd0) && mw_v) begin
          pw[k] = mw_w; pl[k] = mw_l; prd[k] = mw_rd;
        end else begin
          pw[k] = m2_w; pl[k] = m2_l; prd[k] = m2_rd;
        end
        n4 = n4 + 4'd1;
      end else if (e.pl[3]) begin
        if ((cfsm == 2'd0) && (n3 < lw_cnt)) begin
          pw[k] = (lw_rd[n3[2:0]] != 5'd0); pl[k] = lw_l[n3[2:0]]; prd[k] = lw_rd[n3[2:0]];
        end
        n3 = n3 + 4'd1;
      end
      pw[k] = pw[k] & pv[k];
      pl[k] = pl[k] & pv[k];
    end
  end

  // older-not-live: of two in-flight writers of the same register, the older one is WAW-cancelled
  logic j_old;
  always_comb begin
    j_old = 1'b1;
    for (int p = 0; p < 8; p++)
      for (int q = p + 1; q < 8; q++)
        if (pw[q] && pw[p] && (prd[p] == prd[q]) && pl[p]) j_old = 1'b0;
  end

  // reservation held: every reserved register has a live in-flight writer (sbd view)
  logic [31:1] p_live;
  logic        j_hold;
  always_comb begin
    for (int r = 1; r < 32; r++) begin
      p_live[r] = 1'b0;
      for (int p = 0; p < 8; p++)
        if (pl[p] && (prd[p] == 5'(r))) p_live[r] = 1'b1;
    end
  end
  assign j_hold = ((wrsv & ~p_live) == '0) || cerr;

  // live writer is reserved (converse), only checked in normal decode operation
  logic j_conv;
  assign j_conv = ((p_live & ~wrsv) == '0) || cerr ||
                  !kudu_top.issuer_i.ctrl_fsm_cs[CSM_DECODE];

  // live pipeline slots appear in the scoreboard view (slot-level form)
  logic [31:1] s_live;
  always_comb begin
    for (int r = 1; r < 32; r++) begin
      s_live[r] = (a0_l && (a0_rd == 5'(r))) || (a1_l && (a1_rd == 5'(r))) ||
                  (mw_l && (mw_rd == 5'(r))) || (m2_l && (m2_rd == 5'(r)));
      for (int k = 0; k < 8; k++)
        if ((4'(k) < lw_cnt) && lw_l[k] && (lw_rd[k] == 5'(r))) s_live[r] = 1'b1;
    end
  end

  // older writer is never live
  AssertHelpWrsvOld: assert property (@(posedge clk_i) disable iff (!rst_ni) j_old);
  // reserved register -> live writer in the scoreboard view (or commit error pending)
  AssertHelpWrsvHold: assert property (@(posedge clk_i) disable iff (!rst_ni) j_hold);
  // joint form
  AssertHelpWrsvJ: assert property (@(posedge clk_i) disable iff (!rst_ni) j_hold && j_old);
  // reserved register -> live pipeline slot (issue_ctrl W_Hold / ifc HlpWrsvLive shape)
  AssertHelpWrsvSlot: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ((wrsv & ~s_live) == '0) || cerr);
  // converse in DECODE
  AssertHelpWrsvConv: assert property (@(posedge clk_i) disable iff (!rst_ni) j_conv);

  // ---------------- load-filter reservations (CHERIoT)
  // LS items in flight: wb fifo entries, LSU outstanding request, lsu_if held / delayed requests
  logic [2:0]    lsif;
  logic          dly_v, outst, ls_idle, pend_hold, pend_hng, pend_dly2;
  lsu_req_info_t dly_q, hold_q, lq;
  assign lsif      = 3'(kudu_top.ls_pipeline_i.lsu_if_i.lsif_fsm_q);
  assign dly_v     = kudu_top.ls_pipeline_i.lsu_if_i.req_dly_valid;
  assign dly_q     = kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q;
  assign hold_q    = kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q;
  assign lq        = kudu_top.ls_pipeline_i.load_store_unit_i.lsu_req_info_q;
  assign outst     = kudu_top.ls_pipeline_i.load_store_unit_i.outstanding_resp_q;
  assign ls_idle   = kudu_top.ls_pipeline_i.load_store_unit_i.ls_fsm_cs == '0;
  assign pend_hold = (lsif == 3'd1) || (lsif == 3'd3);
  assign pend_hng  = pend_hold && ls_idle;
  assign pend_dly2 = ((lsif == 3'd2) || (lsif == 3'd3)) && dly_v;

  logic [2:0]  wbf_n;
  assign wbf_n = 3'(kudu_top.ls_pipeline_i.wb_fifo_i.wr_ptr_q - kudu_top.ls_pipeline_i.wb_fifo_i.rd_ptr_q);

  logic [15:1] ls_clc, tv_clc;
  logic [2:0]  tv_v;
  logic [2:0][4:0] tv_a;
  assign tv_v    = kudu_top.ls_pipeline_i.gen_trvk.cheri_trvk_stage_i.clc_valid_q;
  assign tv_a[0] = kudu_top.ls_pipeline_i.gen_trvk.cheri_trvk_stage_i.trsv_addr_q[0];
  assign tv_a[1] = kudu_top.ls_pipeline_i.gen_trvk.cheri_trvk_stage_i.trsv_addr_q[1];
  assign tv_a[2] = kudu_top.ls_pipeline_i.gen_trvk.cheri_trvk_stage_i.trsv_addr_q[2];
  always_comb begin
    logic [1:0] wi;
    pl_out_t    wo;
    for (int r = 1; r < 16; r++) begin
      ls_clc[r] = (outst && lq.is_cap && lq.rf_we && (lq.rd == 5'(r))) ||
                  (pend_hng && hold_q.is_cap && hold_q.rf_we && (hold_q.rd == 5'(r))) ||
                  (pend_dly2 && dly_q.is_cap && dly_q.rf_we && (dly_q.rd == 5'(r)));
      for (int unsigned k = 0; k < 4; k++) begin
        wi = kudu_top.ls_pipeline_i.wb_fifo_i.rd_ptr_q[1:0] + k[1:0];
        wo = pl_out_t'(kudu_top.ls_pipeline_i.wb_fifo_i.fifo_mem[wi]);
        if ((3'(k) < wbf_n) && wo.is_cap && wo.we && (wo.waddr == 5'(r))) ls_clc[r] = 1'b1;
      end
      tv_clc[r] = (tv_v[0] && (tv_a[0] == 5'(r))) || (tv_v[1] && (tv_a[1] == 5'(r))) ||
                  (tv_v[2] && (tv_a[2] == 5'(r)));
    end
  end

  // a load-filter reservation is held by a clc in the LS pipe or in the revocation stage
  AssertHelpTrsvHold: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ((trsv & ~(ls_clc | tv_clc)) == '0) || cerr);
  // same, without the commit-error escape
  AssertHelpTrsvHoldNe: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ((trsv & ~(ls_clc | tv_clc)) == '0));

  // ---------------- special issue drained
  logic st_spec, st_wtrvk;
  assign st_spec  = kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL];
  assign st_wtrvk = kudu_top.issuer_i.ctrl_fsm_cs[CSM_WAIT_TRVK];
  // ISSUE_SPECIAL is entered from WAIT_CMT0 only with an empty scoreboard and no commit error
  AssertHelpSpecSbd: assert property (@(posedge clk_i) disable iff (!rst_ni)
    st_spec |-> (sbd_n == 4'd0) && !cerr);

  // ---------------- load-filter reservation, joint invariant
  logic [15:1][3:0] tcnt;
  always_comb begin
    logic [1:0] wi;
    pl_out_t    wo;
    for (int r = 1; r < 16; r++) begin
      tcnt[r] = 4'(outst && lq.is_cap && lq.rf_we && (lq.rd == 5'(r))) +
                4'(pend_hng && hold_q.is_cap && hold_q.rf_we && (hold_q.rd == 5'(r))) +
                4'(pend_dly2 && dly_q.is_cap && dly_q.rf_we && (dly_q.rd == 5'(r))) +
                4'(tv_v[0] && (tv_a[0] == 5'(r))) + 4'(tv_v[1] && (tv_a[1] == 5'(r))) +
                4'(tv_v[2] && (tv_a[2] == 5'(r)));
      for (int unsigned k = 0; k < 4; k++) begin
        wi = kudu_top.ls_pipeline_i.wb_fifo_i.rd_ptr_q[1:0] + k[1:0];
        wo = pl_out_t'(kudu_top.ls_pipeline_i.wb_fifo_i.fifo_mem[wi]);
        if ((3'(k) < wbf_n) && wo.is_cap && wo.we && (wo.waddr == 5'(r))) tcnt[r] = tcnt[r] + 4'd1;
      end
    end
  end
  logic j_tu, j_tls, j_ttv, j_th;
  always_comb begin
    j_tu = 1'b1;
    for (int r = 1; r < 16; r++) if (tcnt[r] > 4'd1) j_tu = 1'b0;
  end
  assign j_tls = (ls_clc & ~trsv) == '0;
  assign j_ttv = ((tv_clc & ~trsv) == '0) || st_wtrvk;
  assign j_th  = (trsv & ~(ls_clc | tv_clc)) == '0;
  // at most one clc in flight per register
  AssertHelpTrsvUniq: assert property (@(posedge clk_i) disable iff (!rst_ni) j_tu);
  // a clc in the LS pipe holds its load-filter reservation
  AssertHelpTrsvLsConv: assert property (@(posedge clk_i) disable iff (!rst_ni) j_tls);
  // a clc in the revocation stage holds its reservation unless the issuer flushed (WAIT_TRVK)
  AssertHelpTrsvTvConv: assert property (@(posedge clk_i) disable iff (!rst_ni) j_ttv);
  // joint load-filter invariant (uniqueness, both converses, hold without commit-error escape)
  AssertHelpTrsvJ: assert property (@(posedge clk_i) disable iff (!rst_ni) j_tu && j_tls && j_ttv && j_th);

  // ---------------- decoded IR consistency
  ir_dec_t da, db;
  assign da = kudu_top.ir_stage_i.ira_dec_o;
  assign db = kudu_top.ir_stage_i.irb_dec_o;
  // a stored decoded instruction that writes a register without an EX pipeline is an AMO or erroneous
  AssertHelpIrLocalWe: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ((da.pl_type == PL_LOCAL) && da.rf_we && (da.rd != 5'd0) |-> da.is_cmplx || da.any_err) and
    ((db.pl_type == PL_LOCAL) && db.rf_we && (db.rd != 5'd0) |-> db.is_cmplx || db.any_err));
  // a normally issued register writer is sent to an EX pipeline
  AssertHelpIssWrPl: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.issuer_i.ir0_normal_issued && kudu_top.issuer_i.ir0_dec.rf_we && (kudu_top.issuer_i.ir0_dec.rd != 5'd0)
       |-> (kudu_top.issuer_i.ir0_pl_sel[4:1] != 4'h0)) and
    (kudu_top.issuer_i.ir1_issued && kudu_top.issuer_i.ir1_dec.rf_we && (kudu_top.issuer_i.ir1_dec.rd != 5'd0)
       |-> (kudu_top.issuer_i.ir1_pl_sel[4:1] != 4'h0)));

  // LSU busy with a request -> the lsu_if hold register carries the same request (rd/cap/we)
  AssertHelpLsuHoldEq: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !ls_idle |-> pend_hold && (hold_q.rd == lq.rd) && (hold_q.is_cap == lq.is_cap) &&
                 (hold_q.rf_we == lq.rf_we));

  // a stored decoded clc is always an LS-pipeline instruction
  AssertHelpIrClcLs: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (da.cheri_op.clc |-> (da.pl_type == PL_LS)) and (db.cheri_op.clc |-> (db.pl_type == PL_LS)));

  // a stored decoded csc never writes a register and is not a clc
  AssertHelpIrCsc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (da.cheri_op.csc |-> !da.rf_we && !da.cheri_op.clc) and (db.cheri_op.csc |-> !db.rf_we && !db.cheri_op.clc));

  // a stored decoded clc is not a CSR instruction
  AssertHelpIrClcNoCsr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (da.cheri_op.clc |-> !da.is_csr) and (db.cheri_op.clc |-> !db.is_csr));

  // a stored decoded clc is a plain capability load (rs_cheri, LS, LOAD opcode, funct3 011)
  function automatic logic clc_ok (ir_dec_t d);
    return !d.cheri_op.clc || (d.rs_cheri && (d.pl_type == PL_LS) && !d.is_csr && !d.is_cmplx &&
           !d.cheri_op.csc && !d.sysctl.valid && (d.insn[6:0] == 7'h03) && (d.insn[14:12] == 3'b011));
  endfunction
  AssertHelpIrClcFull: assert property (@(posedge clk_i) disable iff (!rst_ni) clc_ok(da) && clc_ok(db));

endmodule


// kudu_fvh_issue_ctrl (was fv/fv_help_issue_ctrl.svh, `include'd at the end of
// kudu_sva_issue). Bound into issuer as u_fvh_issue_ctrl with .*, so every port
// is an issuer signal of the same name and width. Supports the kudu_sva_issue
// control targets: AssertDretRedirect, AssertIrqCauseIsPending,
// AssertIrqTakenLegal, AssertMispredictRedirect, AssertMretRedirect,
// AssertSpecialCaseMatchesIr0, AssertSpecialDrained, AssertStepRedirect,
// AssertTrapMtvalLegal, AssertTrapRedirect, AssertTrsvInflight and
// AssertWrsvInflight. The AssertHelpH_* lemmas read kudu_fvh_backend
// (kudu_top.u_fvh_backend).
module kudu_fvh_issue_ctrl
  import super_pkg::*;
  import cheri_pkg::*;
  import csr_pkg::*;
#(
  parameter bit          CHERIoTEn  = 1'b1,
  parameter bit          RV32A      = 1'b1,
  parameter int unsigned DmHaltAddr = 32'h1A110800,
  parameter int unsigned DmExcAddr  = 32'h1A110808
) (
  // Same declarations as the kudu_sva_issue ports of the same name.
  input logic          clk_i,
  input logic          rst_ni,
  input logic          cheri_pmode_i,

  // IR / issue
  input logic [1:0]    ir_valid_i,
  input ir_dec_t       ir0_dec,
  input logic          ir0_issued,
  input logic          ir1_issued,
  input logic [1:0]    ir_any_err,
  input logic          ir0_mode_err,
  input logic [1:0]    mispredict,
  input logic [31:0]   ir0_target,
  input logic [31:0]   ir1_target,

  // hazards / forwarding
  input pl_fwd_t       alupl0_fwd_info_i,
  input pl_fwd_t       alupl1_fwd_info_i,
  input pl_fwd_t       lspl_fwd_info_i,
  input pl_fwd_t       multpl_fwd_info_i,
  input logic [31:1]   reg_wrsv_q,
  input logic [15:1]   reg_cheri_trsv_q,

  // scoreboard / commit
  input logic          cmt_err_i,
  input logic [1:0]    sbdfifo_rd_valid_i,
  input logic          trvk_outstanding_i,

  // fetch redirect
  input logic          pc_set_o,
  input logic [31:0]   pc_target_o,

  // CSR interface
  input priv_lvl_e     priv_mode_i,
  input logic          irq_pending_i,
  input irqs_t         irqs_i,
  input logic          csr_mstatus_mie_i,
  input logic [31:0]   csr_mtvec_i,
  input logic [31:0]   csr_mepc_i,
  input logic [31:0]   csr_depc_i,
  input logic          csr_save_cause_o,
  input exc_info_t     csr_exc_info_o,
  input logic          csr_restore_mret_o,
  input logic          csr_restore_dret_o,

  // debug
  input logic          debug_step_i,
  input logic          debug_mode_q,
  input logic          debug_csr_save_o,

  // controller
  input logic [15:0]   ctrl_fsm_cs,
  input special_case_e special_case_q,
  input logic          special_setpc_q,
  input sysctl_t       sysctl_q,

  // Helper-only issuer signals (not kudu_sva_issue ports). ctrl_fsm_ns,
  // trvk_addr_i, cmt_regwr_i, tsafe_en_i and cmt_flush_o are not read by the
  // current lemmas; they are kept from the helper port set of the proven run.
  input logic [31:0]   special_pc_q,
  input logic [15:0]   ctrl_fsm_ns,
  input logic          csr_mstatus_tw_i,
  input logic [1:0]    ir_hazard,
  input logic [2:0]    ir0_cjalr_err_i,
  input logic          trvk_en_i,
  input logic [4:0]    trvk_addr_i,
  input logic [31:0]   cmt_regwr_i,
  input logic          tsafe_en_i,
  input logic          cmt_flush_o
);

  // --------------------------------------------------------------------------
  // Copies of kudu_sva_issue helper logic: keep in sync with kudu_sva_issue.
  // --------------------------------------------------------------------------
  localparam logic [31:0] DmHaltPc = DmHaltAddr;
  localparam logic [31:0] DmExcPc  = DmExcAddr;

  logic st_decode, st_cmt_flush, st_wait_cmt0, st_issue, st_wait_final;
  logic st_wait_cmplx, st_sleep;
  assign st_decode     = ctrl_fsm_cs[CSM_DECODE];
  assign st_cmt_flush  = ctrl_fsm_cs[CSM_CMT_FLUSH];
  assign st_wait_cmt0  = ctrl_fsm_cs[CSM_WAIT_CMT0];
  assign st_issue      = ctrl_fsm_cs[CSM_ISSUE_SPECIAL];
  assign st_wait_final = ctrl_fsm_cs[CSM_WAIT_FINAL];
  assign st_wait_cmplx = ctrl_fsm_cs[CSM_WAIT_CMPLX];
  assign st_sleep      = ctrl_fsm_cs[CSM_SLEEP];

  logic do_exec, do_irq, do_debug, do_sysctl, do_cmplx, do_step;
  assign do_exec   = st_issue && (special_case_q == EXEC);
  assign do_irq    = st_issue && (special_case_q == IRQ);
  assign do_debug  = st_issue && (special_case_q == DEBUG);
  assign do_sysctl = st_issue && (special_case_q == SYSCTL);
  assign do_cmplx  = st_issue && (special_case_q == CMPLX);
  assign do_step   = st_issue && (special_case_q == STEP);

  logic        m_trap;      // trap recorded in mcause/mepc (not debug entry, not in debug mode)
  logic [5:0]  mcause;
  logic [31:0] mtval, epc;
  assign m_trap = csr_save_cause_o && !debug_csr_save_o && !debug_mode_q;
  assign mcause = csr_exc_info_o.mcause;
  assign mtval  = csr_exc_info_o.mtval;
  assign epc    = csr_exc_info_o.pc[31:0];

  // --------------------------------------------------------------------------
  // Lemmas (fv/fv_help_issue_ctrl.svh)
  // --------------------------------------------------------------------------
  logic hh_st_reset, hh_st_boot, hh_st_trvk;
  assign hh_st_reset = ctrl_fsm_cs[CSM_RESET];
  assign hh_st_boot  = ctrl_fsm_cs[CSM_BOOT_SET];
  assign hh_st_trvk  = ctrl_fsm_cs[CSM_WAIT_TRVK];
  logic [31:0] hh_mtvec;
  assign hh_mtvec = {csr_mtvec_i[31:2], 2'b00};
  logic hh_sys_setpc;
  assign hh_sys_setpc = sysctl_q.ebrk | sysctl_q.ecall | sysctl_q.mret | sysctl_q.dret | sysctl_q.fencei;
  logic [3:0] hh_sbd_cnt;
  assign hh_sbd_cnt = kudu_top.sbd_fifo_i.wr_ptr_q - kudu_top.sbd_fifo_i.rd_ptr_q;
  logic hh_fwd_any;
  assign hh_fwd_any = (|alupl0_fwd_info_i.valid) | (|alupl1_fwd_info_i.valid) |
                      (|lspl_fwd_info_i.valid) | (|multpl_fwd_info_i.valid);

  // ---- A: FSM and latched special-case state (global invariants) ----
  AssertHelpFsmLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
    $onehot(ctrl_fsm_cs) && ((ctrl_fsm_cs & ~16'h0f5f) == 16'h0));
  AssertHelpSysSetpc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (special_case_q == SYSCTL) |-> (special_setpc_q == hh_sys_setpc));
  AssertHelpSysOneHot: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (special_case_q == SYSCTL) |-> sysctl_q.valid &&
      $onehot({sysctl_q.csrw, sysctl_q.fencei, sysctl_q.ebrk, sysctl_q.ecall, sysctl_q.wfi, sysctl_q.dret, sysctl_q.mret}));
  AssertHelpDbgLatch: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (special_case_q == DEBUG) |-> special_setpc_q && (special_pc_q == DmHaltPc));
  AssertHelpExecIrqSetpc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (special_case_q inside {EXEC, IRQ}) |-> special_setpc_q);
  AssertHelpIssuePrev: assert property (@(posedge clk_i) disable iff (!rst_ni)
    st_issue |-> $past(st_wait_cmt0));
  AssertHelpFlushPrev: assert property (@(posedge clk_i) disable iff (!rst_ni)
    st_cmt_flush |-> $past(st_decode || st_wait_cmt0 || st_wait_final || st_wait_cmplx));

  // ---- B: special_pc_q matches the expected target in ISSUE_SPECIAL / CMT_FLUSH ----
  AssertHelpPcExec: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_exec |-> (special_pc_q == (debug_mode_q ? DmExcPc : hh_mtvec)));
  AssertHelpPcIrq: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_irq |-> !debug_mode_q && (special_pc_q == hh_mtvec));
  AssertHelpPcEbrk: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (do_sysctl && sysctl_q.ebrk) |-> (special_pc_q == (debug_mode_q ? DmHaltPc : hh_mtvec)));
  AssertHelpPcEcall: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (do_sysctl && sysctl_q.ecall) |-> (special_pc_q == (debug_mode_q ? DmExcPc : hh_mtvec)));
  AssertHelpPcMret: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (do_sysctl && sysctl_q.mret) |-> (special_pc_q == csr_mepc_i));
  AssertHelpPcDret: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (do_sysctl && sysctl_q.dret) |-> (special_pc_q == csr_depc_i));
  AssertHelpPrivMret: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (do_sysctl && sysctl_q.mret) |-> (priv_mode_i == PRIV_LVL_M));
  AssertHelpDmDret: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (do_sysctl && sysctl_q.dret) |-> debug_mode_q);
  AssertHelpPcFlush: assert property (@(posedge clk_i) disable iff (!rst_ni)
    st_cmt_flush |-> (special_case_q == EXEC) && (special_pc_q == (debug_mode_q ? DmExcPc : hh_mtvec)));

  // ---- S: CSR / IR0 stability from the WAIT_CMT0 decision to ISSUE_SPECIAL ----
  AssertHelpStMtvec:  assert property (@(posedge clk_i) disable iff (!rst_ni) st_issue |-> $stable(csr_mtvec_i));
  AssertHelpStMepc:   assert property (@(posedge clk_i) disable iff (!rst_ni) st_issue |-> $stable(csr_mepc_i));
  AssertHelpStDepc:   assert property (@(posedge clk_i) disable iff (!rst_ni) st_issue |-> $stable(csr_depc_i));
  AssertHelpStPriv:   assert property (@(posedge clk_i) disable iff (!rst_ni) st_issue |-> $stable(priv_mode_i));
  AssertHelpStMie:    assert property (@(posedge clk_i) disable iff (!rst_ni) st_issue |-> $stable(csr_mstatus_mie_i));
  AssertHelpStTw:     assert property (@(posedge clk_i) disable iff (!rst_ni) st_issue |-> $stable(csr_mstatus_tw_i));
  AssertHelpStStep:   assert property (@(posedge clk_i) disable iff (!rst_ni) st_issue |-> $stable(debug_step_i));
  AssertHelpStDm:     assert property (@(posedge clk_i) disable iff (!rst_ni) st_issue |-> $stable(debug_mode_q));
  AssertHelpStIrqPend: assert property (@(posedge clk_i) disable iff (!rst_ni)
    st_issue && $past(irq_pending_i) |-> irq_pending_i);
  AssertHelpFlMtvec:  assert property (@(posedge clk_i) disable iff (!rst_ni) st_cmt_flush |-> $stable(csr_mtvec_i));
  AssertHelpStHaz:    assert property (@(posedge clk_i) disable iff (!rst_ni) st_issue |-> $stable(ir_hazard[0]));
  AssertHelpStCjErr: assert property (@(posedge clk_i) disable iff (!rst_ni) (st_issue && (special_case_q == EXEC)) |-> $stable(ir0_cjalr_err_i));
  AssertHelpStAnyErr: assert property (@(posedge clk_i) disable iff (!rst_ni) (st_issue && (special_case_q == EXEC)) |-> $stable(ir_any_err[0]));
  AssertHelpStModeErr: assert property (@(posedge clk_i) disable iff (!rst_ni) (st_issue && (special_case_q == EXEC)) |-> $stable(ir0_mode_err));
  AssertHelpStMis0: assert property (@(posedge clk_i) disable iff (!rst_ni) (st_issue && (special_case_q == STEP)) |-> $stable(mispredict[0]));
  AssertHelpStTgt0:   assert property (@(posedge clk_i) disable iff (!rst_ni) (st_issue && (special_case_q == STEP) && mispredict[0]) |-> $stable(ir0_target));
  AssertHelpStValid0: assert property (@(posedge clk_i) disable iff (!rst_ni) st_issue |-> ir_valid_i[0] || $past(!ir_valid_i[0]));
  AssertHelpIssueNoFwd: assert property (@(posedge clk_i) disable iff (!rst_ni) st_issue |-> !hh_fwd_any);
  AssertHelpCmt0NoFwd:  assert property (@(posedge clk_i) disable iff (!rst_ni)
    (st_wait_cmt0 && !sbdfifo_rd_valid_i[0]) |-> !hh_fwd_any);
  AssertHelpSbdEmptyNoFwd: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !sbdfifo_rd_valid_i[0] |-> !hh_fwd_any);
  AssertHelpSbdValidCnt: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sbdfifo_rd_valid_i[0] == (hh_sbd_cnt != 4'd0));
  AssertHelpIssueNoTrvk: assert property (@(posedge clk_i) disable iff (!rst_ni)
    st_issue |-> !trvk_en_i);
  AssertHelpSysNotCti: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (st_issue && (special_case_q inside {SYSCTL, CMPLX})) |-> !mispredict[0]);
  AssertHelpStepMis: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_step |-> (special_setpc_q == mispredict[0]));
  AssertHelpStepTgt: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (do_step && mispredict[0]) |-> (special_pc_q == ir0_target));

  // ---- T: split versions of the targets ----
  AssertHelpT_TrapSetpc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    csr_save_cause_o |-> pc_set_o);
  AssertHelpT_TrapFlush: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (csr_save_cause_o && st_cmt_flush) |-> (pc_target_o == (debug_mode_q ? DmExcPc : hh_mtvec)));
  AssertHelpT_TrapDbg: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_debug |-> (pc_target_o == DmHaltPc));
  AssertHelpT_TrapExec: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_exec |-> (pc_target_o == (debug_mode_q ? DmExcPc : hh_mtvec)));
  AssertHelpT_TrapIrq: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_irq |-> (pc_target_o == (debug_mode_q ? DmExcPc : hh_mtvec)));
  AssertHelpT_TrapSys: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (csr_save_cause_o && do_sysctl) |-> (pc_target_o == ((debug_mode_q && sysctl_q.ebrk) ? DmHaltPc :
                                                         debug_mode_q ? DmExcPc : hh_mtvec)));
  AssertHelpT_MretPriv: assert property (@(posedge clk_i) disable iff (!rst_ni)
    csr_restore_mret_o |-> (priv_mode_i == PRIV_LVL_M));
  AssertHelpT_MretSet: assert property (@(posedge clk_i) disable iff (!rst_ni)
    csr_restore_mret_o |-> pc_set_o && !csr_save_cause_o);
  AssertHelpT_MretTgt: assert property (@(posedge clk_i) disable iff (!rst_ni)
    csr_restore_mret_o |-> (pc_target_o == csr_mepc_i));
  AssertHelpT_DretDm: assert property (@(posedge clk_i) disable iff (!rst_ni)
    csr_restore_dret_o |-> debug_mode_q);
  AssertHelpT_DretSet: assert property (@(posedge clk_i) disable iff (!rst_ni)
    csr_restore_dret_o |-> pc_set_o && !csr_save_cause_o);
  AssertHelpT_DretTgt: assert property (@(posedge clk_i) disable iff (!rst_ni)
    csr_restore_dret_o |-> (pc_target_o == csr_depc_i));
  AssertHelpT_StepSet: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_step |-> (pc_set_o == mispredict[0]));
  AssertHelpT_StepTgt: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (do_step && pc_set_o) |-> (pc_target_o == ir0_target));
  AssertHelpT_Mis0Dec: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (st_decode && ir0_issued && mispredict[0]) |-> pc_set_o && (pc_target_o == ir0_target) && !ir1_issued);
  AssertHelpT_Mis0Spc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (!st_decode && ir0_issued && mispredict[0]) |-> pc_set_o && (pc_target_o == ir0_target) && !ir1_issued);
  AssertHelpT_Mis1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (ir1_issued && mispredict[1]) |-> pc_set_o && (pc_target_o == ir1_target));
  AssertHelpT_MtvIrq: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_trap |-> (!mcause[5] || (mtval == 32'h0)));
  AssertHelpT_MtvBrk: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_trap |-> ((mcause != 6'(EXC_CAUSE_BREAKPOINT)) || (mtval == epc)));
  AssertHelpT_MtvFetch: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_trap |-> ((mcause != 6'(EXC_CAUSE_INSTR_ACCESS_FAULT)) || (mtval == epc) || (mtval == epc + 32'd2)));
  AssertHelpT_MtvIll: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_trap |-> ((mcause != 6'(EXC_CAUSE_ILLEGAL_INSN)) || !(CHERIoTEn && cheri_pmode_i) || (mtval == 32'h0)));
  AssertHelpT_MtvCheriFl: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (m_trap && st_cmt_flush) |-> ((mcause != 6'(EXC_CAUSE_CHERI_FAULT)) || ((mtval[31:11] == '0) && (mtval[4:0] != 5'h0))));
  AssertHelpT_MtvCheriIs: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (m_trap && st_issue) |-> ((mcause != 6'(EXC_CAUSE_CHERI_FAULT)) || ((mtval[31:11] == '0) && (mtval[4:0] != 5'h0))));
  AssertHelpT_IrqAny: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_irq |-> (irqs_i != '0));
  AssertHelpT_IrqPend: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_irq |-> irq_pending_i);
  AssertHelpT_IrqMie: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_irq |-> (csr_mstatus_mie_i || (priv_mode_i != PRIV_LVL_M)));
  AssertHelpT_IrqDm: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_irq |-> !debug_mode_q);
  AssertHelpT_IrqStep: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_irq |-> !debug_step_i);
  AssertHelpT_ScExec: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_exec |-> (ir_any_err[0] || ir0_mode_err));
  AssertHelpT_ScSysErr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_sysctl |-> !ir_any_err[0] && !ir0_mode_err);
  AssertHelpT_ScSysEq: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_sysctl |-> (ir0_dec.sysctl == sysctl_q) && sysctl_q.valid);
  AssertHelpT_ScCmplx: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_cmplx |-> RV32A && !ir_any_err[0] && ir0_dec.is_cmplx);
  AssertHelpT_ScStepErr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_step |-> !ir_any_err[0] && !ir0_mode_err);
  AssertHelpT_ScStepOth: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_step |-> !ir0_dec.sysctl.valid && !(RV32A && ir0_dec.is_cmplx) && debug_step_i && !debug_mode_q);
  AssertHelpT_DrSbd: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (st_issue || st_sleep) |-> !sbdfifo_rd_valid_i[0]);
  AssertHelpT_DrTrvk: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (st_issue || st_sleep) |-> !trvk_outstanding_i);
  AssertHelpT_DrErr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (st_issue || st_sleep) |-> !cmt_err_i);
  AssertHelpT_DrWrsvI: assert property (@(posedge clk_i) disable iff (!rst_ni)
    st_issue |-> (reg_wrsv_q == '0));
  AssertHelpT_DrWrsvS: assert property (@(posedge clk_i) disable iff (!rst_ni)
    st_sleep |-> (reg_wrsv_q == '0));
  AssertHelpT_DrTrsv: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (st_issue || st_sleep) |-> (reg_cheri_trsv_q == '0));

  // ---- W: register reservations vs. in-flight youngest writers ----
  // shadow: per-register "youngest writer still in a pipeline" vector
  logic [3:0]  hh_waw_cnt;
  logic [7:0]  hh_waw_slot_v;
  logic [31:0] hh_hold_alu0, hh_hold_alu1, hh_hold_mex2, hh_hold_mwb, hh_hold_ls, hh_hold;
  logic [31:0] hh_ls_any;           // any LS entry (latest or not) writing r
  logic [31:0] hh_trvk_any;         // revocation pipe holds a clc to r
  logic [3:0]  hh_pl_cnt;
  logic [2:0]  trvk_clc_valid_q;
  logic [4:0]  trvk_addr_q0, trvk_addr_q1, trvk_addr_q2;
  assign trvk_clc_valid_q = kudu_top.ls_pipeline_i.gen_trvk.cheri_trvk_stage_i.clc_valid_q;
  assign trvk_addr_q0 = kudu_top.ls_pipeline_i.gen_trvk.cheri_trvk_stage_i.trsv_addr_q[0];
  assign trvk_addr_q1 = kudu_top.ls_pipeline_i.gen_trvk.cheri_trvk_stage_i.trsv_addr_q[1];
  assign trvk_addr_q2 = kudu_top.ls_pipeline_i.gen_trvk.cheri_trvk_stage_i.trsv_addr_q[2];
  assign hh_waw_cnt = kudu_top.ls_pipeline_i.waw_fifo_i.wr_ptr_q - kudu_top.ls_pipeline_i.waw_fifo_i.rd_ptr_q;
  for (genvar j = 0; j < 8; j++) begin : g_hh_slot
    logic [2:0] off;
    assign off = 3'(j) - kudu_top.ls_pipeline_i.waw_fifo_i.rd_ptr_q[2:0];
    assign hh_waw_slot_v[j] = ({1'b0, off} < hh_waw_cnt);
  end
  for (genvar r = 0; r < 32; r++) begin : g_hh_hold
    logic [7:0] lat, any;
    for (genvar j = 0; j < 8; j++) begin : g_s
      assign lat[j] = hh_waw_slot_v[j] && kudu_top.ls_pipeline_i.waw_fifo_i.fifo_mem[j][5] &&
                      (kudu_top.ls_pipeline_i.waw_fifo_i.fifo_mem[j][4:0] == 5'(r));
      assign any[j] = hh_waw_slot_v[j] && (kudu_top.ls_pipeline_i.waw_fifo_i.fifo_mem[j][4:0] == 5'(r));
    end
    assign hh_hold_alu0[r] = kudu_top.alu_pipeline0_i.wb_valid && kudu_top.alu_pipeline0_i.wb_reg.rf_we &&
                             kudu_top.alu_pipeline0_i.wb_fwd_valid_q && (kudu_top.alu_pipeline0_i.wb_reg.rd == 5'(r));
    assign hh_hold_alu1[r] = kudu_top.alu_pipeline1_i.wb_valid && kudu_top.alu_pipeline1_i.wb_reg.rf_we &&
                             kudu_top.alu_pipeline1_i.wb_fwd_valid_q && (kudu_top.alu_pipeline1_i.wb_reg.rd == 5'(r));
    assign hh_hold_mex2[r] = kudu_top.mult_pipeline_i.ex2_valid && kudu_top.mult_pipeline_i.ex2_reg.rf_we &&
                             kudu_top.mult_pipeline_i.ex2_fwd_ok && (kudu_top.mult_pipeline_i.ex2_reg.rd == 5'(r));
    assign hh_hold_mwb[r]  = kudu_top.mult_pipeline_i.wb_valid && kudu_top.mult_pipeline_i.wb_reg.rf_we &&
                             kudu_top.mult_pipeline_i.wb_fwd_valid_q && (kudu_top.mult_pipeline_i.wb_reg.rd == 5'(r));
    assign hh_hold_ls[r]   = |lat;
    assign hh_ls_any[r]    = |any;
    assign hh_trvk_any[r]  = (trvk_clc_valid_q[0] && (trvk_addr_q0 == 5'(r))) ||
                             (trvk_clc_valid_q[1] && (trvk_addr_q1 == 5'(r))) ||
                             (trvk_clc_valid_q[2] && (trvk_addr_q2 == 5'(r)));
  end
  assign hh_hold   = hh_hold_alu0 | hh_hold_alu1 | hh_hold_mex2 | hh_hold_mwb | hh_hold_ls;
  assign hh_pl_cnt = 4'(kudu_top.alu_pipeline0_i.wb_valid) + 4'(kudu_top.alu_pipeline1_i.wb_valid) +
                     4'(kudu_top.mult_pipeline_i.ex2_valid) + 4'(kudu_top.mult_pipeline_i.wb_valid) + hh_waw_cnt;

  // every reserved register has a youngest in-flight writer (or a commit error is pending)
  AssertHelpW_Hold: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (({reg_wrsv_q, 1'b0} & ~hh_hold) == 32'h0) || cmt_err_i);
  // every instruction held in an EX pipeline (ALU/mult stages, LS waw-fifo) has a scoreboard entry
  AssertHelpW_Cnt: assert property (@(posedge clk_i) disable iff (!rst_ni)
    hh_pl_cnt <= hh_sbd_cnt);
  // the complex unit only runs with the LS waw-fifo empty
  AssertHelpW_CmplxWaw: assert property (@(posedge clk_i) disable iff (!rst_ni)
    st_wait_cmplx |-> (hh_waw_cnt == 4'd0));
  // LS output corresponds to the waw-fifo head (rd and write-enable)
  AssertHelpW_LsOut: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.ls_pipeline_i.lspl_valid_o && (hh_waw_cnt != 4'd0) && !kudu_top.ls_pipeline_i.lspl_output_o.err) |->
      (kudu_top.ls_pipeline_i.lspl_output_o.waddr == kudu_top.ls_pipeline_i.waw_fifo_i.fifo_mem[kudu_top.ls_pipeline_i.waw_fifo_i.rd_ptr_q[2:0]][4:0]) &&
      ((kudu_top.ls_pipeline_i.waw_fifo_i.fifo_mem[kudu_top.ls_pipeline_i.waw_fifo_i.rd_ptr_q[2:0]][4:0] == 5'h0) ||
       kudu_top.ls_pipeline_i.lspl_output_o.we));
  // LS output is only presented with a waw-fifo entry outside the complex-unit sequence
  AssertHelpW_LsValid: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.ls_pipeline_i.lspl_valid_o && !st_wait_cmplx) |-> (hh_waw_cnt != 4'd0));
  // every load-filter reservation has a clc either in the LS pipe or in the revocation pipe
  AssertHelpW_TrsvHold: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (({reg_cheri_trsv_q, 1'b0} & ~(hh_ls_any[15:0] | hh_trvk_any[15:0])) == 16'h0) || cmt_err_i);
  // direct forms of the targets' consequents
  AssertHelpW_HoldSbd: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (hh_hold != 32'h0) |-> sbdfifo_rd_valid_i[0]);
  AssertHelpW_LsSbd: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (hh_waw_cnt != 4'd0) |-> sbdfifo_rd_valid_i[0]);

  // ---- C: CSR side effects only while their instruction is still in flight ----
  // a CSR read/write executes in the LSU before its scoreboard entry retires
  AssertHelpCsrSbd: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.csr_op_en |-> sbdfifo_rd_valid_i[0]);
  // same, phrased against the LS waw-fifo occupancy
  AssertHelpCsrWaw: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.csr_op_en |-> (hh_waw_cnt != 4'd0));

  // ---- S2: IR0 error/decode stability for every IR0-based special case ----
  logic hh_ir0_case;
  assign hh_ir0_case = (special_case_q inside {EXEC, SYSCTL, CMPLX, STEP});
  AssertHelpSt2AnyErr:  assert property (@(posedge clk_i) disable iff (!rst_ni)
    (st_issue && hh_ir0_case) |-> $stable(ir_any_err[0]));
  AssertHelpSt2ModeErr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (st_issue && hh_ir0_case) |-> $stable(ir0_mode_err));
  AssertHelpSt2Sys:     assert property (@(posedge clk_i) disable iff (!rst_ni)
    (st_issue && hh_ir0_case) |-> $stable(ir0_dec.sysctl) && $stable(ir0_dec.is_cmplx));
  AssertHelpSt2CjErr:   assert property (@(posedge clk_i) disable iff (!rst_ni)
    (st_issue && hh_ir0_case) |-> $stable(ir0_cjalr_err_i));

  // ---- E: an EXEC special case always has a concrete recorded cause ----
  AssertHelpExecCause: assert property (@(posedge clk_i) disable iff (!rst_ni)
    do_exec |-> (|{ir0_dec.errs.perm_vio, ir0_dec.errs.bound_vio, ir0_dec.errs.fetch_err, ir0_dec.errs.illegal_insn,
                   ir0_dec.errs.illegal_c_insn, ir0_dec.errs.asr_vio}) || ir0_mode_err || (|ir0_cjalr_err_i));
  // the decoder's any_err is fully explained by the errs fields it reports
  AssertHelpAnyErrErrs: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ir_valid_i[0] && ir0_dec.any_err |-> (|ir0_dec.errs));

  // ---- H: link to the backend scoreboard/pipeline correspondence (kudu_fvh_backend, proven there) ----
  // u_fvh_backend.seq_cnt[3] = LS instructions in flight (wb_fifo + LSU outstanding + lsu_if hold/dly)
  // u_fvh_backend.plcnt[x]   = scoreboard entries targeting pipeline x
  // a CSR access in the LSU is the LSU's outstanding request
  AssertHelpH_CsrLsuE: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.ls_pipeline_i.load_store_unit_i.csr_go_q |-> kudu_top.u_fvh_backend.lsu_e);
  // any LS instruction in flight keeps the scoreboard non-empty
  AssertHelpH_LsSeqSbd: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.u_fvh_backend.seq_cnt[3] != 4'd0) |-> sbdfifo_rd_valid_i[0]);
  // the LS waw-fifo never tracks more instructions than the LS pipe holds
  AssertHelpH_WawLe: assert property (@(posedge clk_i) disable iff (!rst_ni)
    hh_waw_cnt <= kudu_top.u_fvh_backend.seq_cnt[3]);
  // ALU/mult in-flight instructions keep the scoreboard non-empty
  AssertHelpH_AluMulSbd: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.alu_pipeline0_i.wb_valid || kudu_top.alu_pipeline1_i.wb_valid ||
     kudu_top.mult_pipeline_i.ex2_valid || kudu_top.mult_pipeline_i.wb_valid) |-> sbdfifo_rd_valid_i[0]);
  // the revocation stage only holds clc's while trvk_outstanding is raised
  AssertHelpH_TrvkOut: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (hh_trvk_any != 32'h0) |-> trvk_outstanding_i);
endmodule

`endif  // KUDU_FCOV_OFF
`endif  // CHERIoT
`endif  // KUDU_FV_HELPERS
