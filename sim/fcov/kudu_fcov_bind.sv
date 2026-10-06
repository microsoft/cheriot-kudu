// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Bind statements for the Kudu functional coverage model.
//
// Use .* for same-name ports so missing signals fail elaboration. Explicit
// connections are limited to expressions and renamed or hierarchical signals.
//
// See doc/functional_coverage_plan.md, and sim/fcov/README.md for the one
// integration point (the retire tap) that needs review.

`ifndef KUDU_FCOV_OFF

// This directive protects this scope, not implicit nets in the bind target.
// check_binds.py audits the explicit expressions; .* checks matching signals.
`default_nettype none

// ---------------------------------------------------------------------------
// FC_ISA_INSTR -> tracer
//
// The tracer already reconstructs the architectural retire order, so binding
// to it avoids building a second, independently buggy retire model.  This is
// the one integration point that needs human review: if the tracer's retire
// loop (tracer.sv:456-469) changes, sample_entry() in kudu_fcov_isa.sv must
// change with it.
//
// The FIFO uses the shared tracer_pkg::instr_trace_t. The coverage input is a
// packed vector with a checked width, cast back to that same shared type.
// ---------------------------------------------------------------------------
`ifdef RVFI
bind tracer kudu_fcov_isa u_fcov_isa (
  .*,
  .amo_retire (cmt_valid[0] &&
               ((amo_state == AMO_T_WAIT1) ||
                ((amo_state == AMO_T_WAIT0) && cmt_instr_err[0])))
);
`endif

// ---------------------------------------------------------------------------
// FC_ISA_CSR -> cs_registers
//
// status_t and dcsr_t are declared inside cs_registers, so individual fields
// are connected rather than the whole struct.
// ---------------------------------------------------------------------------
bind cs_registers kudu_fcov_csr #(
  .CHERIoTEn      (CHERIoTEn),
  .DbgTriggerEn   (DbgTriggerEn),
  .PMPEnable      (PMPEnable),
  .MHPMCounterNum (MHPMCounterNum)
) u_fcov_csr (
  .*,
  .mstatus_mie    (mstatus_q.mie),
  .mstatus_mpie   (mstatus_q.mpie),
  .mstatus_mpp    (mstatus_q.mpp),
  .priv_mode      (priv_mode_o),
  .dcsr_step      (dcsr_q.step),
  .dcsr_stepie    (dcsr_q.stepie),
  .dcsr_ebreakm   (dcsr_q.ebreakm),
  .dcsr_ebreaku   (dcsr_q.ebreaku),
  .dcsr_nmip      (dcsr_q.nmip),
  .dcsr_prv       (dcsr_q.prv),
  .tmatch_control (|tmatch_control_o)
);

// ---------------------------------------------------------------------------
// FC_MA_IF -> if_stage
//
// Reaches into prefetch_buffer_i / prefetch_buffer_i.fifo_i / branch_predict_i
// rather than binding those modules separately, so that fetch, buffering and
// prediction stay in one covergroup set: they are one pipeline stage and their
// interesting states are correlated.
// ---------------------------------------------------------------------------
bind if_stage kudu_fcov_if #(
  .BhtSize       (PredictBhtSize),
  .PrefetchDepth (PrefetchDepth),
  .AltEnable     (AltEnable),
  .InstrBufEn    (InstrBufEn)
) u_fcov_if (
  .*,
  .rdata_outstanding_q  (prefetch_buffer_i.rdata_outstanding_q),
  .branch_discard_q     (prefetch_buffer_i.branch_discard_q),
  .discard_req_q        (prefetch_buffer_i.discard_req_q),
  .fifo_clear           (prefetch_buffer_i.fifo_clear),
  .fifo_busy            (prefetch_buffer_i.fifo_busy),

  // Preserve the full count rather than narrowing a parameter-dependent depth.
  .fifo_occupancy       (unsigned'($countones(prefetch_buffer_i.fifo_i.valid_q))),
  .alt_status           (prefetch_buffer_i.fifo_i.alt_status),
  .pdt_en_i             (branch_predict_i.pdt_en_i),
  .pdt_valid_o          (branch_predict_i.pdt_valid_o),
  .pdt_instr0           (branch_predict_i.pdt_instr0),
  .pdt_instr1           (branch_predict_i.pdt_instr1),
  .bp_is_branch         (branch_predict_i.is_branch),
  .bp_is_jal            (branch_predict_i.is_jal),
  .bp_is_jalr_ra        (branch_predict_i.is_jalr_ra),
  .pdt_branch_go        (branch_predict_i.pdt_branch_go),
  .pdt_jal_go           (branch_predict_i.pdt_jal_go),
  .pdt_jalr_go          (branch_predict_i.pdt_jalr_go),
  .pdt_pc_set           (branch_predict_i.pdt_pc_set),
  .bht_rdata0           (branch_predict_i.bht_rdata[0][1:0]),
  .bht_rdata1           (branch_predict_i.bht_rdata[1][1:0]),
  .fetch_instr0_is_comp (branch_predict_i.fetch_instr0_i.is_comp)
);

// ---------------------------------------------------------------------------
// FC_MA_ID -> ir_stage
//
// Only module-scope signals are used.  The stage 0/1 FIFOs live inside
// configuration-dependent generate blocks (ir_stage.sv:244, :274, :450), so
// reaching into them would break when StageBypass changes.
// The three five-bit rf_waddrN_i ports map directly through .* like rf_weN_i.
// ---------------------------------------------------------------------------
bind ir_stage kudu_fcov_id #(
  .StageBypass(StageBypass), .CHERIoTEn(CHERIoTEn), .PredictRA(PredictRA)
) u_fcov_id (.*);

// ---------------------------------------------------------------------------
// FC_MA_ISSUE -> issuer
// ---------------------------------------------------------------------------
bind issuer kudu_fcov_issue u_fcov_issue (
  .*,

  // The fwd_act buses are 32-bit per-register masks; the coverage model only
  // needs to know which pipeline is driving one this cycle.
  .alupl0_fwd_act_i_any (|alupl0_fwd_act_i),
  .alupl1_fwd_act_i_any (|alupl1_fwd_act_i),
  .lspl_fwd_act_i_any   (|lspl_fwd_act_i),
  .multpl_fwd_act_i_any (|multpl_fwd_act_i),
  .irq_fast             (irqs_i.irq_fast)
);

// ---------------------------------------------------------------------------
// FC_MA_EX -> alu_pipeline (both instances), branch_unit, mult_pipeline, cmplx_unit
//
// The ALU bind names each instance explicitly rather than binding the module
// once, so that the two pipelines report separate coverage: slot 1 is issued
// under different conditions from slot 0 and must not be allowed to inherit
// slot 0's coverage.
// ---------------------------------------------------------------------------
bind kudu_top.alu_pipeline0_i kudu_fcov_alu #(
  .PlName("alu0"), .SingleStage(SingleStage), .CHERIoTEn(CHERIoTEn)
) u_fcov_alu (
  .*,
  // cycle2 is a field of alupl_reg_t (alu_pipeline.sv:43-49) carried in the
  // EX2 stage register, not a module-scope signal.
  .cycle2 (ex2_reg.cycle2)
);

bind kudu_top.alu_pipeline1_i kudu_fcov_alu #(
  .PlName("alu1"), .SingleStage(SingleStage), .CHERIoTEn(CHERIoTEn)
) u_fcov_alu (
  .*,
  .cycle2 (ex2_reg.cycle2)
);

bind branch_unit kudu_fcov_branch_unit #(
  .CHERIoTEn(CHERIoTEn), .ChkBranchJALAddr(ChkBranchJALAddr)
) u_fcov_branch_unit (.*);

bind mult_pipeline kudu_fcov_mult #(.CHERIoTEn(CHERIoTEn)) u_fcov_mult (
  .*,
  // is_mult / is_div are fields of flags_t (mult_pipeline.sv:55-59) held in
  // the EX2 stage register, not module-scope signals.
  .is_mult (ex2_reg.flags.is_mult),
  .is_div  (ex2_reg.flags.is_div)
);

bind cmplx_unit kudu_fcov_cmplx u_fcov_cmplx (
  .*,
  // cmplx_fsm_e is declared inside cmplx_unit (:38), so it cannot be named
  // in a bound module's port list.
  .cmplx_fsm_cs (2'(cmplx_fsm_cs))
);

// ---------------------------------------------------------------------------
// FC_MA_LSU -> ls_pipeline (+ load_store_unit_i, dcache_i, cheri_trvk_stage_i)
// ---------------------------------------------------------------------------
bind ls_pipeline kudu_fcov_lsu u_fcov_lsu (
  .*,

  .ls_fsm_cs               (load_store_unit_i.ls_fsm_cs),
  .split_misaligned_access (load_store_unit_i.split_misaligned_access),
  .handle_misaligned_q     (load_store_unit_i.handle_misaligned_q),
  .addr_incr_req           (load_store_unit_i.addr_incr_req),
  .lsu_busy                (load_store_unit_i.busy_o)
);

// dcache_i and cheri_trvk_stage_i live inside generate blocks in ls_pipeline
// (:359 unnamed, :383 gen_trvk), so they are bound by module name instead of
// reached through a hierarchical path that would break with the config.
bind dcache kudu_fcov_dcache u_fcov_dcache (.*);

// The testbench and syntax checker keep CHERIoT aligned with CHERIoTEn;
// kudu_top also sets LoadFiltEn from CHERIoTEn, so RV32 builds have no target.
`ifdef CHERIoT
bind cheri_trvk_stage kudu_fcov_trvk u_fcov_trvk (.*);
`endif

// ---------------------------------------------------------------------------
// FC_MA_TOP -> kudu_top
//
// Observe the scoreboard FIFO and selected top-level bus/configuration ports.
// Adding a new RTL port does not automatically add coverage; review it explicitly.
// ---------------------------------------------------------------------------
bind kudu_top kudu_fcov_top #(
  .MemW (MemW),
  .CHERIoTEn(CHERIoTEn),
  .UnalignedFetch(CFG.UnalignedFetch)
) u_fcov_top (.*);

// ---------------------------------------------------------------------------
// FC_MA_CMT -> committer
// ---------------------------------------------------------------------------
bind committer kudu_fcov_cmt u_fcov_cmt (.*);

// Context reads RTL stages/FIFO controls through hierarchical references.
bind kudu_top kudu_fcov_context #(
  .CFG(CFG), .CHERIoTEn(CHERIoTEn)
) u_fcov_context (.*);

`default_nettype wire

`endif  // KUDU_FCOV_OFF
