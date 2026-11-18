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

// Design-property SVAs of the CSR block (kudu_sva_csr). status_t/dcsr_t are
// local to cs_registers, so their fields are connected one by one.
bind cs_registers kudu_sva_csr #(
  .CHERIoTEn      (CHERIoTEn),
  .CFG            (CFG),
  .DbgTriggerEn   (DbgTriggerEn),
  .BrkptNum       (BrkptNum)
) u_fcov_sva_csr (
  .*,
  .mstatus_mie    (mstatus_q.mie),
  .mstatus_mpie   (mstatus_q.mpie),
  .mstatus_mpp    (mstatus_q.mpp),
  .mstatus_mprv   (mstatus_q.mprv),
  .mstatus_tw     (mstatus_q.tw),
  .dcsr_bits      (dcsr_q),                // whole dcsr as 32 bits for $stable
  .dcsr_xdebugver (dcsr_q.xdebugver),
  .dcsr_cause     (dcsr_q.cause),
  .dcsr_prv       (dcsr_q.prv),
  // fields forced to zero or unsupported (cs_registers.sv:702-714)
  .dcsr_fixed     ({dcsr_q.zero2, dcsr_q.zero1, dcsr_q.zero0, dcsr_q.stepie,
                    dcsr_q.nmip, dcsr_q.mprven, dcsr_q.stopcount, dcsr_q.stoptime}),
  .mcycle         (mhpmcounter[0])         // mcycle is counter 0
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
  .InstrBufEn    (InstrBufEn),
  .PredictRA     (PredictRA)
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

// SVA property checker for the fetch path (kudu_sva_if in kudu_fcov_if.sv).
// All hierarchical signals are module-scope in their targets (the generate
// blocks in prefetch_buffer64/fetch_fifo64 only assign them).
bind if_stage kudu_sva_if #(
  .PrefetchDepth  (PrefetchDepth),
  .AltEnable      (AltEnable),
  .PredictRA      (PredictRA),
  .UnalignedFetch (UnalignedFetch),
  .PredictUseBtb  (PredictUseBtb)
) u_fcov_sva_if (
  .*,
  .pb_outstanding_q (prefetch_buffer_i.rdata_outstanding_q),
  .pb_discard_q     (prefetch_buffer_i.branch_discard_q),
  // Response as seen by the buffer (registered when InstrRdataBypass = 0).
  .pb_rvalid_in     (prefetch_buffer_i.instr_rvalid_in),
  .pb_rdata_in      (prefetch_buffer_i.instr_rdata_in),
  .pb_err_in        (prefetch_buffer_i.instr_err_in),
  .pb_fifo_valid    (prefetch_buffer_i.fifo_valid),
  .pb_alt_nxt_addr  (prefetch_buffer_i.alt_nxt_addr),
  .ff_valid_q       (prefetch_buffer_i.fifo_i.valid_q),
  .ff_apply_alt     (prefetch_buffer_i.fifo_i.apply_alt),
  .ff_alloc_alt     (prefetch_buffer_i.fifo_i.alloc_alt),
  .ff_alt_status    (prefetch_buffer_i.fifo_i.alt_status),
  .ff_alt_free_id   (prefetch_buffer_i.fifo_i.alt_free_id),
  .ff_alt_err_event (prefetch_buffer_i.fifo_i.alt_err_event),
  // bht_e is an integer enum: connect the full 32-bit value.
  .bp_bht_rdata0    (branch_predict_i.bht_rdata[0]),
  .bp_bht_rdata1    (branch_predict_i.bht_rdata[1])
);

// Reference-expansion checker for every compressed_decoder instance (in
// if_stage when IfCompDecEn, otherwise in ir_stage).
bind compressed_decoder kudu_sva_if_cdec #(
  .CHERIoTEn (CHERIoTEn)
) u_fcov_sva_if_cdec (
  .*
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

// Formal SVA checkers for the IR / decode stage (kudu_sva_id in kudu_fcov_id.sv).
// The stage-1 FIFO and RA-prediction checks reach into ir_stage.gen_stage1 only under
// matching generate guards on StageBypass / PredictRA.
bind ir_stage kudu_sva_id #(
  .StageBypass(StageBypass), .CHERIoTEn(CHERIoTEn), .PredictRA(PredictRA),
  .RV32M(RV32M), .RV32B(RV32B), .RV32A(RV32A)
) u_fcov_sva_id (.*);

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
  .irq_fast             (irqs_i.irq_fast),
  // Renamed in the RTL by 127aade; the coverage port names are kept so the
  // standalone stub in tb_fcov_frontend_temporal.sv does not change.
  .debug_single_step_i  (debug_step_i),
  .single_step_trap_q   (step_req_q)
);

// Design-property assertions for the issuer (no coverage).
bind issuer kudu_sva_issue #(
  .CHERIoTEn  (CHERIoTEn),
  .RV32A      (RV32A),
  .DmHaltAddr (DmHaltAddr),
  .DmExcAddr  (DmExcAddr)
) u_fcov_sva_issue (.*);

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

// SVA property checkers for the execution units (kudu_sva_* in kudu_fcov_ex.sv).
bind kudu_top.alu_pipeline0_i kudu_sva_alu #(
  .CHERIoTEn(CHERIoTEn), .SingleStage(SingleStage)
) u_fcov_sva_alu (.*);

bind kudu_top.alu_pipeline1_i kudu_sva_alu #(
  .CHERIoTEn(CHERIoTEn), .SingleStage(SingleStage)
) u_fcov_sva_alu (.*);

bind branch_unit kudu_sva_branch_unit #(.CHERIoTEn(CHERIoTEn)) u_fcov_sva_branch_unit (.*);

bind mult_pipeline kudu_sva_mult #(.CHERIoTEn(CHERIoTEn)) u_fcov_sva_mult (.*);

bind cmplx_unit kudu_sva_cmplx #(.CHERIoTEn(CHERIoTEn)) u_fcov_sva_cmplx (
  .*,
  // cmplx_fsm_e is local to cmplx_unit (:38).
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

// SVA design properties (kudu_sva_* in kudu_fcov_lsu.sv).
bind ls_pipeline kudu_sva_lsu #(.CHERIoTEn(CHERIoTEn)) u_fcov_sva_lsu (
  .*,

  .ls_fsm_cs           (load_store_unit_i.ls_fsm_cs),
  .handle_misaligned_q (load_store_unit_i.handle_misaligned_q),
  .outstanding_resp_q  (load_store_unit_i.outstanding_resp_q),
  .req_err_q           (load_store_unit_i.req_err_q),
  .csr_go_q            (load_store_unit_i.csr_go_q),
  .ls_go               (load_store_unit_i.ls_go),
  .csr_go              (load_store_unit_i.csr_go),
  .lsu_req_info_q      (load_store_unit_i.lsu_req_info_q),
  // lsif_fsm_e is declared inside lsu_if (:27), so pass it as a 3-bit vector
  .lsif_fsm_q          (3'(lsu_if_i.lsif_fsm_q)),
  .req_dly_valid       (lsu_if_i.req_dly_valid),
  // FIFO wr_rdy_o ports are left unconnected at ls_pipeline.sv:331/:355
  .wb_fifo_wr_rdy      (wb_fifo_i.wr_rdy),
  .waw_fifo_wr_rdy     (waw_fifo_i.wr_rdy)
);

bind dcache kudu_sva_dcache #(.TagHi(TagHi)) u_fcov_sva_dcache (.*);

`ifdef CHERIoT
bind cheri_trvk_stage kudu_sva_trvk #(.HeapBase(HeapBase), .TSMapSize(TSMapSize))
  u_fcov_sva_trvk (.*);
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

// SVA property checkers (kudu_sva_* in kudu_fcov_top.sv). The FIFO checkers are
// bound by module name so that every instance in every configuration is covered;
// their parameters are taken from the target instance.
bind kudu_top kudu_sva_top #(
  .CHERIoTEn(CHERIoTEn)
) u_fcov_sva_top (.*);

bind dual_fifo kudu_sva_dual_fifo #(
  .Depth(Depth), .Width(Width), .PplRead(PplRead), .WrThrough(WrThrough)
) u_fcov_sva_dual_fifo (.*);

bind stage_fifo kudu_sva_stage_fifo #(
  .Width(Width), .PeekMem(PeekMem)
) u_fcov_sva_stage_fifo (.*);

bind wt_fifo kudu_sva_wt_fifo #(
  .Depth(Depth), .Width(Width)
) u_fcov_sva_wt_fifo (.*);

bind waw_tracking_fifo kudu_sva_waw_fifo #(
  .Depth(Depth), .Width(Width), .WrThrough(WrThrough)
) u_fcov_sva_waw_fifo (.*);

// ---------------------------------------------------------------------------
// FC_MA_CMT -> committer
// ---------------------------------------------------------------------------
bind committer kudu_fcov_cmt u_fcov_cmt (.*);
bind committer kudu_sva_cmt #(.CHERIoTEn(CHERIoTEn)) u_fcov_sva_cmt (.*);

// Context reads RTL stages/FIFO controls through hierarchical references.
bind kudu_top kudu_fcov_context #(
  .CFG(CFG), .CHERIoTEn(CHERIoTEn)
) u_fcov_context (.*);

// ---------------------------------------------------------------------------
// FV helper lemmas (formal only; the modules are defined at the end of
// kudu_fcov_{csr,if,issue,ex,cmt}.sv). Simulation never defines
// KUDU_FV_HELPERS. The helpers read internals of the fcov instances bound
// above, so they need this KUDU_FCOV_OFF guard too, and they were proven only
// with CHERIoTEn=1 (kudu_fvh_issue_ctrl names the CHERIoT-only
// gen_trvk.cheri_trvk_stage_i), hence the CHERIoT guard.
// ---------------------------------------------------------------------------
`ifdef KUDU_FV_HELPERS
`ifdef CHERIoT
bind kudu_top kudu_fvh_csr      u_fvh_csr      (.*);
bind kudu_top kudu_fvh_front_pc u_fvh_front_pc (.*);
bind kudu_top kudu_fvh_issue_fwd u_fvh_issue_fwd (.*);
bind kudu_top kudu_fvh_wrsv     u_fvh_wrsv     (.*);
bind kudu_top kudu_fvh_ex_lsu   u_fvh_ex_lsu   (.*);
bind kudu_top kudu_fvh_backend  u_fvh_backend  (.*);

bind issuer kudu_fvh_issue_ctrl #(
  .CHERIoTEn  (CHERIoTEn),
  .RV32A      (RV32A),
  .DmHaltAddr (DmHaltAddr),
  .DmExcAddr  (DmExcAddr)
) u_fvh_issue_ctrl (.*);
`endif  // CHERIoT
`endif  // KUDU_FV_HELPERS

`default_nettype wire

`endif  // KUDU_FCOV_OFF
