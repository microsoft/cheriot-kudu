// JasperGold file list for FPV of the SVAs in the functional coverage model
// (sim/fcov), used by fv_kudu_fcov.tcl. $rtlRoot, $verifRoot (sim/) and
// $fvRoot (fv/) are set by the TCL script.
//
// Differences from kudu.jp.f:
//  - no +define+SYNTHESIS: the fcov binds use RTL debug signals that only
//    exist under `ifndef SYNTHESIS, and kudu_top then instantiates the tracer,
//    so tracer_pkg.sv / tracer.sv are added;
//  - module_fv_ext_fcov.sv replaces module_fv_ext.sv (none of its
//    KUDU_FORMAL_G* groups or AltEnable override are used);
//  - fv_fcov_env.sv holds the environment assumptions (boot address, bus
//    protocol, error qualification, held irq/debug requests);
//  - kudu_fcov_isa.sv is left out (no SVAs; binds into the RVFI tracer).
//    JasperGold skips the covergroups (VERI-9060) and keeps the assertions.
+define+CHERIoT
+define+KUDU_FORMAL_RTL
+incdir+$rtlRoot
$rtlRoot/cheri_pkg.sv
$rtlRoot/csr_pkg.sv
$rtlRoot/super_pkg.sv
$rtlRoot/kudu_cfg_pkg.sv
$rtlRoot/dual_fifo.sv
$rtlRoot/stage_fifo.sv
$rtlRoot/wt_fifo.sv
$rtlRoot/waw_tracking_fifo.sv
$rtlRoot/regfile.sv
$rtlRoot/ir_decoder.sv
$rtlRoot/ir_stage.sv
$rtlRoot/issuer.sv
$rtlRoot/fetch_fifo64.sv
$rtlRoot/prefetch_buffer64.sv
$rtlRoot/compressed_decoder.sv
$rtlRoot/if_stage.sv
$rtlRoot/alu_decoder.sv
$rtlRoot/rv32_alu.sv
$rtlRoot/cheri_alu.sv
$rtlRoot/alu_pipeline.sv
$rtlRoot/load_store_unit.sv
$rtlRoot/lsu_if.sv
$rtlRoot/dcache.sv
$rtlRoot/cheri_trvk_stage.sv
$rtlRoot/ls_pipeline.sv
$rtlRoot/multdiv32.sv
$rtlRoot/mult_pipeline.sv
$rtlRoot/committer.sv
$rtlRoot/branch_unit.sv
$rtlRoot/branch_predict.sv
$rtlRoot/ibex_counter.sv
$rtlRoot/ibex_csr.sv
$rtlRoot/cs_registers.sv
$rtlRoot/cmplx_unit.sv
$rtlRoot/kudu_top.sv
$rtlRoot/tracer_pkg.sv
$rtlRoot/tracer.sv
$fvRoot/module_fv_ext_fcov.sv
$fvRoot/fv_fcov_env.sv
$verifRoot/fcov/kudu_fcov_pkg.sv
$verifRoot/fcov/kudu_fcov_csr.sv
$verifRoot/fcov/kudu_fcov_if.sv
$verifRoot/fcov/kudu_fcov_id.sv
$verifRoot/fcov/kudu_fcov_issue.sv
$verifRoot/fcov/kudu_fcov_ex.sv
$verifRoot/fcov/kudu_fcov_context.sv
$verifRoot/fcov/kudu_fcov_lsu.sv
$verifRoot/fcov/kudu_fcov_cmt.sv
$verifRoot/fcov/kudu_fcov_top.sv
$verifRoot/fcov/kudu_fcov_bind.sv
