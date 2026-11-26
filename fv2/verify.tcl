# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Stage-1 end-to-end proof of kudu_top against the cheriot-sail spec
# (README.md). Structure follows cheriot-ibex dv/formal/verify.tcl.
#
# Run from fv2/ (paths are relative to this script), e.g. with the JasperGold
# project in scratch:
#   source /home/scratch/fortress/kunyanliu/e2e_tools/env.sh
#   cd fv2 && submit -i jg verify.tcl -proj $T/kudu_e2e/jgproject
#
# Generated spec inputs come from $T (env.sh) or E2E_TOOLS.

if {[info exists ::env(T)]} {
  set tools $::env(T)
} elseif {[info exists ::env(E2E_TOOLS)]} {
  set tools $::env(E2E_TOOLS)
} else {
  set tools /home/scratch/fortress/kunyanliu/e2e_tools
}

set fv2Root  [file dirname [file normalize [info script]]]
set rtlRoot  [file normalize $fv2Root/../rtl]
# Spec generated from the CHERIoT-Platform cheriot-sail dii-read-from-file
# branch with lowRISC's FV changes ported ($T/upstream_spec/build_spec.sh).
# E2E_SPEC_BLD overrides it (e.g. $T/ibex_formal/build for the lowRISC spec).
if {[info exists ::env(E2E_SPEC_BLD)]} {
  set specBld $::env(E2E_SPEC_BLD)
} else {
  set specBld $tools/upstream_spec/out
}
set sailLib  $tools/src/sail/lib/sv

clear -all

# SYNTHESIS drops the tracer and simulation-only code; KUDU_FORMAL_RTL selects
# the Jasper-friendly regfile read mux (as in fv/kudu.jp.f).
set rtlDefs {+define+SYNTHESIS +define+CHERIoT +define+KUDU_FORMAL_RTL}

set rtlFiles {
  cheri_pkg csr_pkg super_pkg kudu_cfg_pkg
  dual_fifo stage_fifo wt_fifo waw_tracking_fifo regfile
  ir_decoder ir_stage issuer
  fetch_fifo64 prefetch_buffer64 compressed_decoder if_stage
  alu_decoder rv32_alu cheri_alu alu_pipeline
  load_store_unit lsu_if dcache cheri_trvk_stage ls_pipeline
  multdiv32 mult_pipeline committer branch_unit branch_predict
  ibex_counter ibex_csr cs_registers cmplx_unit kudu_top
}

set rtlPaths {}
foreach f $rtlFiles { lappend rtlPaths $rtlRoot/$f.sv }

analyze -sv12 {*}$rtlDefs +incdir+$rtlRoot {*}$rtlPaths

# Sail spec and its support code, in the Ibex order.
analyze -sv12 -incdir $sailLib -incdir $specBld $specBld/ibexspec.sv
analyze -sv12 $fv2Root/spec/stub.sv
analyze -sv12 $specBld/extracted.sv
analyze -sv12 $fv2Root/spec/ext_bounds.sv
analyze -sv12 {*}$rtlDefs $fv2Root/spec/cheri.sv
analyze -sv12 {*}$rtlDefs $fv2Root/spec/spec_api.sv

# Harness (check/top.sv includes abs, spec_instance, follower, checks).
analyze -sv12 {*}$rtlDefs +incdir+$fv2Root/check $fv2Root/check/top.sv

# No auto black-boxing: the regfile and mult/div arrays must stay real.
elaborate -top kudu_e2e_top -disable_auto_bbox

clock clk_i
reset ~rst_ni

# Stage 1: bounded model checking only.
set_max_trace_length 20
set_prove_time_limit 24h
set_engine_mode {B Ht}

prove -all

puts "kudu_e2e: prove -all done (BMC, depth 20)"
