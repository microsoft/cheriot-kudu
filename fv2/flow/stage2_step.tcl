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

set fv2Root @FV2@
set rtlRoot  [file normalize $fv2Root/../rtl]
set specBld  $tools/upstream_spec/out
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
# Stage 2 induction sweep 2 (README §5): free initial state, rst_ni high,
# past_valid assumed (Harness_PastValidSoon), every other property assumed.
reset -init_state @RUNDIR@/empty.init
assume -name Ind_NoReset {rst_ni}
assume -name Ind_PastValid {past_valid}
set D @RUNDIR@
set all {}
foreach p [get_property_list -include {type assert}] {
  if {[string match *precondition* $p]} continue
  lappend all $p
}
set slow {}; set l0 {}; set l1 {}; set l2 {}; set u1 {}; set u2 {}
foreach p $all {
  if {[regexp {\.(Inv_H_AluData[01]|Inv_H_MulEx2Data|Inv_G_F[A-Za-z0-9]*|Fetch_Iss[01])$} $p]} { lappend l1 $p } elseif {[regexp {\.(Cmt_Wr|Reg_Cont[01]_Rs[12])$} $p]} { lappend l2 $p } elseif {[regexp {\.(g_inv_aisx[01]\[11\]\.Inv_H_AluIss_X|Inv_F_LsqTrap|Inv_F_LsqCause|Inv_H_MulIss_C|Inv_F_CurTrap|Mem_GoReq|Mem_GoTrap)$} $p] || [regexp {\.(g_inv_regwf\[([1-9]|1[0-5])\]\.Inv_B_RegWF)$} $p]} { lappend slow $p } else { lappend l0 $p }
  if {[regexp {\.(Inv_H_AluIss_[CX]|Inv_H_MulIss_C)$} $p]} { lappend u1 $p }
  if {[regexp {\.(Inv_H_AluIss_[CX]|Inv_H_MulIss_C|Inv_H_AluData[01]|Inv_H_MulEx2Data|Inv_H_MulData|Inv_H_LsWbData)$} $p]} { lappend u2 $p }
}
set mine {}; set i 0
foreach p $l0 { if {($i % 2) == 0} { lappend mine $p }; incr i }
set myslow {}; set i 0
foreach p $slow { if {($i % 2) == 0} { lappend myslow $p }; incr i }
set out [open $D/res.txt w]
puts $out "NPROPS [llength $mine]+[llength $myslow] of [llength $all] slow [llength $slow] l0 [llength $l0] l1 [llength $l1] l2 [llength $l2] u1 [llength $u1] u2 [llength $u2] round8 L0 shard 0/2"; flush $out
set_max_trace_length 3
set_engine_mode {B Hp N AM}
proc rec {p lvl dt} {
  global out D
  regsub {^<embedded>::} $p {} short
  set st [get_property_info $p -list status]
  puts $out [format "%-14s %4s %5ds L%s %s" $st [get_property_info $p -list min_length] $dt $lvl $p]; flush $out
  if {$st eq "cex"} {
    if {[catch {
      visualize -violation -property $p -new_window
      regsub -all {[^A-Za-z0-9_.]} $short _ f
      visualize -save -vcd $D/$f.vcd -force
    } e]} { puts $out "VCDERR $p $e" }
  }
}
proc done {p} {
  set st [get_property_info $p -list status]
  if {$st eq "proven" || $st eq "cex"} { return 1 }
  return [expr {[get_property_info $p -list min_length] >= 4}]
}
proc runp {p lvl} {
  global out
  if {[catch {
    assert -enable $p
    set t0 [exec date +%s]
    prove -property $p
    rec $p $lvl [expr {[exec date +%s]-$t0}]
  } e]} { puts $out "ERR $p $e"; flush $out }
}
proc runchunks {ps lvl sz} {
  global out
  set retry {}
  for {set j 0} {$j < [llength $ps]} {incr j $sz} {
    set c [lrange $ps $j [expr {$j+$sz-1}]]
    if {[catch {
      foreach p $c { assert -enable $p }
      set t0 [exec date +%s]
      prove -property $c
      set dt [expr {[exec date +%s]-$t0}]
      foreach p $c { if {[done $p]} { rec $p $lvl $dt } else { lappend retry $p } }
    } e]} { puts $out "ERR chunk $j $e"; flush $out; set retry [concat $retry $c] }
  }
  return $retry
}
proc setassumes {unb} {
  global all
  set bnd {}
  foreach p $all { if {[lsearch -exact $unb $p] < 0} { lappend bnd $p } }
  assume -from_assert $bnd -bound 2
  if {[llength $unb]} { assume -from_assert $unb }
}
if {0 == 0} {
  setassumes {}
  set_prove_time_limit 20m
  set retry [runchunks $mine 0 20]
  set_prove_time_limit 45m
  foreach p [concat $retry $myslow] { runp $p 0 }
} elseif {0 == 1} {
  setassumes $u1
  set_prove_time_limit 30m
  set retry [runchunks $l1 1 10]
  set_prove_time_limit 45m
  foreach p $retry { runp $p 1 }
} else {
  setassumes $u2
  set_prove_time_limit 45m
  foreach p $l2 { runp $p 2 }
}
close $out
exit
