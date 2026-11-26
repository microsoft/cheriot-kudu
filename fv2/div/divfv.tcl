# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Block-level proof of multdiv32's divider (div/divfv.sv, README 4.4).
# Joint k-induction as in the stage-2 e2e sweeps:
#   base: BMC from reset (all properties, plus covers);
#   step: free state, rst_ni high, every assertion assumed for 2 cycles,
#         each one checked at cycle 3.
# Results go to $DIVOUT/res.txt. Run from fv2/:
#   DIVOUT=<scratch dir> submit -i -q interactive jg -batch -fpv div/divfv.tcl -proj <scratch dir>/jg

set fv2Root [expr {[info exists ::env(FV2ROOT)] ? $::env(FV2ROOT) : "/home/kunyanliu/riscdev/super/fv2"}]
set rtlRoot [file normalize $fv2Root/../rtl]
# MDFILE overrides the divider RTL (mutation runs on a scratch copy).
set mdFile [expr {[info exists ::env(MDFILE)] ? $::env(MDFILE) : "$rtlRoot/multdiv32.sv"}]
set D $::env(DIVOUT)
set out [open $D/res.txt a]

proc load_design {} {
  global rtlRoot fv2Root mdFile
  clear -all
  analyze -sv12 +define+SYNTHESIS $rtlRoot/cheri_pkg.sv $rtlRoot/super_pkg.sv $mdFile
  analyze -sv12 $fv2Root/div/divfv.sv
  elaborate -top divfv_top -disable_auto_bbox
  clock clk_i
}

proc divreport {tag} {
  global out
  foreach p [get_property_list -include {type {assert cover}}] {
    if {[string match *precondition* $p]} continue
    puts $out [format "%-5s %-14s %4s %s" $tag [get_property_info $p -list status] \
                 [get_property_info $p -list min_length] $p]
  }
  flush $out
}

# Base case (skipped with SKIP_BASE=1, e.g. when rerunning the step).
if {![info exists ::env(SKIP_BASE)]} {
load_design
reset ~rst_ni
set_max_trace_length 45
set_engine_mode {B K N}
set_prove_time_limit [expr {[info exists ::env(BASE_TL)] ? $::env(BASE_TL) : "20m"}]
prove -all
divreport BASE
}

# Step.
load_design
close [open $D/empty.init w]
reset -init_state $D/empty.init
assume -name Ind_NoReset {rst_ni}
set all {}
foreach p [get_property_list -include {type assert}] {
  if {[string match *precondition* $p]} continue
  lappend all $p
}
assume -from_assert $all -bound 2
set_max_trace_length 3
set_engine_mode {B Hp N AM}
set_prove_time_limit [expr {[info exists ::env(STEP_TL)] ? $::env(STEP_TL) : "10m"}]
foreach p $all {
  assert -enable $p
  set t0 [exec date +%s]
  prove -property $p
  puts $out [format "STEP  %-14s %4s %5ds %s" [get_property_info $p -list status] \
               [get_property_info $p -list min_length] [expr {[exec date +%s]-$t0}] $p]
  flush $out
}
puts $out "DONE"
close $out
exit
