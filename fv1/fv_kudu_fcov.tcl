# FPV of the SVAs embedded in the functional coverage model (sim/fcov).
#
# The fcov modules bind into the DUT exactly as in simulation; JasperGold
# skips their covergroups (VERI-9060) and proves the assert properties
# (illegal_bins companions and standalone invariants). See kudu_fcov.jp.f
# for the file list and fv_fcov_env.sv for the environment.
#
# Interactive (from fv/):  ./run_jg, then
#   source fv_kudu_fcov.tcl
#   run_fcov_clean "" 1              ;# all asserts + FV helper lemmas, ordered,
#                                    ;# pmode 1 -> jp_fcov_clean_p1.log
#   run_fcov_all                     ;# fcov asserts only, no helpers -> jp_fcov_out.log
#   run_fcov "" 300s "*u_fcov_lsu*"  ;# one fcov instance
#   fcov_cex_vcd <property> <file.vcd>
# Batch: jg -batch -fpv -allow_unsupported_OS -proj <dir> <wrapper.tcl>,
#   where the wrapper sources this file, calls run_fcov_clean (or run_fcov_all)
#   and exits. Full description: sim/fv/README.md.

# Asserts known to fail because of open or waived RTL behaviour
# (sim/testplan/bug_logs_3.md).
set fcov_expected_cex {
  kudu_top.ls_pipeline_i.u_fcov_sva_lsu.AssertEarlyLoadSplitInRegion {waived: INT-3, sim/testplan/integration_issues.md}
}

# Vdef: extra analyze options, e.g. "+define+FCOV_FV_FREE_REQ".
# pmode: value assumed for cheri_pmode_i (1 CHERIoT, 0 RV32 compatibility).
# Eopts: extra elaborate options. The default keeps JasperGold from
#   black-boxing the multiplier partial-product array and the SVA reference
#   multiply/divide operators, which gives spurious CEXs on their checks.
proc fcov_setup {{Vdef ""} {pmode 1} {Eopts "-bbox_a 4096 -bbox_mul 256"}} {
  clear -all
  set rtlRoot   ../rtl
  set verifRoot ../sim
  set fvRoot    .

  analyze -sv17 {*}$Vdef -f ./kudu_fcov.jp.f
  elaborate {*}$Eopts -parameter CHERIoTEn 1 -parameter CFG KuduCfg1 -top kudu_top

  reset ~rst_ni
  clock clk_i
  assume -name AssumeFcovPmode "cheri_pmode_i == 1'b$pmode"
}

# limit: per-property proof time limit. pattern: glob on property names.
# Vdef, pmode: as for fcov_setup.
proc run_fcov {{Vdef ""} {limit 300s} {pattern *} {pmode 1}} {
  global fcov_expected_cex
  fcov_setup $Vdef $pmode

  set props {}
  foreach p [get_property_list -include {type assert}] {
    if {[string match "*u_fcov_*" $p] && [string match $pattern $p]} {
      lappend props $p
    }
  }
  foreach a [get_property_list -include {type assume}] {
    regsub {^.*::} $a {} name
    puts "ASSUME $name"
  }
  set_prove_per_property_time_limit $limit
  prove -property $props

  array set exp $fcov_expected_cex
  set n(proven) 0; set n(cex) 0; set n(other) 0
  set unexpected {}
  foreach p $props {
    regsub {^.*::} $p {} name
    set st  [get_property_info $p -list status]
    set len [get_property_info $p -list min_length]
    set note ""
    if {[string match "*cex*" $st]} {
      incr n(cex)
      if {[info exists exp($name)]} {
        set note "expected ($exp($name))"
      } else {
        set note "UNEXPECTED"
        lappend unexpected $name
      }
    } elseif {[string match "proven*" $st]} {
      incr n(proven)
    } else {
      incr n(other)
      if {[info exists exp($name)]} { set note "expected CEX ($exp($name)) not found" }
    }
    puts [format "RES %-14s %8s %s %s" $st $len $name $note]
  }
  puts "FCOV FV $Vdef pmode=$pmode: [llength $props] asserts, $n(proven) proven, $n(cex) cex, $n(other) undetermined"
  if {[llength $unexpected]} {
    puts "FCOV FV FAIL: unexpected CEX: $unexpected"
  } else {
    puts "FCOV FV PASS: no unexpected CEX"
  }
  puts "Done FV with fcov $Vdef ----------------------------------------------"
}

proc run_fcov_all {{log jp_fcov_out.log} {limit 300s} {pmode 1}} {
  redirect -file $log -force [list run_fcov "" $limit * $pmode]
}

# Clean lemma flow: every fcov assert plus the FV helper lemmas (kudu_fvh_*
# modules, +define+KUDU_FV_HELPERS) in one session, with nothing pre-assumed.
# Asserts are proved one at a time in the order of fcov_order_p<pmode>.txt
# (asserts missing from it go last); each proven assert immediately becomes
# an assumption for the later ones, a CEX never does. Passes over the
# remaining asserts repeat with limit "short" while they make progress, then
# once with limit "long". Progress goes to $log as it happens.
proc run_fcov_clean {{log ""} {pmode 1} {short 2m} {long 15m} {order ""} {maxpass 12}} {
  global fcov_expected_cex
  if {$log eq ""} { set log jp_fcov_clean_p$pmode.log }
  if {$order eq ""} { set order fcov_order_p$pmode.txt }
  fcov_setup "+define+KUDU_FV_HELPERS" $pmode \
    "-bbox_a 4096 -bbox_mul 256 -bbox_div 64 -bbox_mod 64"

  set out [open $log w]
  set t00 [::tcl::clock::seconds]
  foreach a [get_property_list -include {type assume}] {
    puts $out "ASSUME [fcov_norm $a]"
  }
  array set full {}
  foreach p [get_property_list -include {type assert}] { set full([fcov_norm $p]) $p }
  set seq {}
  array set seen {}
  if {[file exists $order]} {
    set h [open $order]
    foreach n [split [read $h] "\n"] {
      set n [string trim $n]
      if {[info exists full($n)] && ![info exists seen($n)]} { lappend seq $n; set seen($n) 1 }
    }
    close $h
  }
  set nord [llength $seq]
  foreach n [lsort [array names full]] {
    if {![info exists seen($n)]} { lappend seq $n; set seen($n) 1; puts $out "UNORDERED $n" }
  }
  puts $out "TOTAL [llength $seq] asserts ($nord ordered by $order)"; flush $out

  array set stat {}
  set remaining $seq
  set pass 0
  set lim $short
  while {[llength $remaining] && $pass < $maxpass} {
    incr pass
    puts $out "PASS $pass limit $lim remaining [llength $remaining] t=[expr {[::tcl::clock::seconds] - $t00}]s"
    flush $out
    set next {}
    set nproved 0
    foreach n $remaining {
      set p $full($n)
      set t0 [::tcl::clock::seconds]
      # prove -property takes glob patterns, so generate-block brackets become ?
      if {[catch {prove -property [list [string map {[ ? ] ?} $p]] \
                    -engine_mode {N Tri AM I Hp} -time_limit $lim -orchestration off} e]} {
        puts $out "PROVE_ERR $n $e"
      }
      set st  [get_property_info $p -list status]
      set len [get_property_info $p -list min_length]
      puts $out [format "RES P%d %-12s %8s %5ss %s" $pass $st $len [expr {[::tcl::clock::seconds] - $t0}] $n]
      flush $out
      set stat($n) $st
      if {[string match proven* $st]} {
        incr nproved
        assume -from_assert $p -remove_original
      } elseif {![string match *cex* $st]} {
        lappend next $n
      }
    }
    set remaining $next
    puts $out "PASS_DONE $pass proven $nproved"; flush $out
    if {$nproved == 0} {
      if {$lim eq $long} break
      set lim $long
    } else {
      set lim $short
    }
  }

  array set exp {}
  foreach {name why} $fcov_expected_cex { set exp([fcov_norm $name]) $why }
  set np 0; set nc 0; set nu 0
  set unexpected {}
  foreach n $seq {
    set st $stat($n)
    if {[string match proven* $st]} {
      incr np
    } elseif {[string match *cex* $st]} {
      incr nc
      if {[info exists exp($n)]} {
        puts $out "FINAL_CEX $n expected ($exp($n))"
      } else {
        puts $out "FINAL_CEX $n UNEXPECTED"
        lappend unexpected $n
      }
    } else {
      incr nu
      puts $out "FINAL_OPEN $st $n"
    }
  }
  puts $out "FCOV FV CLEAN pmode=$pmode: [llength $seq] asserts, $np proven, $nc cex, $nu undetermined, $pass passes, [expr {[::tcl::clock::seconds] - $t00}]s"
  if {[llength $unexpected]} {
    puts $out "FCOV FV FAIL: unexpected CEX: $unexpected"
  } else {
    puts $out "FCOV FV PASS: no unexpected CEX"
  }
  close $out
}

# Property name without the "<embedded>::" and "kudu_top." prefixes.
proc fcov_norm {name} {
  regsub {^.*::} $name {} name
  regsub {^kudu_top\.} $name {} name
  return $name
}

proc fcov_cex_vcd {prop file} {
  visualize -violation -property $prop -new_window
  visualize -save -vcd $file -force
}
