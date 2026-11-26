# Round-8 consolidated step-ordered check (review 1, gap 8).
# usage: mkfinal8.py <src_rundir> <dst_rundir> <level 0|1|2> [<shard> <nshards>]
# One Jasper session per level (round 7 showed re-deriving assumes in one
# session fails with EPM029).
# Same levels as round 7 (sound by induction on (time, level)):
#   L0: all properties not listed below, other properties assumed on 2 cycles only.
#   L1: AluData*, MulEx2Data, fetch group (Inv_G_F*, Fetch_Iss*), with H0 (issue
#       helpers) assumed on all cycles.
#   L2: Cmt_Wr, Reg_Cont, with H0 + L1 data + MulData/LsWbData on all cycles.
# Fixes the round-7 EPM029 crash: an assert is never made both a bounded and
# an unbounded assume.
# L0 fast properties are proved in chunks; any left at min_length < 4 (time
# out) is retried alone at the slow limit. Known-slow ones (round 7) run alone.
import sys
src, dst, lv = sys.argv[1], sys.argv[2], int(sys.argv[3])
k, n = (int(sys.argv[4]), int(sys.argv[5])) if lv == 0 else (0, 1)
t = open(f"{src}/run.tcl").read().replace(src, dst)
a = t.index("set slow {}"); b = t.index("close $out")
SLOW = (r'g_inv_aisx[01]\[11\]\.Inv_H_AluIss_X|Inv_F_LsqTrap|Inv_F_LsqCause|Inv_H_MulIss_C|'
        r'Inv_F_CurTrap|Mem_GoReq|Mem_GoTrap')
SLOWRWF = r'g_inv_regwf\[([1-9]|1[0-5])\]\.Inv_B_RegWF'
H0 = r'Inv_H_AluIss_[CX]|Inv_H_MulIss_C'
L1 = r'Inv_H_AluData[01]|Inv_H_MulEx2Data|Inv_G_F[A-Za-z0-9]*|Fetch_Iss[01]'
L2 = r'Cmt_Wr|Reg_Cont[01]_Rs[12]'
U2 = H0 + r'|Inv_H_AluData[01]|Inv_H_MulEx2Data|Inv_H_MulData|Inv_H_LsWbData'
body = f'''set slow {{}}; set l0 {{}}; set l1 {{}}; set l2 {{}}; set u1 {{}}; set u2 {{}}
foreach p $all {{
  if {{[regexp {{\\.({L1})$}} $p]}} {{ lappend l1 $p }} elseif {{[regexp {{\\.({L2})$}} $p]}} {{ lappend l2 $p }} elseif {{[regexp {{\\.({SLOW})$}} $p] || [regexp {{\\.({SLOWRWF})$}} $p]}} {{ lappend slow $p }} else {{ lappend l0 $p }}
  if {{[regexp {{\\.({H0})$}} $p]}} {{ lappend u1 $p }}
  if {{[regexp {{\\.({U2})$}} $p]}} {{ lappend u2 $p }}
}}
set mine {{}}; set i 0
foreach p $l0 {{ if {{($i % {n}) == {k}}} {{ lappend mine $p }}; incr i }}
set myslow {{}}; set i 0
foreach p $slow {{ if {{($i % {n}) == {k}}} {{ lappend myslow $p }}; incr i }}
set out [open $D/res.txt w]
puts $out "NPROPS [llength $mine]+[llength $myslow] of [llength $all] slow [llength $slow] l0 [llength $l0] l1 [llength $l1] l2 [llength $l2] u1 [llength $u1] u2 [llength $u2] round8 L{lv} shard {k}/{n}"; flush $out
set_max_trace_length 3
set_engine_mode {{B Hp N AM}}
proc rec {{p lvl dt}} {{
  global out D
  regsub {{^<embedded>::}} $p {{}} short
  set st [get_property_info $p -list status]
  puts $out [format "%-14s %4s %5ds L%s %s" $st [get_property_info $p -list min_length] $dt $lvl $p]; flush $out
  if {{$st eq "cex"}} {{
    if {{[catch {{
      visualize -violation -property $p -new_window
      regsub -all {{[^A-Za-z0-9_.]}} $short _ f
      visualize -save -vcd $D/$f.vcd -force
    }} e]}} {{ puts $out "VCDERR $p $e" }}
  }}
}}
proc done {{p}} {{
  set st [get_property_info $p -list status]
  if {{$st eq "proven" || $st eq "cex"}} {{ return 1 }}
  return [expr {{[get_property_info $p -list min_length] >= 4}}]
}}
proc runp {{p lvl}} {{
  global out
  if {{[catch {{
    assert -enable $p
    set t0 [exec date +%s]
    prove -property $p
    rec $p $lvl [expr {{[exec date +%s]-$t0}}]
  }} e]}} {{ puts $out "ERR $p $e"; flush $out }}
}}
proc runchunks {{ps lvl sz}} {{
  global out
  set retry {{}}
  for {{set j 0}} {{$j < [llength $ps]}} {{incr j $sz}} {{
    set c [lrange $ps $j [expr {{$j+$sz-1}}]]
    if {{[catch {{
      foreach p $c {{ assert -enable $p }}
      set t0 [exec date +%s]
      prove -property $c
      set dt [expr {{[exec date +%s]-$t0}}]
      foreach p $c {{ if {{[done $p]}} {{ rec $p $lvl $dt }} else {{ lappend retry $p }} }}
    }} e]}} {{ puts $out "ERR chunk $j $e"; flush $out; set retry [concat $retry $c] }}
  }}
  return $retry
}}
proc setassumes {{unb}} {{
  global all
  set bnd {{}}
  foreach p $all {{ if {{[lsearch -exact $unb $p] < 0}} {{ lappend bnd $p }} }}
  assume -from_assert $bnd -bound 2
  if {{[llength $unb]}} {{ assume -from_assert $unb }}
}}
if {{{lv} == 0}} {{
  setassumes {{}}
  set_prove_time_limit 20m
  set retry [runchunks $mine 0 20]
  set_prove_time_limit 45m
  foreach p [concat $retry $myslow] {{ runp $p 0 }}
}} elseif {{{lv} == 1}} {{
  setassumes $u1
  set_prove_time_limit 30m
  set retry [runchunks $l1 1 10]
  set_prove_time_limit 45m
  foreach p $retry {{ runp $p 1 }}
}} else {{
  setassumes $u2
  set_prove_time_limit 45m
  foreach p $l2 {{ runp $p 2 }}
}}
'''
open(f"{dst}/run.tcl", "w").write(t[:a] + body + t[b:])
