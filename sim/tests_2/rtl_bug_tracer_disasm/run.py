#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_tracer_disasm directed test (tracer disassembly, SV vs DPI-C).

Reproduces:
  KUDU-064  DPI tracer prints amomin/amomax/amominu as amoadd/amoxor/amoor
  KUDU-065  SV tracer truncates the c.CH.clcsp / c.CH.cscsp offset to 8 bits
  KUDU-066  SV tracer prints a bare INVALID (no PC/encoding) for loads with funct3 = 6/7
  KUDU-067  tracer decode patterns disagree with the core decoder (SYSTEM,
            CHERI single-operand ops, fence.i)
  KUDU-068  unnamed CSR / SCR operands formatted differently by the two tracers
and, as a by-product, KUDU-057 (amoand.w printed as INVALID) and KUDU-058
(bare c.ebreak line), which are also covered by trace tests of their own.

What it does: a script run compiles tb_trc.sv with vcs against the
repository's tracer sources (rtl/{cheri,csr,super,kudu_cfg,tracer}_pkg.sv and
rtl/tracer_dpi.cpp, i.e. both the default SV formatter and the -trace_dpi C
formatter), once with +define+CHERIoT (pmode 0 and 1) and once for RV32. The
standalone testbench (no core) then
  * feeds a directed table of encodings taken from the bug reports (e.g.
    a00eafaf amomax.w, 6016 c.CH.clcsp 320(c0), e226 c.CH.cscsp 256(..),
    000be783 INVALID, 00090e73 INVALID, 0180180f fence.i, csr 0x006, scr 4)
    to both formatters and checks PC, encoding, mnemonic and operand text
    ("TRC FAIL GOLDEN class=..." on a miss);
  * runs the differential sweep of the original review ($TC/tb_trc.sv:
    every 16-bit encoding, every opcode x funct3 x funct7 x rs2, every
    CSR x funct3, 500 K random words, random register/memory/trap data) and
    reports every SV/C disagreement as "TRC FAIL MISMATCH class=...".
Each failure line carries an instruction class that the checks map to a bug.
This needs no -trace_dpi core build (the harness has none): the C formatter
is exercised directly through tracer_dpi_wrapper.sv (included from rtl/).
Validated against the pre-fix tracer sources (rtl/ of 0ab3b26^): every class
fails (41 GOLDEN and 36 MISMATCH lines on the two builds), and the harness
reports KUDU-057, 058 and 064-068 failing.

Runs: script "cheri_rv32" (no simv/program), about 1-2 min of farm time.
Expected on HEAD: PASS ("TRACER DISASM PASS build=cheri" and "build=rv32";
all fixed in 0ab3b26, c7598d2 and 6722f7c).

Run from anywhere: ./run.py [--work <new dir>] (see ../common/kudu_test.py and
sim/testplan/direct_tests.md). --build is not used.
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, main  # noqa: E402

SCRIPT = r"""
rtl=$REPO/rtl
for b in cheri rv32; do
  def=""; [ $b = cheri ] && def="+define+CHERIoT"
  mkdir -p build_$b
  ( cd build_$b && vcs -full64 -sverilog -xlrm uniq_prior_final +systemverilogext+sv \
      -timescale=1ns/1ps $def +define+RVFI +incdir+$rtl \
      $rtl/cheri_pkg.sv $rtl/csr_pkg.sv $rtl/super_pkg.sv $rtl/kudu_cfg_pkg.sv \
      $rtl/tracer_pkg.sv $rtl/tracer_dpi.cpp $TEST_DIR/tb_trc.sv \
      -top tb_trc -o simv -l comp.log > /dev/null 2>&1 )
  if [ ! -x build_$b/simv ]; then
    echo "TRC COMPILE FAIL build=$b (see $PWD/build_$b/comp.log)"
    grep -m10 -A3 "^Error" build_$b/comp.log
    continue
  fi
  ( cd build_$b && ./simv +seed=7 +maxlog=3 ) | grep "^TRC\|^TRACER\|^    \(SV\|C\) *:"
done
"""

TEST = Test(
    "rtl_bug_tracer_disasm",
    ["KUDU-057", "KUDU-058", "KUDU-064", "KUDU-065", "KUDU-066", "KUDU-067", "KUDU-068"],
    [Run("cheri_rv32", None, None, script=SCRIPT, est=150)],
    r"(?s)TRACER DISASM PASS build=cheri.*TRACER DISASM PASS build=rv32",
    [(r"class=cebreak\b", "KUDU-058"),
     (r"class=amo\b.*insn=6", "KUDU-057"),
     (r"class=amo\b", "KUDU-064"),
     (r"class=clcsp\b", "KUDU-065"),
     (r"class=load_f3\b", "KUDU-066"),
     (r"class=(system|cheri1op|fencei)\b", "KUDU-067"),
     (r"class=(csr|scr)\b", "KUDU-068")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
