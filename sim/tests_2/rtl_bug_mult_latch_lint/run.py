#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_mult_latch_lint lint test.

Reproduces KUDU-053: in rtl/mult_pipeline.sv the combinational
set_bounds_comb block left outputs unassigned on some paths, so synthesis
and Verilator inferred latches.

The script runs Verilator 5 (`--lint-only -Wall -Wno-fatal`, CHERIoTEn=1,
CHERIoT defined) on the packages, multdiv32.sv and mult_pipeline.sv with
mult_pipeline as the top. Any %Warning-LATCH in mult_pipeline.sv prints
"FAIL KUDU-053 <warning>". A lint %Error or a non-zero exit prints
"FAIL lint ...". As a control, the same command lints a small module with a
deliberate always_comb latch, and the test fails unless Verilator reports
LATCH there. A clean run prints "MULT LATCH LINT PASS". Other warning
classes (UNUSED, WIDTH, ...) are ignored. Before the fix Verilator reported
4 LATCH warnings in mult_pipeline.sv.

The Verilator object directory is in the run directory, so nothing is
written to the repository.

Expected on HEAD: PASS (bug fixed).

Run from anywhere: ./run.py [--work <new dir>] (see ../common/kudu_test.py and
sim/testplan/direct_tests.md). --build is not used.
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, main  # noqa: E402

SCRIPT = r"""
VL=/home/noncad/verilator/5.038/bin/verilator
[ -x "$VL" ] || VL=$(command -v verilator)
if [ -z "$VL" ]; then
  echo "FAIL lint: verilator not found"
  exit 1
fi
$VL --version
R=$REPO/rtl
LINT="--lint-only -Wall -Wno-fatal +define+CHERIoT -I$REPO/prim -I$R"

cat > latch_ctrl.sv <<'EOS'
module latch_ctrl (input logic en_i, input logic [3:0] d_i, output logic [3:0] q_o);
  always_comb begin
    if (en_i) q_o = d_i;
  end
endmodule
EOS
$VL $LINT --Mdir obj_ctrl latch_ctrl.sv --top-module latch_ctrl > lint_ctrl.log 2>&1
if grep -q 'Warning-LATCH' lint_ctrl.log; then
  echo "control: Verilator reports LATCH for latch_ctrl.sv"
else
  cat lint_ctrl.log
  echo "FAIL lint control: Verilator did not report LATCH for latch_ctrl.sv"
fi

$VL $LINT -GCHERIoTEn=1 --Mdir obj_mult $R/cheri_pkg.sv $R/csr_pkg.sv $R/super_pkg.sv \
  $R/kudu_cfg_pkg.sv $R/multdiv32.sv $R/mult_pipeline.sv \
  --top-module mult_pipeline > lint.log 2>&1
rc=$?
echo "verilator exit $rc; warnings by class:"
grep -o '^%Warning-[A-Z0-9_]*' lint.log | sort | uniq -c
[ $rc -eq 0 ] || echo "FAIL lint: verilator exit $rc"
grep '^%Error' lint.log | sed 's/^/FAIL lint: /'
grep '^%Warning-LATCH' lint.log | grep 'mult_pipeline.sv' | sed 's/^/FAIL KUDU-053 /'
nlatch=$(grep '^%Warning-LATCH' lint.log | grep -c 'mult_pipeline.sv')
nerr=$(grep -c '^%Error' lint.log)
if [ $rc -eq 0 ] && [ "$nlatch" -eq 0 ] && [ "$nerr" -eq 0 ] && \
   grep -q 'Warning-LATCH' lint_ctrl.log; then
  echo "MULT LATCH LINT PASS"
fi
"""

TEST = Test(
    "rtl_bug_mult_latch_lint", ["KUDU-053"],
    [Run("lint", None, None, script=SCRIPT, est=20)],
    r"^MULT LATCH LINT PASS",
    [(r"^FAIL KUDU-053 ", "KUDU-053")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
