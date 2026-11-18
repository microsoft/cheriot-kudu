#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_vcscomp_trace_dpi flow test.

Reproduces KUDU-069: `sim/run/vcscomp -trace_dpi` was silently dropped when
combined with -nowave or -dw, because all three flags wrote the same
VlogArg3 variable and the last one won.

check_vcscomp.sh puts a fake `vcs` (a shell script that only logs its
arguments, environment roots and working directory) first on PATH and runs
the repository's $REPO/sim/run/vcscomp from sim/run, with -outdir=<run dir>/
out_<case>, for these combinations: "-nowave -trace_dpi",
"-trace_dpi -nowave", "-dw -trace_dpi -nowave", "-dw -nowave",
"-conf3 -dii -trace_dpi -nowave" and "-cov -dii -trace_dpi -nowave". For
both vcs calls (simv32 and simv) it checks:
- every expected define is present (TraceDPI, NO_FSDB, KUDU_DW_MULT,
  DII_SIM, KUDU_PPL_CFG);
- CHERIoT is defined for simv only;
- the file list is kudu_dw.vcs.f for -dw and kudu.vcs.f otherwise;
- -cov adds the fcov file list and -cm;
- vcs runs in the -outdir;
- every entry of the selected file list exists.
Each problem prints "FAIL vcscomp <case>: ..."; a clean run prints
"VCSCOMP FLAGS PASS". Before the fix (ff98820) "-nowave -trace_dpi"
lacked +define+NO_FSDB and "-trace_dpi -nowave" lacked +define+TraceDPI.

No real vcs runs and nothing is written to the repository: vcscomp with
-outdir resolves its inputs, then works in the output directory.

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
bash $TEST_DIR/check_vcscomp.sh
"""

TEST = Test(
    "rtl_bug_vcscomp_trace_dpi", ["KUDU-069"],
    [Run("flags", None, None, script=SCRIPT, est=10)],
    r"^VCSCOMP FLAGS PASS",
    [(r"^FAIL vcscomp ", "KUDU-069")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
