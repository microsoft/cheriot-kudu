#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_tracer_cebreak directed test.

Reproduces KUDU-058: the c.ebreak trace line had no PC or encoding (the SV
tracer printed a bare "<time> <cycle> c.ebreak"), so compare_trace.py lost
alignment with the Sail trace at the first c.ebreak and miscompared every later
record. Fixed by 6722f7c.

The program is the fuzz reproducer tracer_cebreak (fuzzgen.py FZ_CEBREAK=1,
seed 1; cheri_atest.S for CHERIoT, rv32_atest.S for RV32, one test_main.c
selecting by CHERIOT): a random stream with 5 c.ebreak (.2byte 0x9002), each
trapping to a handler that skips 2 bytes. It prints an "FZSIG" signature
(trap count and hashes) but has no self-check; the original reproducer
compared the trace against the Sail model. The test does not need Sail: the
post hook cebreak_trace_check.py checks that every c.ebreak line has an
8-digit PC and the encoding 9002 and that no trace line other than an
interrupt entry has fewer than five fields ("FAIL KUDU-058 ..."), then prints
"CEBREAK TRACE PASS n=N" (N c.ebreak trace lines, 6-7 on HEAD; required
>= 1).

Runs:
  cheri    cheri program on simv, +PMODE=1
  rv32     rv32 program on simv32, +PMODE=0
  cheriot  rv32 program on simv, +PMODE=0
Expected on HEAD: all PASS (KUDU-058 Fixed).

Run from anywhere: ./run.py [--build <dir>] [--work <new dir>] [--keep_traces]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "common"))
sys.path.insert(0, str(HERE))
from kudu_test import Run, Test, HW_BOTH, main  # noqa: E402
import cebreak_trace_check  # noqa: E402

TEST = Test(
    "rtl_bug_tracer_cebreak",
    ["KUDU-058"],
    [Run("cheri", "simv", "cheri", ["+PMODE=1"], est=5)] +
    [Run(hw, sim, "rv32", ["+PMODE=0"], est=5) for hw, sim in HW_BOTH],
    r"(?s)^FZSIG traps=.*^CEBREAK TRACE PASS n=[1-9]",
    [(r"^FAIL KUDU-058 ", "KUDU-058")],
    post=cebreak_trace_check.post)

if __name__ == "__main__":
    sys.exit(main([TEST]))
