#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_debug_mode directed test.

Reproduces KUDU-021: ebreak in debug mode does not re-enter debug cleanly
Reproduces KUDU-022: exceptions in debug mode jump to mtvec
Reproduces KUDU-023: illegal CSR accesses do not trap in debug mode
Reproduces KUDU-024: CLC skips load-permission stripping in debug mode
Reproduces KUDU-025: csrw dpc/dscratch0/dscratch1 is silently dropped at PMODE=1

Expected on HEAD: PASS (bug fixed).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, DLY_DBG, main  # noqa: E402

TEST = Test(
    "rtl_bug_debug_mode", ["KUDU-021", "KUDU-022", "KUDU-023", "KUDU-024", "KUDU-025"],
    [Run(v, "simv", "dbg", ["+PMODE=1", "+DBGROM=debug_rom", "+TIMEOUT=400000"] + d, est=13)
     for v, d in (("default", []), ("delayed", DLY_DBG))],
    r"DEBUG MODE SUMMARY PASS",
    [(r"DEBUG MODE D1[ab] ", "KUDU-021"), (r"DEBUG MODE D2 ", "KUDU-022"),
     (r"DEBUG MODE D3 ", "KUDU-023"), (r"DEBUG MODE D4 ", "KUDU-024"),
     (r"DEBUG MODE P1 ", "KUDU-025")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
