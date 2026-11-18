#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_debug_ecall directed test.

Reproduces KUDU-035: ECALL in debug mode goes to mtvec

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
    "rtl_bug_debug_ecall", ["KUDU-035"],
    [Run(v, "simv", "dbg", ["+PMODE=1", "+DBGROM=debug_rom", "+TIMEOUT=400000"] + d)
     for v, d in (("default", []), ("delayed", DLY_DBG))],
    r"DEBUG ECALL PASS failures=0 cases=2", [(r"DEBUG ECALL E1 ", "KUDU-035")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
