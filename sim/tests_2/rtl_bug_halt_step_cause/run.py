#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_halt_step_cause directed test.

Reproduces KUDU-040: halt request during single step reports cause STEP

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
    "rtl_bug_halt_step_cause", ["KUDU-040"],
    [Run(v, "simv", "dbg", ["+PMODE=1", "+DBGROM=debug_rom", "+TIMEOUT=400000"] + d)
     for v, d in (("default", []), ("delayed", DLY_DBG))],
    r"HALT STEP CAUSE PASS failures=0 cases=3", [(r"HALT STEP CAUSE H1 ", "KUDU-040")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
