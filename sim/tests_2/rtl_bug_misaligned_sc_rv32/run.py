#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_misaligned_sc_rv32 directed test.

Reproduces KUDU-031: misaligned LR/SC/AMO reach the bus on the RV32 build

Expected on HEAD: PASS (bug fixed).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, DLY_DATA, HW_BOTH, T1M, main  # noqa: E402

TEST = Test(
    "rtl_bug_misaligned_sc_rv32", ["KUDU-031"],
    [Run(hw + "_" + v, sim, "rv32", ["+PMODE=0"] + T1M + d)
     for hw, sim in HW_BOTH for v, d in (("default", []), ("delayed", DLY_DATA))],
    r"MISALIGNED SC RV32 PASS failures=0 cases=7", [(r"^FAIL misaligned-sc ", "KUDU-031")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
