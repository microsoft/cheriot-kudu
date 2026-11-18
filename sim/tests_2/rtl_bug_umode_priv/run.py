#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_umode_priv directed test.

Reproduces KUDU-034: U-mode MRET and WFI are not privileged
Reproduces KUDU-038: M-mode interrupts blocked in U-mode when MIE = 0

Expected on HEAD: PASS (bug fixed).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, DLY_ALL3, HW_BOTH, T1M, main  # noqa: E402

TEST = Test(
    "rtl_bug_umode_priv", ["KUDU-034", "KUDU-038"],
    [Run(hw + "_" + v, sim, "rv32", ["+PMODE=0", "+INTR_RATE=3"] + T1M + d, est=7)
     for hw, sim in HW_BOTH for v, d in (("default", []), ("delayed", DLY_ALL3))],
    r"UPRIV PASS failures=0 cases=4",
    [(r"UPRIV [AB] ", "KUDU-034"), (r"UPRIV C ", "KUDU-038")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
