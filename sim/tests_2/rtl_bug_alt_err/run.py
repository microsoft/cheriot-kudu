#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_alt_err directed test.

Reproduces KUDU-013: Fetch bus error on the second fetch word is imprecise or lost

Expected on HEAD: PASS (bug fixed).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, DLY_SLOT1, HW_BOTH, main  # noqa: E402

TEST = Test(
    "rtl_bug_alt_err", ["KUDU-013"],
    [Run(hw + "_" + v, sim, "rv32",
         ["+PMODE=0", "+INSTR_ERR_ADDR=80010100", "+TIMEOUT=3000000"] + d, est=70)
     for hw, sim in HW_BOTH for v, d in (("default", []), ("delayed", DLY_SLOT1))],
    r"ALTERR PASS failures=0x0+\b", [(r"^ALTERR FAIL KUDU013 ", "KUDU-013")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
