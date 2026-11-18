#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_csr_rmw directed test.

Reproduces KUDU-001: MTVEC/MEPC CSR set/clear corruption

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
    "rtl_bug_csr_rmw", ["KUDU-001"],
    [Run(hw + "_" + v, sim, "rv32", ["+PMODE=0"] + T1M + d, est=7)
     for hw, sim in HW_BOTH for v, d in (("default", []), ("delayed", DLY_ALL3))],
    r"CSR RMW PASS failures=0x0+ cases=0x0000001b", [(r"", "KUDU-001")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
