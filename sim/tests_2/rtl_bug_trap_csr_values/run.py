#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_trap_csr_values directed test.

Reproduces KUDU-004: DRET outside debug mode raises CHERI fault
Reproduces KUDU-005: ECALL writes mtval = PC

Expected on HEAD: PASS (bug fixed).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, T1M, main  # noqa: E402

TEST = Test(
    "rtl_bug_trap_csr_values", ["KUDU-004", "KUDU-005"],
    [Run("rv32", "simv32", "rv32", ["+PMODE=0"] + T1M)],
    r"TRAP CSR VALUES PASS failures=0x0+ cases=0x00000006",
    [(r"\bdret_", "KUDU-004"), (r"\becall_mtval\b", "KUDU-005")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
