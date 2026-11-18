#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_sc_forwarding directed test.

Reproduces KUDU-014: Failed SC forwards uncommitted store data

Expected on HEAD: PASS (bug fixed).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, DLY_DATA, T1M, main, rv32_both  # noqa: E402

TEST = Test(
    "rtl_bug_sc_forwarding", ["KUDU-014"],
    rv32_both(T1M) + [Run("cheriot_delayed", "simv", "rv32", ["+PMODE=0"] + T1M + DLY_DATA)],
    r"SC FORWARDING PASS failures=0x0+ cases=0x00000002", [(r"", "KUDU-014")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
