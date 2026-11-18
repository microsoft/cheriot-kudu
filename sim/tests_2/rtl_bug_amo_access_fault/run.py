#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_amo_access_fault directed test.

Reproduces KUDU-008: AMO bus error reports load access fault

Expected on HEAD: PASS (bug fixed).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Test, T1M, main, rv32_both  # noqa: E402

TEST = Test(
    "rtl_bug_amo_access_fault", ["KUDU-008"], rv32_both(T1M),
    r"AMO ACCESS FAULT PASS failures=0x0+ cases=0x00000001", [(r"", "KUDU-008")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
