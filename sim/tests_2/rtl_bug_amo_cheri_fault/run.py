#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_amo_cheri_fault directed test.

Reproduces KUDU-032: trapping AMO overwrites rd
Reproduces KUDU-036: trapping AMO saves mstatus.MPIE = 0

Expected on HEAD: PASS (bug fixed).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Test, T1M, cheri_dly, main  # noqa: E402

TEST = Test(
    "rtl_bug_amo_cheri_fault", ["KUDU-032", "KUDU-036"], cheri_dly(T1M),
    r"AMO CHERI FAULT PASS failures=0 cases=8",
    [(r"^FAIL amo-rd ", "KUDU-032"), (r"^FAIL amo-mpie ", "KUDU-036")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
