#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_cap_misaligned_mtval directed test.

Reproduces KUDU-015: Misaligned capability accesses report stale mtval

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
    "rtl_bug_cap_misaligned_mtval", ["KUDU-015"], cheri_dly(T1M),
    r"CAP ALIGN MTVAL PASS failures=0x0+ cases=0x00000002", [(r"", "KUDU-015")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
