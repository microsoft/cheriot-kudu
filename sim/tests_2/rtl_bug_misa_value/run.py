#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_misa_value directed test.

Reproduces KUDU-020: misa reads back with bits 31:9 set

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
    "rtl_bug_misa_value", ["KUDU-020"],
    [Run("rv32", "simv32", "rv32", T1M),
     Run("pmode0", "simv", "rv32", ["+PMODE=0"] + T1M),
     Run("pmode1", "simv", "cheri", ["+PMODE=1"] + T1M)],
    r"MISA VALUE .* PASS", [(r"", "KUDU-020")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
