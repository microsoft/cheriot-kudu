#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_trigger_csr_sail: Kudu vs CHERIoT Sail: Kudu implements the Debug-spec trigger CSRs (tselect,
tdata*); Sail models no triggers and reads tselect as all ones. A documented
model divergence (bug_logs.md, Sail divergences), not a KUDU bug.

Expected on HEAD: DEFER (divergence waived).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, T1M, main  # noqa: E402

TEST = Test(
    "rtl_bug_trigger_csr_sail", [],
    [Run("rv32", "simv32", "rv32", ["+PMODE=0"] + T1M)],
    r"SAIL TRIGGER CSR PASS failures=0x0+ cases=0x00000002",
    [(r"", "SAIL-TRIGGER")], known={"SAIL-TRIGGER": "Waived"}, regression=False)

if __name__ == "__main__":
    sys.exit(main([TEST]))
