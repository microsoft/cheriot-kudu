#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_debug_irq_not_ignored directed test.

Reproduces KUDU-012: Interrupts are taken in debug mode

Expected on HEAD: PASS (bug fixed).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, main  # noqa: E402

TEST = Test(
    "rtl_bug_debug_irq_not_ignored", ["KUDU-012"],
    [Run("cheriot", "simv", "dbg",
         ["+PMODE=1", "+DBGROM=debug_rom", "+INTR_RATE=6", "+TIMEOUT=300000"])],
    r"DEBUG IRQ PASS cases=0x00000001", [(r"", "KUDU-012")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
