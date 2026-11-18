#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_issuer_debug directed test.

Reproduces KUDU-003: WFI is not woken by a debug halt request
Reproduces KUDU-026: halt request with an empty IR saves a stale dpc
Reproduces KUDU-027: debug-mode entry overwrites MEPC
Reproduces KUDU-028: stepping a trapping instruction runs the handler's first instruction
Reproduces KUDU-029: interrupts are taken while single-stepping
Reproduces KUDU-030: stepped ebreak reports cause STEP instead of EBREAK

Expected on HEAD: PASS (bug fixed).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, DLY_DBG, main  # noqa: E402

TEST = Test(
    "rtl_bug_issuer_debug",
    ["KUDU-003", "KUDU-026", "KUDU-027", "KUDU-028", "KUDU-029", "KUDU-030"],
    [Run(v, "simv", "dbg",
         ["+PMODE=1", "+DBGROM=debug_rom", "+INTR_RATE=6", "+TIMEOUT=400000"] + d, est=17)
     for v, d in (("default", []), ("delayed", DLY_DBG))],
    r"ISSUER DBG SUMMARY PASS",
    [(r"ISSUER DBG I1 ", "KUDU-026"), (r"ISSUER DBG I2 ", "KUDU-028"),
     (r"ISSUER DBG I3 ", "KUDU-029"), (r"ISSUER DBG I4 ", "KUDU-030"),
     (r"ISSUER DBG I5 ", "KUDU-003"), (r"ISSUER DBG I6 ", "KUDU-027")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
