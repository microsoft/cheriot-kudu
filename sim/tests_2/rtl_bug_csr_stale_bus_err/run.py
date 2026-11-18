#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_csr_stale_bus_err directed test.

Reproduces KUDU-076: after the first half of a misaligned load/store takes a
bus error, the LSU's bus_err_q stays set until the next load/store starts.
A CSR access that fails before then is reported as a load/store access fault
(mcause 5/7, mtval = the faulting split access's address) instead of an
illegal-instruction exception (mcause 2, mtval = insn), because
lsu_err_mcause checks data_or_pmp_err (which includes bus_err_q) before
csr_err.

rv32_atest.S runs five cases; the trap handler makes no memory access, so
nothing clears bus_err_q between the two traps of a case:
  C0 control  illegal csrr 0x5c0 alone
  C1          misaligned lw at 0x7ffffffd (first half unmapped), then csrr 0x5c0
  C2          misaligned sw at 0x7ffffffd, then csrr 0x5c0
  C3          misaligned lw, then csrw mvendorid (read-only)
  C4 control  misaligned lw, an aligned lw, then csrr 0x5c0
Each case must report the first trap as 5/7 with mtval 0x7ffffffd and the CSR
trap as mcause 2 with mtval = the CSR instruction.

Runs: simv32 and simv at PMODE=0, each with no wait states and with
+DATA_GNT_WMAX=3 +DATA_RESP_WMAX=5.

Expected on HEAD: XFAIL (KUDU-076 open; C1-C3 report mcause 5/7).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, DLY_DATA, HW_BOTH, main  # noqa: E402

TEST = Test(
    "rtl_bug_csr_stale_bus_err", ["KUDU-076"],
    [Run(hw + "_" + v, sim, "rv32", ["+PMODE=0", "+TIMEOUT=200000"] + d)
     for hw, sim in HW_BOTH for v, d in (("default", []), ("waits", DLY_DATA))],
    r"CSR BUSERR PASS failures=0 cases=5",
    [(r"CSR BUSERR C[123] ", "KUDU-076")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
