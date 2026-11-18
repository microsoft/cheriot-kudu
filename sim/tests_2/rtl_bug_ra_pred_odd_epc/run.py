#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_ra_pred_odd_epc directed test.

Reproduces KUDU-075: an interrupt or debug request taken right after a
predicted return through an odd ra/cra saves an odd mepc/dpc. The RA
predictor uses the odd cur_ra as ptarget, the branch unit compares ptarget
with the raw register (no mispredict), and the issuer keeps the odd ptarget
in ir0_nxt_pc_q, which becomes mepc/dpc when IR0 is empty at the trap. The
KUDU-039 fix only cleared bit 0 of the computed JALR target.

The program runs 4000 iterations of `mv ra, <tgt+1>; ret` (rv32_atest.S,
RV32) or `cmove cra, <odd backward sentry>; cret` (cheri_atest.S, CHERIoT).
The interrupt handler and the debug ROM count entries whose mepc/dpc is odd,
record the first one and clear bit 0 before returning.
  R1  no interrupt reports an odd mepc        (KUDU-075)
  R2  no debug entry reports an odd dpc       (KUDU-075)
  R3  control: loop completed, no exception, >= 50 interrupts/debug entries

Runs: simv32, simv at PMODE=0 (RV32 program) and simv at PMODE=1 (CHERIoT
program), each with random interrupts (+INTR_RATE) and with random debug
requests (+DBG_REQ_RATE), all with instruction-side wait states so that IR0
is often empty when the event is taken.

Expected on HEAD: XFAIL (KUDU-075 open).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, DLY_ALL3, T1M, main  # noqa: E402

BUILDS = (("rv32", "simv32", "rv32", []),
          ("pmode0", "simv", "rv32", ["+PMODE=0"]),
          ("cheri", "simv", "cheri", ["+PMODE=1"]))
EVENTS = (("irq", ["+INTR_RATE=4"]),
          ("dbg", ["+DBG_REQ_RATE=4", "+DBGROM=debug_rom"]))

TEST = Test(
    "rtl_bug_ra_pred_odd_epc", ["KUDU-075"],
    [Run(b + "_" + e, sim, flav, pm + ev + T1M + DLY_ALL3, est=10)
     for b, sim, flav, pm in BUILDS for e, ev in EVENTS],
    r"RA ODD EPC PASS failures=0 cases=3",
    [(r"RA ODD EPC R[12] ", "KUDU-075")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
