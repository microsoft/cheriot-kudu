#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_depcc_odd directed test.

Reproduces KUDU-077: in CHERIoT mode a DEPCC write (cspecialw, SCR 24) with
an odd address keeps bit 0. cs_registers passes rv32_mepc_wr, rv32_depc_wr
and cheri_mepcc_wr, but not cheri_depcc_wr, as the is_mepcc argument of
legalize_scr, so the CHERIoT DEPCC path skips the bit-0 clear that MEPCC,
mepc and the RV32 dpc get. dret then resumes at the odd address, and a trap
taken there saves an odd mepc (JasperGold CEX of AssertTrapPcEven).

On its first entry after the test sets up its mailbox, the debug ROM writes
DEPCC/dpc with the saved address | 1, reads it back and restores the
original value before dret.
  R1  the read-back DEPCC/dpc has bit 0 clear   (KUDU-077)
  R2  control: the check ran, the written address was odd, and the
      read-back address differs from it only in bit 0

Runs: simv at PMODE=1 (CHERIoT program, the failing path), with and without
wait states, and the RV32 program on simv32 and simv at PMODE=0 as controls
(the RV32 dpc path is already legalized). All use random debug requests.

Expected on HEAD: XFAIL on the cheri runs (KUDU-077 open); PASS on rv32.

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, DLY_ALL3, T1M, main  # noqa: E402

DBG = ["+DBG_REQ_RATE=4", "+DBGROM=debug_rom"] + T1M

TEST = Test(
    "rtl_bug_depcc_odd", ["KUDU-077"],
    [Run("cheri_default", "simv", "cheri", ["+PMODE=1"] + DBG, est=3),
     Run("cheri_waits", "simv", "cheri", ["+PMODE=1"] + DBG + DLY_ALL3, est=3),
     Run("rv32", "simv32", "rv32", ["+PMODE=0"] + DBG, est=3),
     Run("pmode0", "simv", "rv32", ["+PMODE=0"] + DBG, est=3)],
    r"DEPCC ODD PASS failures=0 cases=2",
    [(r"DEPCC ODD R1 ", "KUDU-077")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
