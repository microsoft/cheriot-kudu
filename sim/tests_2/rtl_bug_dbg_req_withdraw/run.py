#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_dbg_req_withdraw: KUDU-073, a withdrawn debug request still enters
debug mode, with dcsr.cause = 0.

A debug_req pulse of 1-4 cycles is fired 1-12 cycles after an arming store
(48 combinations) while straight-line code runs. A 1-cycle pulse may be
ignored; any halt taken must report cause 3 (HALTREQ). On HEAD every 2-cycle
pulse halts with cause 0 (12 COLMON DBGNONE errors, ROM bad-cause count 0xc).

Expected on HEAD: XFAIL (KUDU-073 open).

Needs the collide testbench (common/patches/collide_sched.patch: event
scheduler at 0x8380_0160 plus the COLMON issuer monitor), so the runner builds
a shadow simv/simv32 in the work directory (--build is not used).
common/colmon.py turns every COLMON-ERR line into a FAIL line.

Run from anywhere: ./run.py [--work <new dir>] (see sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
COMMON = Path(__file__).resolve().parents[1] / "common"
sys.path.insert(0, str(COMMON))
from kudu_test import Run, Shadow, Test, main  # noqa: E402
import colmon  # noqa: E402

W2 = ["+INSTR_GNT_WMAX=2", "+INSTR_RESP_WMAX=2", "+DATA_GNT_WMAX=2", "+DATA_RESP_WMAX=3"]

TEST = Test(
    "rtl_bug_dbg_req_withdraw", ["KUDU-073"],
    [Run("rv32", "simv32", "asm", ["+DBGROM=debug_rom", "+TIMEOUT=200000"]),
     Run("pmode0_w2", "simv", "asm", ["+PMODE=0", "+DBGROM=debug_rom", "+TIMEOUT=200000"] + W2)],
    r"^DBG WITHDRAW PASS",
    [(r"FAIL colmon DBGNONE ", "KUDU-073"), (r"^FAIL dbg-withdraw ", "KUDU-073")],
    shadow=Shadow(patches=[COMMON / "patches" / "collide_sched.patch"]),
    post=colmon.post)

if __name__ == "__main__":
    sys.exit(main([TEST]))
