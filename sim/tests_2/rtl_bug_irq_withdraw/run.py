#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_irq_withdraw: KUDU-072, an interrupt trap reports mcause = machine
timer when the pending line withdraws.

Only fast interrupt 0 is enabled. A pulse of 1-4 cycles on that line is fired
1-12 cycles after an arming store (48 combinations) while straight-line code
runs. A pulse may be missed, but every interrupt taken must report mcause
0x80000010. On HEAD, pulses that drop between the issuer's decision and
ISSUE_SPECIAL are taken with mcause 0x80000007 (COLMON IRQNONE errors; the
handler counts them).

Expected on HEAD: XFAIL (KUDU-072 open).

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
    "rtl_bug_irq_withdraw", ["KUDU-072"],
    [Run("rv32", "simv32", "asm", ["+TIMEOUT=200000"]),
     Run("pmode0_w2", "simv", "asm", ["+PMODE=0", "+TIMEOUT=200000"] + W2)],
    r"^IRQ WITHDRAW PASS",
    [(r"FAIL colmon IRQ(NONE|CAUSE) ", "KUDU-072"), (r"^FAIL irq-withdraw ", "KUDU-072")],
    shadow=Shadow(patches=[COMMON / "patches" / "collide_sched.patch"]),
    post=colmon.post)

if __name__ == "__main__":
    sys.exit(main([TEST]))
