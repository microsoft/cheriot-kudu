#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_tracer_clc_irq directed test.

Reproduces KUDU-056: tracer CLC/trvk matching breaks after an interrupt, and
final_fifo can overflow. An interrupt-entry record (rvfi.intr = 1) carries the
ir_dec of the instruction it displaced; when that is a CLC, the tracer waited
for a trvk (tag revocation) result that never came, so every later CLC took
the previous one's trvk and was traced with the wrong tag, and the queue could
fall behind until final_fifo wrapped. The core's tags are correct; only
trace_kudu_core.log / rvfi_kudu_core.log are wrong. Fixed by 69b5f26
(is_good_clc also requires ~rvfi.intr; $error on FIFO occupancy > 48).

The program is the issue review's rvk_s1 (cheri_atest.S): a random CHERIoT
stream of CLC/CSC, CH.cgettag and capability ops over a small capability heap,
under interrupts, self-checked against a model ("RW PASS").
Port note: the testbench interrupt interface changed since the original
(+INTR_INTVL gated by bit 2 of 0x83800100 became +INTR_RATE with the mask
register 0x83800108), so the program now unmasks the external line in
intr_mask when it sets bit 2 of 0x83800100, and masks + acks all lines at the
end. +INTR_RATE=5 matches the original +INTR_INTVL=2.

The post hook clc_trace_check.py replays the trace through a shadow register
file: an operand that differs from the last value a CLC wrote to that
register prints "FAIL KUDU-056 ...", as does a tracer FIFO occupancy $error in
sim.log; other shadow mismatches print an unmapped "FAIL TRACE-SHADOW ...".
It counts interrupts whose handler returns (mret) to a CLC, i.e. interrupts
that displaced a CLC, and prints "CLC TRACE PASS irq_displaced_clc=N" only if
N >= 1 and there are no errors.

Runs (cheri program on simv, +PMODE=1, +TIMEOUT=5000000, +INTR_RATE=5,
+DATA_GNT_WMAX=5, +DATA_RESP_WMAX=5):
  irq_s55340  +ntb_random_seed=55340 (the original reproducer seed)
  irq_s1      +ntb_random_seed=1
Expected on HEAD: both PASS (KUDU-056 Fixed).

Run from anywhere: ./run.py [--build <dir>] [--work <new dir>] [--keep_traces]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "common"))
sys.path.insert(0, str(HERE))
from kudu_test import Run, Test, main  # noqa: E402
import clc_trace_check  # noqa: E402

ARGS = ["+PMODE=1", "+TIMEOUT=5000000", "+INTR_RATE=5", "+DATA_GNT_WMAX=5", "+DATA_RESP_WMAX=5"]

TEST = Test(
    "rtl_bug_tracer_clc_irq",
    ["KUDU-056"],
    [Run("irq_s%d" % seed, "simv", "cheri", ARGS + ["+ntb_random_seed=%d" % seed], est=10)
     for seed in (55340, 1)],
    r"(?s)RW PASS.*^CLC TRACE PASS irq_displaced_clc=[1-9]",
    [(r"^FAIL KUDU-056 ", "KUDU-056")],
    post=clc_trace_check.post)

if __name__ == "__main__":
    sys.exit(main([TEST]))
