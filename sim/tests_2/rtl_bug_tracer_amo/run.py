#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_tracer_amo directed test.

Reproduces two tracer bugs in how AMOs are reported:
  KUDU-055  AMOs traced and RVFI-reported with rd = x0 (rd_addr/rd_wdata were
            captured in the AMO read phase, where rf_we is 0 after KUDU-032),
            and with load:0x00000000 (mem_rdata captured in the same phase).
            Fixed by c7598d2 + 69b5f26.
  KUDU-057  amoand.w disassembled as INVALID with no rd write. Fixed by c7598d2.
The core itself writes rd correctly; only trace_kudu_core.log /
rvfi_kudu_core.log are wrong.

The program is the issue review's is_r_s501_amo_nobus (rv32_atest.S, seed
501): a random RV32 stream of AMOs (all nine AMO ops), LR/SC, loads/stores and
ALU ops over a small data area, self-checked against a model ("RW PASS").
Port note: the testbench interrupt interface changed since the original
(+INTR_INTVL gated by bit 2 of 0x83800100 became +INTR_RATE with the mask
register 0x83800108), so the program now unmasks the external line in
intr_mask when it sets bit 2 of 0x83800100, and masks + acks all lines at the
end. +INTR_RATE=5 matches the original +INTR_INTVL=2.

The post hook amo_trace_check.py checks the trace (and rvfi_kudu_core.log,
which only DII builds write, when present): every retired AMO must carry the
right mnemonic ("FAIL KUDU-057" for amoand.w, an unmapped FAIL for other
names), the encoding's rd as rd operand, an xN= write equal to its load:
value, and a shadow register file replayed over the trace must agree with
every later read of an AMO's rd ("FAIL KUDU-055"). It prints
"AMO TRACE PASS amos=N rd_nonzero=M amoand=K" only if the trace holds at least
one amoand.w and one AMO with rd != x0.

Runs (rv32 program, +PMODE=0, +TIMEOUT=5000000):
  {rv32 (simv32), cheriot (simv)} x
  {default, irq_delayed (+INTR_RATE=5, all memory wait states up to 3)}.
Expected on HEAD: all PASS (both bugs Fixed).

Run from anywhere: ./run.py [--build <dir>] [--work <new dir>] [--keep_traces]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "common"))
sys.path.insert(0, str(HERE))
from kudu_test import Run, Test, DLY_ALL3, HW_BOTH, main  # noqa: E402
import amo_trace_check  # noqa: E402

VARIANTS = (("default", []), ("irq_delayed", ["+INTR_RATE=5"] + DLY_ALL3))

TEST = Test(
    "rtl_bug_tracer_amo",
    ["KUDU-055", "KUDU-057"],
    [Run(hw + "_" + v, sim, "rv32", ["+PMODE=0", "+TIMEOUT=5000000"] + args, est=10)
     for hw, sim in HW_BOTH for v, args in VARIANTS],
    r"(?s)RW PASS.*^AMO TRACE PASS amos=[1-9]",
    [(r"^FAIL KUDU-055 ", "KUDU-055"), (r"^FAIL KUDU-057 ", "KUDU-057")],
    post=amo_trace_check.post)

if __name__ == "__main__":
    sys.exit(main([TEST]))
