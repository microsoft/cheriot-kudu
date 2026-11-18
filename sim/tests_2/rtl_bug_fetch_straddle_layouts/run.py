#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_fetch_straddle_layouts directed test.

Reproduces KUDU-013 (straddle case): a fetch bus error on the second fetch
word was imprecise or lost. Here a 32-bit instruction `addi a3,x0,6` starts
at 0x8001005e and its upper half lies in the faulting 64-bit word
0x80010060 (+INSTR_ERR_ADDR=80010060). The required trap is an instruction
access fault with mcause 1, mepc 0x8001005e and mtval 0x80010060 (pc + 2),
and neither a3 nor the following instructions may execute.

test_main.c writes the code into RAM at 0x80010000 with 8 layouts of the
16/32-bit instructions in the two preceding 64-bit words, and enters it
either by jumping to each instruction boundary or after a DIV stall with
0-5 NOP words of padding. The fetch aligner therefore hands the straddler
out as slot 0 or slot 1 with different fetch-FIFO states (94 tries). A
no-error control copy at 0x80011000 must run without a trap. Each try prints
an "FSTR_INFO ..." line; the run ends with "FSTR PASS tries=.. fails=0 ..."
or "FSTR FAIL tries=.. fails=N mtval_eq_pc=.. other=.. ctrl_bad=..". Before
the fix (e79286b) the straddle reported mtval = pc, or was lost when the
straddler was in slot 1.

This complements rtl_bug_fetch_slot1_err and rtl_bug_alt_err, which cover
only a fetch error in the slot-1 word, not an instruction straddling into
the error word.

Runs: rv32 (simv32) and cheriot (simv, PMODE=0), each with default and
delayed instruction/data memory.

Expected on HEAD: PASS (bug fixed).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, HW_BOTH, main  # noqa: E402

DLY = ["+INSTR_GNT_WMAX=2", "+INSTR_RESP_WMAX=2", "+DATA_GNT_WMAX=2", "+DATA_RESP_WMAX=2"]

TEST = Test(
    "rtl_bug_fetch_straddle_layouts", ["KUDU-013"],
    [Run(hw + "_" + v, sim, "rv32",
         ["+PMODE=0", "+INSTR_ERR_ADDR=80010060", "+TIMEOUT=3000000"] + d, est=70)
     for hw, sim in HW_BOTH for v, d in (("default", []), ("delayed", DLY))],
    r"^FSTR PASS tries=", [(r"^FSTR FAIL ", "KUDU-013")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
