#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_split_mtval_rv32: KUDU-052, a misaligned access whose second half
gets a bus error reports the first word's address in mtval (RV32 program).

lw/lh/lhu/sw/sh at 0x8007fff0 + 13/14/15 straddle the end of DRAM, so the
second half (0x80080000, unmapped) returns a data bus error. Each of the 9
op/offset combinations runs 16 times so that random data wait states reach the
LSU path where the second grant precedes the first rvalid. Every access must
trap with mcause 5 (loads, rd unchanged = 0xdeadbeef) or 7 (stores) and mtval
0x80080000 (Kudu/ibex convention) or the original address (Sail). Before the
fix, with waits, mtval was 0x8007fffc (`FAIL lw+13 ... mtval=8007fffc`, 9/9).

Runs: simv32 and simv at PMODE=0, each with no wait states and with
+DATA_GNT_WMAX=1 +DATA_RESP_WMAX=3 (the reproducing setting). One PASS/FAIL
line per op/offset, then `SPLIT MTVAL PASS` / `FAIL`.

Expected on HEAD: PASS (fixed in a6e599e).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, HW_BOTH, main  # noqa: E402

WAITS = ["+DATA_GNT_WMAX=1", "+DATA_RESP_WMAX=3"]

TEST = Test(
    "rtl_bug_split_mtval_rv32", ["KUDU-052"],
    [Run(hw + "_" + v, sim, "rv32", ["+PMODE=0", "+TIMEOUT=2000000"] + d)
     for hw, sim in HW_BOTH for v, d in (("default", []), ("waits", WAITS))],
    r"^SPLIT MTVAL PASS$",
    [(r"^FAIL (lw|lh|lhu|sw|sh)\+1[345] ", "KUDU-052"), (r"^SPLIT MTVAL FAIL$", "KUDU-052")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
