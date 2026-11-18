#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_split_mtval_cheri: KUDU-052, a misaligned access whose second half
gets a bus error reports the first word's address in mtval (CHERIoT program).

The PMODE=1 form of rtl_bug_split_mtval_rv32: clw/clh/clhu/csw/csh at
0x8007fff0 + 13/14/15 straddle the end of DRAM (0x80080000 unmapped, data bus
error on the second half), 16 iterations per op/offset. Every access must trap
with mcause 5/7, rd unchanged, and mtval 0x80080000 or the original address.
Before the fix, with waits, mtval was 0x8007fffc (`FAIL clw+13 ...`).

Runs: simv at PMODE=1 with no wait states, with +DATA_RESP_WMAX=3 (the
reproducing setting of the bug log) and with +DATA_GNT_WMAX=1 +DATA_RESP_WMAX=3.
One PASS/FAIL line per op/offset, then `SPLIT MTVAL C PASS` / `FAIL`.

Expected on HEAD: PASS (fixed in a6e599e).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, main  # noqa: E402

TEST = Test(
    "rtl_bug_split_mtval_cheri", ["KUDU-052"],
    [Run(v, "simv", "cheri", ["+PMODE=1", "+TIMEOUT=2000000"] + d)
     for v, d in (("default", []), ("resp3", ["+DATA_RESP_WMAX=3"]),
                  ("gnt1_resp3", ["+DATA_GNT_WMAX=1", "+DATA_RESP_WMAX=3"]))],
    r"^SPLIT MTVAL C PASS$",
    [(r"^FAIL c(lw|lh|lhu|sw|sh)\+1[345] ", "KUDU-052"), (r"^SPLIT MTVAL C FAIL$", "KUDU-052")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
