#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_split_store_err: KUDU-052, misaligned accesses where exactly one
half hits an unmapped address (RV32 program).

12 op/offset kinds, 8 iterations each: sw/sh at 0x7ffffff0 + 13/14/15
(first half unmapped, second half 0x80000000 mapped: st1), sw/sh at
0x8007fff0 + 13/14/15 (second half 0x80080000 unmapped: st2), and lw/lhu
with the first half unmapped (ld1). Each access must trap with mcause 7/5;
mtval must be the original address, or for st2 the second word's address
0x80080000; loads must leave rd unchanged; the mapped word must be either
untouched or hold exactly the bytes of the non-faulting half (reported as
`other_half_written` / `not_written`; the spec allows both). Before the fix,
with waits, st2 reported mtval 0x8007fffc
(`FAIL st2 sw+13 ... first_bad 00000007 8007fffc 22334400`).

Runs: simv32 and simv at PMODE=0, each with no wait states and with
+DATA_GNT_WMAX=1 +DATA_RESP_WMAX=3. One INFO/FAIL line per kind, then
`SPLIT WR DONE` (no failure) or `SPLIT WR FAIL`.

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
    "rtl_bug_split_store_err", ["KUDU-052"],
    [Run(hw + "_" + v, sim, "rv32", ["+PMODE=0", "+TIMEOUT=2000000"] + d)
     for hw, sim in HW_BOTH for v, d in (("default", []), ("waits", WAITS))],
    r"^SPLIT WR DONE$",
    [(r"^FAIL (st1|st2|ld1) ", "KUDU-052"), (r"^SPLIT WR FAIL$", "KUDU-052")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
