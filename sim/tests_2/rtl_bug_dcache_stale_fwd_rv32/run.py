#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_dcache_stale_fwd_rv32: KUDU-050, the dcache forwards stale data
after a misaligned store (RV32 program).

48 generated cases (gen_dcs.py, RAW/WAW hazard review; dcs_r): each pre-fills
the dcache line of word A+4, does a misaligned sw/sh that spans into A+4 (sw to
A+1/A+2/A+3, sh to A+3), then `lw a3, A+4` followed after 0-3 nops by
`xor a4, a3, x0`, and compares both a3 (RF) and a4 (forwarded value) with a
delayed re-read. Before the fix the load hit the stale line while the store
response was still pending and the stale word was forwarded to the xor
(RF correct, a4 stale): 40/48 cases failed.

Runs: simv32 and simv at PMODE=0, each with no wait states and with data-side
wait states. Prints `RW PASS bad=0x00000000 cases=0x00000030` or `RW FAIL ...`
(bad = failing cases, fwd/mem = first bad values, CASES: per-case flags).

Expected on HEAD: PASS (fixed in f61f89d, refined in 6e157c3).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, DLY_DATA, HW_BOTH, T1M, main  # noqa: E402

TEST = Test(
    "rtl_bug_dcache_stale_fwd_rv32", ["KUDU-050"],
    [Run(hw + "_" + v, sim, "rv32", ["+PMODE=0"] + T1M + d)
     for hw, sim in HW_BOTH for v, d in (("default", []), ("delayed", DLY_DATA))],
    r"^RW PASS bad=0x00000000 cases=0x00000030", [(r"^RW FAIL ", "KUDU-050")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
