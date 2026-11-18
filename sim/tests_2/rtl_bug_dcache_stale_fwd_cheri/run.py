#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_dcache_stale_fwd_cheri: KUDU-050, the dcache forwards stale data
after a capability or misaligned store (CHERIoT program).

60 generated cases (gen_dcs.py, RAW/WAW hazard review; dcs_c): each pre-fills
the dcache line of word A+4, does a store that writes A+4 without matching the
one-word store-to-load bypass (`csc` to A, or a misaligned csw/csh spanning
into A+4), then `clw a3, A+4` followed after 0-3 nops by `xor a4, a3, x0`,
and compares both a3 (RF) and a4 (forwarded value) with a delayed re-read.
Before the fix the stale line was forwarded to the xor (e.g. `clw x13` =
0x3333b4b4 but the xor read 0x33333333): 44-48/60 cases failed.

Runs: simv at PMODE=1, with no wait states and with data-side wait states.
Prints `RW PASS bad=0x00000000 cases=0x0000003c` or `RW FAIL ...`.

Expected on HEAD: PASS (fixed in f61f89d, refined in 6e157c3).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Test, T1M, cheri_dly, main  # noqa: E402

TEST = Test(
    "rtl_bug_dcache_stale_fwd_cheri", ["KUDU-050"], cheri_dly(T1M),
    r"^RW PASS bad=0x00000000 cases=0x0000003c", [(r"^RW FAIL ", "KUDU-050")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
