#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_lrsc_load_barrier: KUDU-051, LR.W/SC.W skip the load-barrier (trvk)
hazard after CLC.

22 cases: a capability to a heap object whose granule is marked in the
revocation bitmap is loaded with `clc`, then used 0/2/4/8 instructions later
as the address of lr.w, sc.w, clw, csw and amoadd (20 cases), plus two
non-revoked controls (lr.w, clw). The load barrier must clear the tag, so every
revoked case must trap with a CHERI tag violation (mcause 0x1c, mtval 0x22),
leave rd = 0xdeadbeef and memory = 0x12345678; the controls must not trap.
Before the fix, lr.w/sc.w issued with the stale tagged capability and did not
trap (`FAIL revoked lr.w nops=... trapped=0 rd=0x12345678`; 6/22 failed).

Runs: simv at PMODE=1, with no wait states and with data-side wait states.
Prints one PASS/FAIL line per case and `LSU RVK LRSC PASS` / `FAIL`.

Expected on HEAD: PASS (fixed in 0ab3b26).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Test, cheri_dly, main  # noqa: E402

TEST = Test(
    "rtl_bug_lrsc_load_barrier", ["KUDU-051"], cheri_dly(["+TIMEOUT=2000000"], est=13),
    r"^LSU RVK LRSC PASS$",
    [(r"^FAIL (revoked|control) ", "KUDU-051"), (r"^LSU RVK LRSC FAIL$", "KUDU-051")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
