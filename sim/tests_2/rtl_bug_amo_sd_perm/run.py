#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_amo_sd_perm: KUDU-061, an AMO through a capability with LD but no
SD reports a bounds or misaligned fault instead of the SD violation.

4 cases (cmem review, cm_rep_amo), each an AMO through c5 = a 16-byte cap at
0x80023000 with SD removed (perms 0x7b): amoadd in bounds; amoadd at the top;
amoswap misaligned (0x80023002); amoadd through a zero-length cap. Sail checks
tag > seal > LD > SD > bounds > alignment before the AMO's own alignment check,
so every case must trap with mcause 0x1c, mtval 0xb3 (SD violation, rs1 = 5)
and leave rd, memory and tag unchanged. Before the fix cases 1-3 reported
0x1c/0xa1 (bounds) or 6/0x80023002 (misaligned).

The test prints the raw records (`R ...`), then one PASS / `FAIL amo-sd`
(wrong mcause/mtval) / `FAIL amo-state` (rd or memory changed) line per case
and `AMO SD PERM PASS cases=4`. Uses a local link_test.ld (data at 0x8001c000,
clear of the 0x80020000-0x80030fff area the program uses).

Runs: simv at PMODE=1, with no wait states and with data-side wait states.

Expected on HEAD: PASS (fixed in ff98820).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Test, T1M, cheri_dly, main  # noqa: E402

TEST = Test(
    "rtl_bug_amo_sd_perm", ["KUDU-061"], cheri_dly(T1M, est=13),
    r"^AMO SD PERM PASS cases=4$", [(r"^FAIL amo-sd case ", "KUDU-061")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
