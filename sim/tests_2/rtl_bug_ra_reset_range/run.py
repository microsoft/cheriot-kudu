#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_ra_reset_range test.

Reproduces KUDU-049: the return-address prediction register cur_ra32_q in
ir_stage reset to RALimitLo (0x00080000, a 4 KB page number) instead of
0x80000000. A return predicted after reset, before x1 held an in-range
value, made the front end fetch from unpopulated address 0x00080000.

test.S (bare assembly) places `c.jr ra` on the fall-through path of
always-taken beq instructions: first at _start, before anything writes x1
(the RA review's ra_rst startup sequence), then 8 more times at fresh
addresses after setting x1 to the out-of-range value 0x2000 (ignored by the
RA clamp). ra_rst_chk.sv (extra top-level module in a shadow build) counts
the front end's return predictions and flags any instruction fetch outside
DRAM/debug ROM. It prints "RA_RST FAIL KUDU-049 fetch_oob=N", "RA_RST FAIL
no return predicted ..." (test not exercised) or "RA_RST PASS ...". The
pass verdict also needs the program's "RA RESET PROGRAM DONE".

The original ra_rst replaced the cheri startup.S. The tests_2 cheri flavour
always uses common/csrc_cheri/startup.S, so the sequence was rewritten as an
asm-flavour test (rv32imac, PMODE=0 on simv). RA prediction does not depend
on PMODE.

Expected on HEAD: PASS (bug fixed in 8e3b20b).

Needs the checker, so the runner builds a shadow simv/simv32 (conf1) in the
work directory (--build is not used).

Run from anywhere: ./run.py [--work <new dir>] (see ../common/kudu_test.py and
sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "common"))
from kudu_test import Run, Shadow, Test, main  # noqa: E402

BASE = ["+TIMEOUT=200000"]
WS = ["+INSTR_GNT_WMAX=2", "+INSTR_RESP_WMAX=3", "+DATA_GNT_WMAX=2", "+DATA_RESP_WMAX=3"]

TEST = Test(
    "rtl_bug_ra_reset_range", ["KUDU-049"],
    [Run("rv32", "simv32", "asm", BASE),
     Run("rv32_ws", "simv32", "asm", BASE + WS),
     Run("pmode0", "simv", "asm", ["+PMODE=0"] + BASE)],
    r"(?s)^RA RESET PROGRAM DONE.*^RA_RST PASS",
    [(r"RA_RST FAIL KUDU-049 ", "KUDU-049")],
    shadow=Shadow(extra=[HERE / "ra_rst_chk.sv"]))

if __name__ == "__main__":
    sys.exit(main([TEST]))
