#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_failed_sc_tag: KUDU-063, the testbench memory model writes the tag
on a failed SC.W (deferred); also covers KUDU-061 (AMO without SD reports the
wrong fault, fixed).

Two generated LR/SC/AMO sweeps through capabilities (cmem review,
gen_amo.py): cm_amo1.S (330 cases: lr, sc without and with reservation,
amoswap, amoadd, amoor x full/noLD/noSD/noLDnoSD/untagged/sealed authority x
10 geometries: in bounds (low/high word), top-4, at top, straddle, mis+1,
mis+2, misaligned straddle, zero length, length 3) and cm_amo2.S (270 cases:
LDonly/SDonly/dataRW/sealed+noLD/untag+noSD authorities over the same
geometries, every AMO op and SC (with and without reservation) on capability
granules), selected by cheri_atest.S (`cheri+AMO_SWEEP=2` builds the second).
Each case prints a record `R mcause mtval rd ... mem mtag ... idx`;
amo_check.py (post hook) checks every record against a reference model of the
cheriot-sail checks (amo_cases.py holds the case table) and prints a FAIL line
per mismatch, tagged [KUDU-063] (a failed SC.W cleared the memory tag: the
testbench data_mem_model.sv writes dram[..][64] on every store, not gated by
SC success) or [KUDU-061] (only mcause/mtval wrong, AMO through a no-SD cap).

On HEAD: amo1 has 6 and amo2 has 8 [KUDU-063] failures, and no KUDU-061 failure
(21 / 14 before ff98820).

Runs: simv at PMODE=1, each sweep with no wait states and with instruction and
data wait states (+INSTR_*_WMAX=2, +DATA_*_WMAX=3). Each run takes about
4 minutes of simulation (~1 M cycles).

Expected on HEAD: DEFER (KUDU-063 deferred).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
from kudu_test import Run, Test, DLY_DBG, main  # noqa: E402
import amo_check  # noqa: E402

TEST = Test(
    "rtl_bug_failed_sc_tag", ["KUDU-063", "KUDU-061"],
    [Run(sweep + "_" + v, "simv", flavour, ["+PMODE=1", "+TIMEOUT=20000000"] + d, est=230)
     for sweep, flavour in (("amo1", "cheri"), ("amo2", "cheri+AMO_SWEEP=2"))
     for v, d in (("default", []), ("delayed", DLY_DBG))],
    r"^AMO SWEEP amo[12] PASS cases=(330|270)$",
    [(r"^FAIL amo[12] case \d+ \[[^]]*\] \[KUDU-063\]", "KUDU-063"),
     (r"^FAIL amo[12] case \d+ \[[^]]*\] \[KUDU-061\]", "KUDU-061")],
    post=amo_check.post)

if __name__ == "__main__":
    sys.exit(main([TEST]))
