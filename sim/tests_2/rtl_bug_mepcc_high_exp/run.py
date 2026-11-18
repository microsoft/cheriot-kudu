#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_mepcc_high_exp: KUDU-062, MEPCC written on a trap loses B/T bits
when the PCC exponent is >= 24 (waived: such a PCC is always an untagged,
malformed capability).

Generated program (capmodel review, gen_capdir.py, cd_mepcc_0): builds
capabilities with csethigh (many exponents and B/T encodings), installs each
one as PCC via cspecialw mepcc + mret, and lets the resulting fetch fault trap.
The handler reads MEPCC (cspecialr c3, mepcc; cgethigh x15, c3) and resumes.
mepcc_check.py (post hook) compares the 186 cgethigh results in
trace_kudu_core.log with those of the cheriot-sail run of the same ELF (Sail
copies PCC into MEPCC bit-exactly). On HEAD the 39 traps whose PCC has E >= 24
differ (e.g. `FAIL mepcc-high trap 144: cgethigh(MEPCC)=0x5e0e803f, Sail
0x5e0e813f`); all other traps match and the program prints
`CHERI CAPDIR DONE`. Needs a local link_test.ld with data at 0x80010000 (the
generated code is larger than the default 16 KB text area).

Runs: simv at PMODE=1 (stock testbench, trace from the default tracer).

Expected on HEAD: DEFER (KUDU-062 waived).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
from kudu_test import Run, Test, main  # noqa: E402
import mepcc_check  # noqa: E402

TEST = Test(
    "rtl_bug_mepcc_high_exp", ["KUDU-062"],
    [Run("pmode1", "simv", "cheri", ["+PMODE=1", "+TIMEOUT=6000000"], est=4)],
    r"^MEPCC HIGH PASS cases=186$",
    [(r"^FAIL mepcc-high trap ", "KUDU-062")],
    post=mepcc_check.post)

if __name__ == "__main__":
    sys.exit(main([TEST]))
