# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Post hook of rtl_bug_mepcc_high_exp: compares the MEPCC metadata the trap
handler reads with `cgethigh x15, c3` (c3 = MEPCC, encoding 0xff7187db) against
the cheriot-sail reference run of the same program.

The program builds malformed PCCs (csethigh, cspecialw mepcc, mret); each one
traps and the handler (186 traps in all) reads MEPCC back. Sail copies the PCC into
MEPCC bit-exactly. KUDU-062: when the PCC exponent is >= 24, Kudu rebuilds B/T
from base/top and loses bits, so cgethigh differs.
"""

import re
from pathlib import Path

CGETHIGH = re.compile(r"\sff7187db\s.*\bx15=0x([0-9a-f]{8})")

# x15 after each cgethigh in the Sail trace, in program order (Sail run of the
# identical ELF: review3 verify/mepcc/sail.log).
SAIL = [
    0x5e00813f, 0x5e000100, 0x5e010000, 0x5e01ffff, 0x5e0020f0, 0x5e00ff01,
    0x5e3c813f, 0x5e3c0100, 0x5e3d0000, 0x5e3dffff, 0x5e3c20f0, 0x5e3cff01,
    0x5e3a813f, 0x5e3a0100, 0x5e3b0000, 0x5e3bffff, 0x5e3a20f0, 0x5e3aff01,
    0x5e38813f, 0x5e380100, 0x5e390000, 0x5e39ffff, 0x5e3820f0, 0x5e38ff01,
    0x5e36813f, 0x5e360100, 0x5e370000, 0x5e37ffff, 0x5e3620f0, 0x5e36ff01,
    0x5e34813f, 0x5e340100, 0x5e350000, 0x5e35ffff, 0x5e3420f0, 0x5e34ff01,
    0x5e32813f, 0x5e320100, 0x5e330000, 0x5e33ffff, 0x5e3220f0, 0x5e32ff01,
    0x5e30813f, 0x5e300100, 0x5e310000, 0x5e31ffff, 0x5e3020f0, 0x5e30ff01,
    0x5e2e813f, 0x5e2e0100, 0x5e2f0000, 0x5e2fffff, 0x5e2e20f0, 0x5e2eff01,
    0x5e2c813f, 0x5e2c0100, 0x5e2d0000, 0x5e2dffff, 0x5e2c20f0, 0x5e2cff01,
    0x5e2a813f, 0x5e2a0100, 0x5e2b0000, 0x5e2bffff, 0x5e2a20f0, 0x5e2aff01,
    0x5e28813f, 0x5e280100, 0x5e290000, 0x5e29ffff, 0x5e2820f0, 0x5e28ff01,
    0x5e26813f, 0x5e260100, 0x5e270000, 0x5e27ffff, 0x5e2620f0, 0x5e26ff01,
    0x5e24813f, 0x5e240100, 0x5e250000, 0x5e25ffff, 0x5e2420f0, 0x5e24ff01,
    0x5e22813f, 0x5e220100, 0x5e230000, 0x5e23ffff, 0x5e2220f0, 0x5e22ff01,
    0x5e20813f, 0x5e200100, 0x5e210000, 0x5e21ffff, 0x5e2020f0, 0x5e20ff01,
    0x5e1e813f, 0x5e1e0100, 0x5e1f0000, 0x5e1fffff, 0x5e1e20f0, 0x5e1eff01,
    0x5e1c813f, 0x5e1c0100, 0x5e1d0000, 0x5e1dffff, 0x5e1c20f0, 0x5e1cff01,
    0x5e1a813f, 0x5e1a0100, 0x5e1b0000, 0x5e1bffff, 0x5e1a20f0, 0x5e1aff01,
    0x5e18813f, 0x5e180100, 0x5e190000, 0x5e19ffff, 0x5e1820f0, 0x5e18ff01,
    0x5e16813f, 0x5e160100, 0x5e170000, 0x5e17ffff, 0x5e1620f0, 0x5e16ff01,
    0x5e14813f, 0x5e140100, 0x5e150000, 0x5e15ffff, 0x5e1420f0, 0x5e14ff01,
    0x5e12813f, 0x5e120100, 0x5e130000, 0x5e13ffff, 0x5e1220f0, 0x5e12ff01,
    0x5e10813f, 0x5e100100, 0x5e110000, 0x5e11ffff, 0x5e1020f0, 0x5e10ff01,
    0x5e0e813f, 0x5e0e0100, 0x5e0f0000, 0x5e0fffff, 0x5e0e20f0, 0x5e0eff01,
    0x5e0c813f, 0x5e0c0100, 0x5e0d0000, 0x5e0dffff, 0x5e0c20f0, 0x5e0cff01,
    0x5e0a813f, 0x5e0a0100, 0x5e0b0000, 0x5e0bffff, 0x5e0a20f0, 0x5e0aff01,
    0x5e08813f, 0x5e080100, 0x5e090000, 0x5e09ffff, 0x5e0820f0, 0x5e08ff01,
    0x5e06813f, 0x5e060100, 0x5e070000, 0x5e07ffff, 0x5e0620f0, 0x5e06ff01,
    0x5e04813f, 0x5e040100, 0x5e050000, 0x5e05ffff, 0x5e0420f0, 0x5e04ff01,
    0x5e02813f, 0x5e020100, 0x5e030000, 0x5e03ffff, 0x5e0220f0, 0x5e02ff01,
]


def post(run_dir, text):
    trace = Path(run_dir) / "trace_kudu_core.log"
    if not trace.is_file():
        return "FAIL mepcc-check: no trace_kudu_core.log\n"
    kudu = [int(m.group(1), 16) for m in map(CGETHIGH.search, trace.read_text(errors="replace").splitlines()) if m]
    out = []
    if len(kudu) != len(SAIL):
        out.append("FAIL mepcc-check: {} cgethigh results in the trace, expected {}".format(len(kudu), len(SAIL)))
    bad = 0
    for n, (got, exp) in enumerate(zip(kudu, SAIL)):
        if got != exp:
            bad += 1
            out.append("FAIL mepcc-high trap {}: cgethigh(MEPCC)=0x{:08x}, Sail 0x{:08x}".format(n, got, exp))
    if out:
        out.append("MEPCC HIGH FAIL failures={} cases={}".format(bad, len(SAIL)))
    else:
        out.append("MEPCC HIGH PASS cases={}".format(len(SAIL)))
    return "\n".join(out) + "\n"
