# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Post hook for tests built with patches/collide_sched.patch.

The patch adds an event scheduler (0x8380_0160) and the COLMON monitor to the
testbench. COLMON checks every debug / interrupt entry in the issuer and prints
"COLMON-ERR> <cycle> <KIND>: ..." for each bad one, plus a final
"COLMON> summary ..." line. This hook turns those into lines the runner
classifies: "FAIL colmon <KIND> ..." per error (at most 20 are listed, then a
count), or "COLMON PASS ..." when the summary reports no errors.
"""

import re

ERR = re.compile(r"^COLMON-ERR> (\d+) (\w+): (.*)$", re.M)
SUMMARY = re.compile(r"^COLMON> summary (.*)$", re.M)
SHOW = 20


def post(run_dir, text):
    errors = ERR.findall(text)
    summary = SUMMARY.search(text)
    lines = ["FAIL colmon {} cycle={} {}".format(kind, cycle, rest)
             for cycle, kind, rest in errors[:SHOW]]
    kinds = sorted({kind for _, kind, _ in errors})
    for kind in kinds:
        count = sum(k == kind for _, k, _ in errors)
        if count > SHOW:
            lines.append("FAIL colmon {} total={}".format(kind, count))
    if summary is None:
        lines.append("COLMON: no summary line (simulation did not finish?)")
    elif not errors:
        lines.append("COLMON PASS " + summary[1])
    else:
        lines.append("COLMON summary " + summary[1])
    return "\n".join(lines) + "\n"
