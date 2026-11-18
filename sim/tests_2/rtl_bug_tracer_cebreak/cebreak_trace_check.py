# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Post hook of rtl_bug_tracer_cebreak: checks that every c.ebreak line of
trace_kudu_core.log has its PC and encoding fields (KUDU-058).

Trace lines are tab-separated: time, cycle, PC, encoding, mnemonic, operands,
register/memory contents. Interrupt entries (==> in the PC field) are the only
lines allowed to have fewer than five fields. A c.ebreak line must carry an
8-digit hex PC and the encoding 9002; any other short line is also reported,
since it breaks compare_trace.py the same way.

Output: "FAIL KUDU-058 ..." lines, or "CEBREAK TRACE PASS n=N" when the trace
holds at least one c.ebreak and every line is well formed.
"""

import re
from pathlib import Path

PC = re.compile(r"^[0-9a-fA-F]{8}$")
MAXERR = 10


def check(path):
    errors, n_cebreak = [], 0
    with open(str(path), errors="replace") as trace:
        for ln, line in enumerate(trace, 1):
            parts = line.rstrip("\n").split("\t")
            if ln == 1 or not line.strip():
                continue
            if len(parts) >= 3 and parts[2].strip().startswith("==>"):
                continue
            cebreak = "c.ebreak" in line
            n_cebreak += cebreak
            if len(parts) < 5:
                errors.append("FAIL KUDU-058 line {}: {} line has {} field(s), no PC/encoding: "
                              "{}".format(ln, "c.ebreak" if cebreak else "trace", len(parts),
                                          line.strip()))
            elif cebreak and not (PC.match(parts[2].strip()) and parts[3].strip() == "9002"):
                errors.append("FAIL KUDU-058 line {}: c.ebreak with PC '{}' encoding '{}'".format(
                    ln, parts[2].strip(), parts[3].strip()))
    out = errors[:MAXERR]
    if len(errors) > MAXERR:
        out.append("CEBREAK TRACE SUMMARY FAIL errors={}".format(len(errors)))
    if not errors:
        out.append("CEBREAK TRACE {} n={}".format("PASS" if n_cebreak else "INEFFECTIVE",
                                                  n_cebreak))
    return out


def post(run_dir, sim_log):
    trace = Path(run_dir) / "trace_kudu_core.log"
    if not trace.is_file():
        return "CEBREAK TRACE ERROR no trace_kudu_core.log\n"
    return "\n".join(check(trace)) + "\n"
