# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Post hook of rtl_bug_tracer_clc_irq: replays trace_kudu_core.log through a
shadow register file to check the capability tags the tracer reports for CLC
results after interrupts (KUDU-056).

Each retired, non-trapping line's source operands (xN:0x..+0x..) must equal
the last value retired to that register (the first read of a register only
learns its value). A mismatch whose last writer was a CLC (CH.clc, c.CH.clc,
c.CH.clcsp) is the KUDU-056 symptom (the tracer applied the trvk result of
another CLC); other mismatches are reported unmapped. A tracer FIFO occupancy
$error in sim.log is also KUDU-056 (final_fifo overflow).

The bug needs an interrupt to displace a CLC (the interrupt record carries the
displaced CLC's decode). The hook counts these triggers: interrupt entries
(==>) whose handler returns (mret) to a CLC. It prints
"CLC TRACE PASS ..." only if there are no errors, at least one trigger and at
least one later CLC; otherwise "FAIL KUDU-056 ..." lines, or
"CLC TRACE INEFFECTIVE ..." when the run did not exercise the bug.
"""

import re
from pathlib import Path

RD = re.compile(r"\bx(\d+):(0x[0-9a-fA-FxXzZ]+(?:\+0x[0-9a-fA-FxXzZ]+)?)")
WR = re.compile(r"\bx(\d+)=(0x[0-9a-fA-FxXzZ]+(?:\+0x[0-9a-fA-FxXzZ]+)?)")
CLC = re.compile(r"^(c\.)?CH\.clc(sp)?$")
OVERFLOW = re.compile(r"tracer: \w+ occupancy \d+ > \d+.*")
MAXERR = 10


def norm(value):
    parts = value.lower().split("+")
    return parts[0], (parts[1] if len(parts) > 1 else None)


def same(read, written):
    return read[0] == written[0] and (read[1] is None or written[1] is None
                                      or read[1] == written[1])


def check(path, sim_log):
    errors, other = [], []
    for match in OVERFLOW.finditer(sim_log or ""):
        errors.append("FAIL KUDU-056 tracer FIFO overflow: " + match.group(0))
    shadow = {}  # reg -> (value, line, writer mnemonic)
    in_isr = trigger_wait = False
    triggers = n_clc = 0
    with open(str(path), errors="replace") as trace:
        for ln, line in enumerate(trace, 1):
            parts = line.rstrip("\n").split("\t")
            if len(parts) >= 3 and parts[2].strip().startswith("==>"):
                in_isr = True
                continue
            if len(parts) < 5:
                continue
            try:
                int(parts[2], 16)
            except ValueError:
                continue
            mnem = parts[4].strip()
            trap = mnem.startswith("-->")
            if trigger_wait:
                trigger_wait = False
                triggers += bool(CLC.match(mnem))
            if in_isr and mnem == "mret":
                in_isr, trigger_wait = False, True
            if trap:
                continue
            n_clc += bool(CLC.match(mnem))
            rest = "\t".join(parts[5:])
            for reg, val in RD.findall(rest):
                reg, val = int(reg), norm(val)
                if not reg:
                    continue
                if reg in shadow and not same(val, shadow[reg][0]):
                    wval, wln, wmnem = shadow[reg]
                    msg = "line {}: x{} read {} but last retired write was {} by {} (line {})".format(
                        ln, reg, "+".join(v for v in val if v), "+".join(v for v in wval if v),
                        wmnem, wln)
                    (errors if CLC.match(wmnem) else other).append(msg)
                    shadow[reg] = (val, wln, wmnem)
                elif reg not in shadow or shadow[reg][0][1] is None:
                    shadow[reg] = (val, "learn", "")
            for reg, val in WR.findall(rest):
                if int(reg):
                    shadow[int(reg)] = (norm(val), ln, mnem)
    out = [e if e.startswith("FAIL") else "FAIL KUDU-056 " + e for e in errors[:MAXERR]]
    out += ["FAIL TRACE-SHADOW " + e for e in other[:MAXERR]]
    if len(errors) + len(other) > len(out):
        out.append("CLC TRACE SUMMARY FAIL clc_errors={} other_errors={}".format(
            len(errors), len(other)))
    if not errors and not other:
        verdict = "PASS" if triggers and n_clc else "INEFFECTIVE"
        out.append("CLC TRACE {} irq_displaced_clc={} clc={}".format(verdict, triggers, n_clc))
    return out


def post(run_dir, sim_log):
    trace = Path(run_dir) / "trace_kudu_core.log"
    if not trace.is_file():
        return "CLC TRACE ERROR no trace_kudu_core.log\n"
    return "\n".join(check(trace, sim_log)) + "\n"
