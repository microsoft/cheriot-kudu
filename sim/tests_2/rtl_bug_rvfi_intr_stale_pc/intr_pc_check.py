# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Post hook for rtl_bug_rvfi_intr_stale_pc: check the pc of every interrupt
record (intr=1) in rvfi_kudu_core.log.

An interrupt record's pc_rdata must be the pc the interrupt displaced, i.e.
mepc. The test's interrupt handler returns with mret without touching mepc,
so the ground truth is the pc of the first non-interrupt record after the
handler's mret (an interrupt taken again right after that mret has the same
mepc and is resolved by the same record). The other fields of an interrupt
record (insn, pc_wdata, mem masks) are don't-care and are not checked; the
insn is only printed for information.

Prints "FAIL intr-pc ..." for every stale record (the first MAX_SHOWN in
full), then "RVFI INTR PC PASS checked=N" or "RVFI INTR PC SUMMARY FAIL
stale=K checked=N". With no resolvable interrupt record it prints neither, so
the run has no pass verdict.
"""

import gzip
from pathlib import Path

MRET = 0x30200073
MAX_SHOWN = 20
FIELDS = ("trap", "intr", "pc_rdata", "insn")


def packets(path):
    """Yield (packet number, trap, intr, pc_rdata, insn) from the multi-line
    "# --- RVFI packet N ---" records written by rtl/tracer.sv."""
    opener = gzip.open if path.suffix == ".gz" else open
    number, rec = None, {}
    with opener(str(path), "rt", errors="replace") as log:
        for line in log:
            if line.startswith("# --- RVFI packet"):
                if number is not None and len(rec) == len(FIELDS):
                    yield (number,) + tuple(rec[f] for f in FIELDS)
                number, rec = int(line.split()[4]), {}
                continue
            key, sep, value = line.partition(":")
            key = key.strip()
            if sep and key in FIELDS:
                rec[key] = int(value.split()[0], 16)
    if number is not None and len(rec) == len(FIELDS):
        yield (number,) + tuple(rec[f] for f in FIELDS)


def check(run_dir, log_text=None):
    run_dir = Path(run_dir)
    if log_text is not None and "SIGEND" not in log_text:
        return "RVFI INTR PC: the program did not reach SIGEND\n"
    path = run_dir / "rvfi_kudu_core.log"
    if not path.is_file():
        path = run_dir / "rvfi_kudu_core.log.gz"
    if not path.is_file():
        return "RVFI INTR PC ERROR: no rvfi_kudu_core.log in {}\n".format(run_dir)
    out, pending = [], []
    after_mret = False
    checked = stale = 0
    for number, trap, intr, pc, insn in packets(path):
        if intr:
            pending.append((number, pc, insn))
            after_mret = False
            continue
        if after_mret:
            for r_number, r_pc, r_insn in pending:
                checked += 1
                if r_pc != pc:
                    stale += 1
                    if stale <= MAX_SHOWN:
                        out.append("FAIL intr-pc pkt {} pc={:08x} insn={:08x}; handler mret "
                                   "(pkt {}) returns to {:08x} insn={:08x}".format(
                                       r_number, r_pc, r_insn, number - 1, pc, insn))
            pending = []
        after_mret = bool(pending) and insn == MRET and not trap
    if stale > MAX_SHOWN:
        out.append("FAIL intr-pc ... and {} more stale record(s)".format(stale - MAX_SHOWN))
    if stale:
        out.append("RVFI INTR PC SUMMARY FAIL stale={} checked={}".format(stale, checked))
    elif checked:
        out.append("RVFI INTR PC PASS checked={}".format(checked))
    else:
        out.append("RVFI INTR PC: no interrupt record could be checked")
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    import sys
    sys.stdout.write(check(sys.argv[1] if len(sys.argv) > 1 else "."))
