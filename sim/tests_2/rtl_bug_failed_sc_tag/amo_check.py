# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Post hook of rtl_bug_failed_sc_tag: checks the "R ..." records of the
cm_amo1 / cm_amo2 sweeps against a reference model of the CHERIoT LR/SC/AMO
checks (cheriot-sail ext_data_get_addr order: tag > seal > LD > SD > bounds >
alignment; this Sail build has no A extension, hence a model).

Each mismatching case is printed as a FAIL line tagged with the bug it matches:
  [KUDU-063]  a failed SC.W (no reservation, rd = 1) cleared the memory tag
              (testbench data_mem_model.sv writes the tag on every store);
  [KUDU-061]  only mcause/mtval differ, for an AMO through a cap without SD;
  untagged    anything else (a new problem).
"""

import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import amo_cases  # noqa: E402

LD, SD = 1 << 5, 1 << 2          # CHERIoT perms: GL LG SD LM SL LD MC ...
CAUSE_CHERI = 0x1c
T, SEAL, PLD, PSD, BND = 0x02, 0x03, 0x12, 0x13, 0x01


def ls_check(acc, tag, sealed, perms, base, top, addr, size=4, regnum=5):
    def cheri(code):
        return (CAUSE_CHERI, (regnum << 5) | code)
    if not tag:
        return cheri(T)
    if sealed:
        return cheri(SEAL)
    if acc in ("R", "RW") and not perms & LD:
        return cheri(PLD)
    if acc in ("W", "RW") and not perms & SD:
        return cheri(PSD)
    if not (base <= addr and addr + size <= top):
        return cheri(BND)
    if addr % size:
        return (4 if acc == "R" else 6, addr)
    return None


def amo_op(fn, old, rs2):
    def s(v):
        return v - (1 << 32) if v & 0x80000000 else v
    return {
        "amoswap": rs2, "amoadd": old + rs2, "amoxor": old ^ rs2, "amoor": old | rs2,
        "amoand": old & rs2, "amomin": old if s(old) < s(rs2) else rs2,
        "amomax": old if s(old) > s(rs2) else rs2, "amominu": min(old, rs2),
        "amomaxu": max(old, rs2),
    }[fn] & 0xffffffff


def expect(row, words):
    """Mismatches of one record as (field, got, expected)."""
    _, _, op, tag, sealed, perms, base, top, addr, word_at, rs2 = row
    acc = {"lr": "R", "sc": "W", "sc_resv": "W"}.get(op, "RW")
    fault = ls_check(acc, tag, sealed, perms, base, top, addr)
    old = words[14]                       # memory word before the op
    mem_now = words[10] if (word_at & 7) == 4 else words[9]
    if fault:
        exp = dict(mcause=fault[0], mtval=fault[1], rd=0x5a5a5a5a, mem=old, mtag=1)
    elif op == "lr":
        exp = dict(mcause=0, mtval=0, rd=old, mem=old, mtag=1)
    elif op == "sc":
        exp = dict(mcause=0, mtval=0, rd=1, mem=old, mtag=1)
    elif op == "sc_resv":
        exp = dict(mcause=0, mtval=0, rd=0, mem=rs2, mtag=0)
    else:
        exp = dict(mcause=0, mtval=0, rd=old, mem=amo_op(op, old, rs2), mtag=0)
    got = dict(mcause=words[0], mtval=words[1], rd=words[2], mem=mem_now, mtag=words[12])
    return [(k, got[k], exp[k]) for k in exp if got[k] != exp[k]]


def classify(row, words, bad):
    op, perms = row[2], row[5]
    fields = {k for k, _, _ in bad}
    if op == "sc" and fields == {"mtag"} and words[0] == 0:
        return "[KUDU-063]"
    if op not in ("lr", "sc", "sc_resv") and not perms & SD and fields <= {"mcause", "mtval"}:
        return "[KUDU-061]"
    return ""


def post(run_dir, text):
    sweep = "amo2" if ".amo2_" in Path(run_dir).name else "amo1"
    rows = getattr(amo_cases, sweep.upper())
    recs = {}
    for line in text.splitlines():
        if line.startswith("R "):
            words = line.split()[1:]
            if len(words) == 16 and all(re.fullmatch(r"[0-9a-f]{8}", w) for w in words):
                recs[int(words[15], 16)] = [int(w, 16) for w in words]
    out, nfail = [], 0
    for row in rows:
        idx, desc = row[0], row[1]
        if idx not in recs:
            out.append("FAIL {} case {} [{}]: record missing".format(sweep, idx, desc))
            nfail += 1
            continue
        bad = expect(row, recs[idx])
        if bad:
            nfail += 1
            out.append("FAIL {} case {} [{}] {}: {}".format(
                sweep, idx, desc, classify(row, recs[idx], bad),
                " ".join("{}={:x}(exp {:x})".format(k, g, e) for k, g, e in bad)))
    if nfail:
        out.append("AMO SWEEP {} FAIL failures={} cases={}".format(sweep, nfail, len(rows)))
    else:
        out.append("AMO SWEEP {} PASS cases={}".format(sweep, len(rows)))
    return "\n".join(out) + "\n"
