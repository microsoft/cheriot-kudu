# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Post hook of rtl_bug_tracer_amo: checks how AMOs are reported in
trace_kudu_core.log (and rvfi_kudu_core.log, which only DII builds write).

For every retired, non-trapping AMO (opcode 0x2f, funct3 010, not LR/SC):
  * the traced mnemonic matches funct5 (amoand.w printed as INVALID: KUDU-057);
  * the traced rd operand equals the encoding's rd, and for rd != x0 the line
    has an `xN=` write whose value equals its `load:` value (KUDU-055);
  * a shadow register file replayed over the whole trace sees every later
    read of an AMO's rd return the traced write value (KUDU-055).
The RVFI log, when present, must report rd_addr = encoding rd and
rd_wdata = mem_rdata for every AMO (KUDU-055).

Output: "FAIL KUDU-0xx ..." lines, or "AMO TRACE PASS ..." when everything
checks and the trace holds at least one amoand.w and one AMO with rd != x0.
"""

import re
from pathlib import Path

AMO_NAMES = {0x00: "amoadd.w", 0x01: "amoswap.w", 0x04: "amoxor.w", 0x08: "amoor.w",
             0x0c: "amoand.w", 0x10: "amomin.w", 0x14: "amomax.w", 0x18: "amominu.w",
             0x1c: "amomaxu.w"}
RD = re.compile(r"\bx(\d+):(0x[0-9a-fA-FxXzZ?]+(?:\+0x[0-9a-fA-FxXzZ?]+)?)")
WR = re.compile(r"\bx(\d+)=(0x[0-9a-fA-FxXzZ?]+(?:\+0x[0-9a-fA-FxXzZ?]+)?)")
LOAD = re.compile(r"\bload:(0x[0-9a-fA-F?]+)")
MAXERR = 10


def limit(errors):
    """At most MAXERR lines per bug tag, so one bug cannot hide another."""
    shown, kept = {}, []
    for e in errors:
        tag = e.split()[1]
        shown[tag] = shown.get(tag, 0) + 1
        if shown[tag] <= MAXERR:
            kept.append(e)
    kept += ["FAIL {} ... {} more error(s)".format(t, n - MAXERR)
             for t, n in shown.items() if n > MAXERR]
    return kept


def is_amo(insn):
    return (insn & 0x707f) == 0x202f and (insn >> 27) in AMO_NAMES


def check_trace(path, out):
    errors = []
    shadow = {}  # reg -> (value, line number, is_amo)
    n_amo = n_rd = n_and = 0
    with open(str(path), errors="replace") as trace:
        for ln, line in enumerate(trace, 1):
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 5:
                continue
            try:
                int(parts[2], 16)
                insn = int(parts[3], 16)
            except ValueError:
                continue
            mnem = parts[4].strip()
            trap = mnem.startswith("-->")
            rest = "\t".join(parts[5:])
            amo = len(parts[3].strip()) == 8 and is_amo(insn)
            if amo:
                funct5, rd = insn >> 27, (insn >> 7) & 31
                bug = "KUDU-057" if funct5 == 0x0c else "AMO-NAME"
                if mnem.replace("-->", "", 1) != AMO_NAMES[funct5]:
                    errors.append("FAIL {} line {}: {:08x} traced as '{}', expected '{}'".format(
                        bug, ln, insn, mnem, AMO_NAMES[funct5]))
                elif not trap:
                    n_amo += 1
                    n_and += funct5 == 0x0c
                    ops = parts[5].split(",")[0].strip() if len(parts) > 5 else ""
                    writes = dict(WR.findall(rest))
                    load = LOAD.search(rest)
                    if ops != "x{}".format(rd):
                        errors.append("FAIL KUDU-055 line {}: {} rd operand '{}', encoding rd "
                                      "x{}".format(ln, mnem, ops, rd))
                    elif rd:
                        n_rd += 1
                        if str(rd) not in writes:
                            errors.append("FAIL KUDU-055 line {}: {} x{} has no rd write".format(
                                ln, mnem, rd))
                        elif not load or int(load.group(1).replace("?", "0"), 16) != \
                                int(writes[str(rd)], 16):
                            errors.append("FAIL KUDU-055 line {}: {} x{}={} but load:{}".format(
                                ln, mnem, rd, writes[str(rd)],
                                load.group(1) if load else "missing"))
            if trap:
                continue
            for reg, val in RD.findall(rest):
                reg = int(reg)
                if reg and reg in shadow and shadow[reg][0] != val.lower() and shadow[reg][2]:
                    errors.append("FAIL KUDU-055 line {}: x{} read {} but AMO at line {} wrote "
                                  "{}".format(ln, reg, val, shadow[reg][1], shadow[reg][0]))
                if reg and (reg not in shadow or shadow[reg][1] == 0):
                    shadow[reg] = (val.lower(), 0, False)
            for reg, val in WR.findall(rest):
                if int(reg):
                    shadow[int(reg)] = (val.lower(), ln, amo)
    out.extend(limit(errors))
    return errors, n_amo, n_rd, n_and


def check_rvfi(path, out):
    errors, pkt = [], {}

    def done():
        if "insn" in pkt and is_amo(pkt["insn"]) and not pkt.get("trap"):
            rd = (pkt["insn"] >> 7) & 31
            if pkt.get("rd") != rd or (rd and (pkt.get("rd_wdata", 0) ^ pkt.get("mem_rdata", 0)) & 0xffffffff):
                errors.append("FAIL KUDU-055 rvfi packet {}: insn {:08x} rd=x{} wdata={:x} "
                              "mem_rdata={:x}, encoding rd x{}".format(
                                  pkt.get("n"), pkt["insn"], pkt.get("rd"), pkt.get("rd_wdata", 0),
                                  pkt.get("mem_rdata", 0), rd))
        pkt.clear()

    with open(str(path), errors="replace") as rvfi:
        for line in rvfi:
            m = re.match(r"# --- RVFI packet (\d+)", line)
            if m:
                done()
                pkt["n"] = int(m.group(1))
                continue
            m = re.match(r"(\w+)\s*:\s*(.*)", line)
            if not m:
                continue
            key, val = m.groups()
            if key == "insn":
                pkt["insn"] = int(val, 16)
            elif key == "trap":
                pkt["trap"] = int(val, 16)
            elif key == "rd":
                r = re.match(r"x(\d+)\s+wdata=0x([0-9a-fA-F]+)", val)
                if r:
                    pkt["rd"], pkt["rd_wdata"] = int(r.group(1)), int(r.group(2), 16)
            elif key == "mem_rdata":
                pkt["mem_rdata"] = int(val, 16)
    done()
    out.extend(limit(errors))
    return errors


def post(run_dir, sim_log):
    run_dir = Path(run_dir)
    out = []
    trace = run_dir / "trace_kudu_core.log"
    if not trace.is_file():
        return "AMO TRACE ERROR no trace_kudu_core.log\n"
    errors, n_amo, n_rd, n_and = check_trace(trace, out)
    rvfi = run_dir / "rvfi_kudu_core.log"
    rvfi_note = "absent (non-DII build)"
    if rvfi.is_file():
        errors += check_rvfi(rvfi, out)
        rvfi_note = "checked"
    if not errors:
        if n_and and n_rd:
            out.append("AMO TRACE PASS amos={} rd_nonzero={} amoand={} rvfi={}".format(
                n_amo, n_rd, n_and, rvfi_note))
        else:
            out.append("AMO TRACE INEFFECTIVE amos={} rd_nonzero={} amoand={}".format(
                n_amo, n_rd, n_and))
    return "\n".join(out) + "\n"
