#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Focused LSU functional-coverage semantics regression."""

from pathlib import Path
from collections import Counter
import os
import re
import subprocess
import sys
import uuid
from isa_operand_reference import permissions, permission_category


def require(value, detail):
    if not value:
        raise AssertionError(detail)


def section(text, kind, name):
    marker = f"Summary for {kind} {name}\n"
    require(marker in text, ("missing section", marker))
    return text.split(marker, 1)[1].split("Summary for ", 1)[0]


def row(group, name):
    for line in group.splitlines():
      fields = line.split()
      if fields and fields[0] == name and len(fields) > 6:
          return fields
    raise AssertionError(("missing row", name))


def bins(text, name, cross=False):
    body = section(text, "Cross" if cross else "Variable", name)
    result = {}
    for line in body.splitlines():
        fields = line.split()
        if not fields:
            continue
        axes = 2 if cross else 1
        if len(fields) > axes and fields[axes].isdigit():
            result[tuple(fields[:axes]) if cross else fields[0]] = int(fields[axes])
    return result


def masked_permissions(code, mask, sealed):
    result = permissions(code)
    if mask & 8:
        return result
    if mask & 1:
        result -= {"GL"} if sealed else {"GL", "LG"}
    if mask & 2 and not sealed:
        result -= {"SD", "LM"}
    # Recompression drops permissions not representable in the remaining category.
    if {"EX", "MC", "LD"} <= result:
        retained = {"GL", "EX", "MC", "LD", "LG", "LM", "SR"}
    elif {"LD", "MC", "SD"} <= result:
        retained = {"GL", "LD", "MC", "SD", "LG", "LM", "SL"}
    elif {"LD", "MC"} <= result:
        retained = {"GL", "LD", "MC", "LG", "LM"}
    elif {"SD", "MC"} <= result:
        retained = {"GL", "SD", "MC"}
    elif {"LD", "SD"} & result:
        retained = {"GL", "LD", "SD"}
    else:
        retained = {"GL", "US", "SE", "U0"}
    return result & retained


def check_permissions(root, hardware):
    work = root / f"hw{hardware}" / "permissions"
    log = (work / "simulation.log").read_text()
    require(f"PASS LSU permission coverage HW={hardware}" in log, work)
    require(not re.search(r"(?:Error|Fatal|Warning)-|FCOV:", log), (work, log))
    text = (work / "report/grpinfo.txt").read_text().split(
        "Summary for Group Instance   FC_MA_LSU.lspl\n", 1)[1].split(
            "Summary for Group ", 1)[0]
    wanted_cross, wanted_bits = Counter(), Counter()
    labels = ("global", "load_global", "load_mutable", "store", "capability", "store_local")
    for code in range(64) if hardware else ():
        before = permissions(code)
        for sealed in (False, True):
            for mask in (0, 1, 2, 3, 11):
                mask_bin = f"some_{mask:x}" if mask else "none"
                wanted_cross[permission_category(code), mask_bin] += 1
                after = masked_permissions(code, mask, sealed)
                for bit, label in zip(("GL", "LG", "LM", "SD", "MC", "SL"), labels):
                    wanted_bits[f"{label}_{int(bit in before)}{int(bit in after)}"] += 1
    actual_cross = {k: v for k, v in bins(text, "x_resp_clrperm_2", True).items() if v}
    actual_bits = {k: v for k, v in bins(text, "cp_resp_cap_perm_bits").items() if v}
    require(actual_cross == wanted_cross, (work, "category/mask counts", actual_cross, wanted_cross))
    require(actual_bits == wanted_bits, (work, "permission-bit counts", actual_bits, wanted_bits))
    require(row(text, "x_resp_clrperm_2")[1] == "30", work)
    require(row(text, "cp_resp_cap_perm_bits")[1] == "18", work)
    print(f"PASS hw{hardware}: exhaustive LSU permission categories and bit effects", flush=True)


def check(root):
    for hw in (0, 1):
        work = root / f"hw{hw}" / "positive"
        log = (work / "simulation.log").read_text()
        require(f"PASS LSU semantics HW={hw}" in log, work)
        require(not re.search(r"(?:Error|Fatal|Warning)-|FCOV:", log), (work, log))
        text = (work / "report/grpinfo.txt").read_text()
        lsu = text.split("Summary for Group Instance   FC_MA_LSU.lspl\n", 1)[1].split(
            "Summary for Group ", 1)[0]
        expect_weight = str(hw)
        for name, goals in (
            ("cp_cheri_req_cause", 7),
            ("cp_resp_early_cheri_cause", 5),
            ("cp_resp_cap_top_path", 8),
            ("cp_resp_cap_perm_effect", 13),
            ("cp_resp_cap_tag_outcome", 3),
        ):
            fields = row(lsu, name)
            require(int(fields[1]) == goals and fields[6] == expect_weight,
                    (work, name, fields))
        require(row(lsu, "x_split_err_phase")[1] == "8", (work, row(lsu, "x_split_err_phase")))
        straddle = bins(text, "cp_unaligned_two_matches")
        wanted = {f"{d}_{k}": 1 for d in ("store", "load")
                  for k in ("word_off1", "word_off2", "word_off3", "half_off3")}
        require(straddle == wanted, (work, "straddle counts", straddle, wanted))
        if hw:
            trvk = text.split("Summary for Group Instance   FC_MA_LSU.trvk\n", 1)[1].split(
                "Summary for Group ", 1)[0]
            require(row(trvk, "x_selected_bit")[1] == "64" and
                    row(trvk, "x_selected_bit")[2] == "0", (work, row(trvk, "x_selected_bit")))
            require(row(trvk, "cp_range_boundary")[1] == "5" and
                    row(trvk, "cp_range_boundary")[2] == "0",
                    (work, row(trvk, "cp_range_boundary")))
            require(row(trvk, "cp_b2b_revocation_outcome")[1] == "2" and
                    row(trvk, "cp_b2b_revocation_outcome")[2] == "0",
                    (work, row(trvk, "cp_b2b_revocation_outcome")))
        print(f"PASS hw{hw}: LSU semantics report checks", flush=True)
        check_permissions(root, hw)


def run(command, directory, log):
    print(f"{directory}: {' '.join(map(str, command))}", flush=True)
    with (directory / log).open("x") as output:
        result = subprocess.run(list(map(str, command)), cwd=directory, stdout=output,
                                stderr=subprocess.STDOUT, timeout=600)
    require(result.returncode == 0, (command, directory / log, result.returncode))


def main():
    if len(sys.argv) > 1:
        require(len(sys.argv) == 3 and sys.argv[1] == "--check",
                "Usage: run_lsu_semantics.py [--check DIRECTORY]")
        check(Path(sys.argv[2]).resolve())
        return
    sim = Path(__file__).resolve().parent.parent
    os.chdir(sim)
    root = Path("temp") / ("lsu_semantics_" + uuid.uuid4().hex[:12])
    root.mkdir(parents=True, exist_ok=False)
    root = root.resolve()
    scratch = root / "tool_scratch"
    scratch.mkdir()
    os.environ["TMPDIR"] = str(scratch)
    print(f"Artifacts: {root}", flush=True)
    rtl = sim.parent / "rtl"
    sources = [rtl / (name + ".sv") for name in
               ("kudu_cfg_pkg", "cheri_pkg", "csr_pkg", "super_pkg")]
    sources += [sim / "fcov" / (name + ".sv") for name in
                ("kudu_fcov_pkg", "kudu_fcov_lsu", "tb_fcov_lsu_semantics")]
    for hw in (0, 1):
        build = root / f"hw{hw}"
        build.mkdir()
        command = ["submit", "-i", "vcs", "-full64", "-sverilog", "-xlrm", "module_xmr",
                   "-timescale=1ns/1ps", "-top", "tb",
                   "-cm", "line+cond+assert", "-o", "simv"]
        if hw:
            command += ["+define+CHERIoT"]
        run(command + sources, build, "compile.log")
        for scenario in ("positive", "permissions"):
            work = build / scenario
            work.mkdir()
            run(["submit", "-i", build / "simv", "-cm", "line+cond+assert",
                 "-cm_dir", work / "run.vdb", "-cm_name", work.name] +
                (["+PERMISSIONS"] if scenario == "permissions" else []),
                work, "simulation.log")
            run(["submit", "-i", "urg", "-full64", "-dir", build / "simv.vdb",
                 work / "run.vdb", "-report", work / "report", "-format", "both",
                 "-show", "tests"], work, "urg.log")
    check(root)
    print(f"LSU semantics validation complete: {root}", flush=True)


if __name__ == "__main__":
    main()
