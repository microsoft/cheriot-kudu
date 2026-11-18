#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Focused LSU functional-coverage semantics regression."""

from pathlib import Path
import os
import re
import subprocess
import sys
import uuid


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
            ("cp_resp_early_cheri_cause", 7),
            ("cp_resp_cap_top_path", 8),
            ("cp_resp_cap_perm_effect", 13),
            ("cp_resp_cap_tag_outcome", 3),
        ):
            fields = row(lsu, name)
            require(int(fields[1]) == goals and fields[6] == expect_weight,
                    (work, name, fields))
        require(row(lsu, "x_split_err_phase")[1] == "8", (work, row(lsu, "x_split_err_phase")))
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
        work = build / "positive"
        work.mkdir()
        run(["submit", "-i", build / "simv", "-cm", "line+cond+assert",
             "-cm_dir", work / "run.vdb", "-cm_name", work.name],
            work, "simulation.log")
        run(["submit", "-i", "urg", "-full64", "-dir", build / "simv.vdb",
             work / "run.vdb", "-report", work / "report", "-format", "both",
             "-show", "tests"], work, "urg.log")
    check(root)
    print(f"LSU semantics validation complete: {root}", flush=True)


if __name__ == "__main__":
    main()
