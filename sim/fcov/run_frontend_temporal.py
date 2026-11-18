#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Focused native regression for frontend temporal coverage additions.

From sim:
  source /etc/profile.d/modules.sh; source run_dii/load_module_vcs
  python3 fcov/run_frontend_temporal.py

All licensed tools use submit -i. Artifacts remain in an exclusive
sim/temp/frontend_temporal_<uuid>/ directory. --check DIRECTORY rechecks the
generated reports without rerunning VCS.
"""

from pathlib import Path
import os
import re
import subprocess
import sys
import uuid


def require(condition, detail):
    if not condition:
        raise AssertionError(detail)


def section(text, marker):
    parts = text.split(marker, 1)
    require(len(parts) == 2, f"Missing report marker: {marker}")
    return parts[1]


def coverpoint_section(text, name):
    parts = text.split(f"Summary for Variable {name}\n", 1)
    require(len(parts) == 2, f"Missing coverpoint: {name}")
    return parts[1].split("Summary for ", 1)[0]


def bin_hit(text, point, label):
    body = coverpoint_section(text, point)
    match = re.search(rf"^\s*{re.escape(label)}\s+(\d+)\s+\d+\s+", body, re.M)
    require(match, f"Missing bin {point}.{label}")
    return int(match.group(1))


def group_text(report, group_name):
    grpinfo = (report / "grpinfo.txt").read_text()
    return section(grpinfo, f"Summary for Group Instance   {group_name}\n").split(
        "Summary for Group", 1)[0]


def check(root):
    root = Path(root)
    for hardware in (0, 1):
        for mode in (0, 1):
            work = root / f"hw{hardware}" / f"pmode{mode}"
            log = (work / "simulation.log").read_text()
            require(f"PASS frontend temporal CHERIoTEn={hardware} PMODE={mode}" in log,
                    (work, "missing PASS"))
            require(not re.search(r"(?:Error|Fatal)-|FCOV:", log), (work, log))

            issue_fwd = group_text(work / "report", "FC_MA_ISSUE")
            expected_outcomes = {
                "ready": 18 if hardware else 26,
                "rescued": 2,
                "raw_stall": 1,
                "same_bundle_ir0_to_ir1": 1,
            }
            for label, count in expected_outcomes.items():
                require(bin_hit(issue_fwd, "cp_operand_outcome", label) == count,
                        (work, label, bin_hit(issue_fwd, "cp_operand_outcome", label), count))
            require(bin_hit(issue_fwd, "cp_producer", "alu0") == 1, work)
            require(bin_hit(issue_fwd, "cp_producer", "ls") == 1, work)

            issue_bp = issue_fwd
            require(bin_hit(issue_bp, "cp_resolution_kind", "branch") ==
                    (4 if hardware else 7), work)
            require(bin_hit(issue_bp, "cp_resolution_kind", "jal") == 1, work)
            require(bin_hit(issue_bp, "cp_resolution_kind", "jalr") ==
                    (1 if hardware else 4), work)
            for label in ("none_correct", "ordinary_pc_set", "alt_apply",
                          "alt_cancel_flush"):
                require(bin_hit(issue_bp, "cp_recovery", label) >= 1, (work, label))

            issue_main = group_text(work / "report", "FC_MA_ISSUE")
            require(bin_hit(issue_main, "cp_slot1_suppressed_by_mispredict0", "hit") == 1,
                    work)

            issue_ch = issue_fwd
            temporal = bin_hit(issue_ch, "cp_cheri_temporal_outcome", "temporal_stall")
            require(temporal == (4 if hardware and mode else 0), (work, temporal))

            if_text = group_text(work / "report", "FC_MA_IF")
            require(bin_hit(if_text, "cp_pdt_cand0", "branch") == 1, work)
            require(bin_hit(if_text, "cp_pdt_cand1", "jal") == 1, work)
            require(bin_hit(if_text, "cp_pdt_src", "auto_PDT_BR0") == 1, work)
            require(bin_hit(if_text, "cp_pdt_src", "auto_PDT_JALR0") == 1, work)
            print(f"PASS hw{hardware}/pmode{mode}: forwarding, prediction/recovery, "
                  "slot1 suppression, contention and CHERI applicability checked",
                  flush=True)


def run(command, directory, log):
    print(f"{directory}: {' '.join(map(str, command))}", flush=True)
    with (directory / log).open("x") as output:
        subprocess.run(list(map(str, command)), cwd=directory, stdout=output,
                       stderr=subprocess.STDOUT, check=True, timeout=600)


def main():
    if len(sys.argv) > 1:
        if len(sys.argv) != 3 or sys.argv[1] != "--check":
            raise SystemExit("Usage: run_frontend_temporal.py [--check EXISTING_RUN_DIRECTORY]")
        check(Path(sys.argv[2]).resolve())
        return

    sim = Path(__file__).resolve().parent.parent
    os.chdir(sim)
    root = Path("temp") / ("frontend_temporal_" + uuid.uuid4().hex[:12])
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
                ("kudu_fcov_pkg", "kudu_fcov_if", "kudu_fcov_issue",
                 "tb_fcov_frontend_temporal")]

    for hardware in (0, 1):
        build = root / f"hw{hardware}"
        build.mkdir()
        command = ["submit", "-i", "vcs", "-full64", "-sverilog", "-xlrm",
                   "uniq_prior_final", "+systemverilogext+sv", "+lint=TFIPC-L",
                   "-timescale=1ns/1ps", "-top", "kudu_top",
                   "-cm", "line+cond+tgl+fsm+branch+assert", "-o", "simv"]
        if hardware:
            command.append("+define+CHERIoT")
        run(command + sources, build, "compile.log")
        for mode in (0, 1):
            work = build / f"pmode{mode}"
            work.mkdir()
            run(["submit", "-i", build / "simv", f"+PMODE={mode}",
                 "-cm", "line+cond+tgl+fsm+branch+assert",
                 "-cm_dir", work / "run.vdb", "-cm_name", f"pmode{mode}"],
                work, "simulation.log")
            run(["submit", "-i", "urg", "-full64", "-dir", build / "simv.vdb",
                 work / "run.vdb", "-report", work / "report", "-format", "both",
                 "-show", "tests"], work, "urg.log")
    check(root)
    print(f"Native validation complete: {root}", flush=True)


if __name__ == "__main__":
    main()
