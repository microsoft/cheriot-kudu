#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Native issuer sample-isolation regression, run from sim with modules loaded.

Optionally pass --baseline PATH to a pre-consolidation kudu_fcov_issue.sv.
The reference monitor then observes the very same signals/edges, in the same
simulation; all points/crosses must agree except the relocation of three
CHERI point weights.
No old database is read or modified. --check DIRECTORY rechecks saved results.
"""

import argparse
import json
import os
from pathlib import Path
import re
import uuid

from run_frontend_temporal import bin_hit, coverpoint_section, group_text, require, run


def pair_counts(body, name):
    section = coverpoint_section(body, name)
    legal = {label: int(count) for label, count in re.findall(
        r"^\s*(pair_[0-3])\s+(\d+)\s+\d+\s+", section, re.M)}
    illegal = re.search(r"^\s*pair_2\s+(\d+)\s+Illegal\b", section, re.M)
    return legal, int(illegal[1]) if illegal else None


def check_pair2(work):
    log = (work / "simulation.log").read_text()
    require("PASS forwarding pairs" in log, work)
    require(not re.search(r"(?:Error|Fatal|Warning)-|FCOV:", log), (work, log))
    body = group_text(work / "report", "FC_MA_ISSUE")
    _, options = point_reports(work / "report", "FC_MA_ISSUE", 130)
    for r in range(1, 32):
        name = f"cp_fwd_wrsv_r{r}"
        require(pair_counts(body, name) ==
                ({"pair_0": 121, "pair_1": 1, "pair_2": 1, "pair_3": 1}, None),
                (work, name, pair_counts(body, name)))
        require(options[name][:4] == ["4", "0", "4", "100.00"],
                (work, name, "all four goals covered"))
    require(sum(bin_hit(body, "cp_ira_is0", label) for label in
                ("irb_is_ir0", "ira_is_ir0")) == 124, (work, "cycle count"))
    print(f"PASS {work}: all 31 pair_2 bins hit exactly once without errors; "
          "reset/subcycle/x0 rejected, all 124 pair goals covered", flush=True)


def point_reports(report, prefix, expected):
    text = (report / "grpinfo.txt").read_text()
    groups = re.findall(r"Summary for Group Instance   (" + prefix + r"[^\n]*)\n", text)
    require(len(groups) == (4 if prefix == "REFERENCE_MA_ISSUE" else 1), groups)
    points, options = {}, {}
    for group in groups:
        body = group_text(report, group)
        for match in re.finditer(
                r"Summary for (Variable|Cross) (\w+)\n(.*?)(?=Summary for |\Z)", body, re.S):
            kind, name, detail = match.groups()
            require(name not in points, ("duplicate point", name))
            # Keep every row: positive counts, holes, default/illegal/ignored
            # bins and transition labels. Ignore formatting, not bin content.
            detail = detail.split("\nGroup :", 1)[0]
            points[name] = " ".join(re.sub(r"[-=]{10,}", "", detail).split())
        for line in body.splitlines():
            if re.match(r"^(?:cp_|x_)\w+\s+\d", line):
                fields = line.split()
                options[fields[0]] = fields[1:]
    require(len(points) == expected, ("expected point/cross reports", expected, len(points)))
    require(len(options) == expected, ("missing point options", len(options)))
    return points, options


def check(root, only=None):
    for hardware in (0, 1):
        for load_filter in (0, 1):
            for mode in (0, 1):
                if only is not None and (hardware, load_filter, mode) != only:
                    continue
                work = root / f"hw{hardware}_lf{load_filter}" / f"pmode{mode}"
                log = (work / "simulation.log").read_text()
                require("PASS issue sampling " in log, work)
                require(not re.search(r"(?:Error|Fatal)-|FCOV:", log), (work, log))
                report = work / "report"
                body = group_text(report, "FC_MA_ISSUE")
                # 113 points + 17 crosses (fcov_bug_crosscheck.md additions).
                points, options = point_reports(report, "FC_MA_ISSUE", 130)
                for label, count in {"ready": 113, "rescued": 64, "raw_stall": 64,
                                     "same_bundle_ir0_to_ir1": 17}.items():
                    require(bin_hit(body, "cp_operand_outcome", label) == count,
                            (work, label, bin_hit(body, "cp_operand_outcome", label), count))
                require(sum(bin_hit(body, "cp_ira_is0", label) for label in
                            ("irb_is_ir0", "ira_is_ir0")) == 69, (work, "cycle count"))
                require(bin_hit(body, "cp_resolution_kind", "branch") == 64, work)
                require(bin_hit(body, "cp_resolution_kind", "jalr") == 65, work)
                active = hardware and load_filter and mode
                for label in ("clear", "temporal_stall"):
                    require(bin_hit(body, "cp_cheri_temporal_outcome", label) ==
                            (64 if active else 0), (work, label))
                require(bin_hit(body, "cp_ra_update_jalr", "actual_equals_predicted") ==
                        (1 if hardware and mode else 0), (work, "RA tracking"))
                require(bin_hit(body, "cp_fsm_trans", "t_reset_boot") == 4, work)
                require(bin_hit(body, "cp_fsm_trans", "t_dec_flush") == 4, work)
                require(bin_hit(body, "cp_fsm_trans", "t_sleep_out") == 3, work)
                for name in ("cp_cheri_slot", "cp_cheri_temporal_outcome",
                             "cp_cheri_temporal_issued"):
                    require(options[name][5] == str(hardware), (work, name, "weight"))
                require(options["x_cheri_temporal_issue"][5] ==
                        str(hardware and load_filter), (work, "cross weight"))
                if (root / "reference.sv").exists():
                    # The pre-consolidation baseline has 93 points + 7 crosses;
                    # later additions are absent from it.
                    reference, ref_options = point_reports(report, "REFERENCE_MA_ISSUE", 100)
                    require(reference.keys() <= points.keys(), (work, "point schema"))
                    for name in reference:
                        require(points[name] == reference[name],
                                (work, name, "bin report mismatch",
                                 points[name], reference[name]))
                        expected = ref_options[name][:]
                        if name in ("cp_cheri_slot", "cp_cheri_temporal_outcome",
                                    "cp_cheri_temporal_issued"):
                            expected[5] = str(hardware)
                        require(options[name] == expected, (work, name, "point options"))
                print(f"PASS {work.name} hw{hardware}/lf{load_filter}: "
                      "69 cycles, 258 operands, 129 resolutions; 130 point/cross reports"
                      + (" match baseline except CHERI point weights"
                         if (root / "reference.sv").exists() else ""),
                      flush=True)
                if load_filter:
                    check_pair2(work.with_name(work.name + "_pair2"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    if args.check:
        check(args.check.resolve())
        return
    sim = Path(__file__).resolve().parent.parent
    os.chdir(sim)
    root = Path("temp") / ("issue_sampling_" + uuid.uuid4().hex[:12])
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
                ("kudu_fcov_pkg", "kudu_fcov_if", "kudu_fcov_issue")]
    fixture = sim / "fcov/tb_fcov_frontend_temporal.sv"
    if args.baseline:
        old = args.baseline.read_text()
        require(len(re.findall(r"\bcovergroup cg_ma_issue", old)) == 4,
                "baseline must have the original four issuer covergroups")
        old = old.replace("module kudu_fcov_issue", "module kudu_fcov_issue_reference", 1)
        old = old.replace('"FC_MA_ISSUE', '"REFERENCE_MA_ISSUE')
        (root / "reference.sv").write_text(old)
        sources.append(root / "reference.sv")
        text = fixture.read_text()
        instance = re.search(r"  kudu_fcov_issue u_fcov_issue \(.*?\n  \);", text, re.S)
        require(instance, "missing production monitor instance in fixture")
        duplicate = instance[0].replace("kudu_fcov_issue u_fcov_issue",
                                       "kudu_fcov_issue_reference u_reference", 1)
        text = text[:instance.end()] + "\n" + duplicate + text[instance.end():]
        fixture = root / "fixture.sv"
        fixture.write_text(text)
    sources.append(fixture)
    for hardware in (0, 1):
        for load_filter in (0, 1):
            build = root / f"hw{hardware}_lf{load_filter}"
            build.mkdir()
            command = ["submit", "-i", "vcs", "-full64", "-sverilog", "-xlrm",
                       "uniq_prior_final", "+systemverilogext+sv", "+lint=TFIPC-L",
                       "-timescale=1ns/1ps", "-top", "kudu_top",
                       "-pvalue+kudu_top.LoadFiltEn=" + str(load_filter),
                       "-cm", "line+cond+tgl+fsm+branch+assert", "-o", "simv"]
            if hardware:
                command.append("+define+CHERIoT")
            run(command + sources, build, "compile.log")
            for mode in (0, 1):
                work = build / f"pmode{mode}"
                work.mkdir()
                run(["submit", "-i", build / "simv", f"+PMODE={mode}", "+issue_sampling",
                     "-cm", "line+cond+tgl+fsm+branch+assert",
                     "-cm_dir", work / "run.vdb", "-cm_name", f"pmode{mode}"],
                    work, "simulation.log")
                run(["submit", "-i", "urg", "-full64", "-dir", build / "simv.vdb",
                     work / "run.vdb", "-report", work / "report", "-format", "both",
                     "-show", "tests"], work, "urg.log")
                points, options = point_reports(work / "report", "FC_MA_ISSUE", 130)
                (work / "point_reports.json").write_text(
                    json.dumps({"bins": points, "options": options}, indent=2) + "\n")
                if load_filter:
                    pair_work = work.with_name(work.name + "_pair2")
                    pair_work.mkdir()
                    run(["submit", "-i", build / "simv", f"+PMODE={mode}",
                         "+forwarding_pairs",
                         "-cm", "line+cond+tgl+fsm+branch+assert",
                         "-cm_dir", pair_work / "run.vdb", "-cm_name", "pair2"],
                        pair_work, "simulation.log")
                    run(["submit", "-i", "urg", "-full64", "-dir", build / "simv.vdb",
                         pair_work / "run.vdb", "-report", pair_work / "report",
                         "-format", "both", "-show", "tests"], pair_work, "urg.log")
                check(root, only=(hardware, load_filter, mode))
    check(root)


if __name__ == "__main__":
    main()
