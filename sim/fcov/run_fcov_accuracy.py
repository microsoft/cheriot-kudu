#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Native production-monitor regression. Run from sim with VCS/LSF modules loaded.

Every invocation retains exclusive UUID output, databases, logs and URG reports.
Use --check DIRECTORY to independently recheck the retained native results.
Synthetic request/response boundaries exhaust guards; WB uses actual wt_fifo RTL.
"""

from collections import Counter
import os
from pathlib import Path
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


def bins(text, name, cross=False):
    body = section(text, "Cross" if cross else "Variable", name)
    result = {}
    for line in body.splitlines():
        fields = line.split()
        # Native covered-bin rows end in COUNT AT_LEAST TESTS NUM_TESTS;
        # uncovered rows have COUNT AT_LEAST with no test attribution.
        if not fields or not (fields[0].startswith(("auto[", "way_", "n_", "some_", "c_"))
                              or fields[0] in ("none", "few", "many", "all_",
                                              "untagged", "tagged_cap", "aligned")):
            continue
        axes = 3 if name in ("x_ls_type_1", "x_ls_type_2") else 2 if cross else 1
        if len(fields) > axes and fields[axes].isdigit():
            result[tuple(fields[:axes]) if cross else fields[0]] = int(fields[axes])
    return result


def check(root):
    names = ("x_ls_type_1", "x_ls_type_2", "x_ls_cap_1",
             "x_access_err", "x_resp_clrperm_1", "x_resp_clrperm_2")
    for hw in (0, 1):
        work = root / f"hw{hw}" / "positive"
        log = (work / "simulation.log").read_text()
        require(f"PASS FCOV accuracy HW={hw} BAD=0" in log, work)
        require(not re.search(r"(?:Error|Fatal|Warning)-|FCOV:", log), (work, log))
        text = (work / "report/grpinfo.txt").read_text()
        # Use only instance detail, not the duplicated type summaries.
        groups = {}
        for name in ("FC_MA_LSU.dcache", "FC_MA_LSU.lspl", "FC_MA_TOP"):
            marker = f"Summary for Group Instance   {name}\n"
            require(marker in text, (work, marker))
            groups[name] = text.split(marker, 1)[1].split("Summary for Group ", 1)[0]
        cache, lsu, top = (groups[n] for n in
                           ("FC_MA_LSU.dcache", "FC_MA_LSU.lspl", "FC_MA_TOP"))
        forward = bins(cache, "cp_fwd_data1")
        expected_ranges = {f"auto[{n << 26}:{((n + 1) << 26) - 1}]": 2
                           for n in range(64)}
        require(forward == expected_ranges,
                (work, "64 forwarding bins, twice each", forward))
        require(bins(cache, "cp_repl") ==
                {**{f"way_{n}": 1 for n in (1, 2, 4, 8)}, "none": 1},
                (work, "replacement", bins(cache, "cp_repl")))
        require(bins(cache, "cp_update_valid") == {"n_0": 210, "n_1": 15},
                (work, "update valid", bins(cache, "cp_update_valid")))
        require(bins(cache, "cp_update_invalid") ==
                {"n_0": 209, "n_1": 9, "n_2": 6, "n_4": 1},
                (work, "update invalid", bins(cache, "cp_update_invalid")))
        require(bins(top, "cp_tsmap_rdata") ==
                {n: 2 * hw for n in ("none", "few", "many", "all_")},
                (work, "map data", bins(top, "cp_tsmap_rdata")))
        rows = {row[0]: row[1:] for line in lsu.splitlines()
                if re.match(r"^(?:cp_|x_)\w+\s+\d", line)
                for row in [line.split()]}
        for name, goals in zip(names, (8, 28, 16, 12, 16, 512)):
            require(int(rows[name][0]) == goals, (work, name, "goals", rows[name]))
            require(rows[name][5] == str(hw), (work, name, "weight", rows[name]))
        require(rows["cp_out_is_cap"][5] == "0", (work, "helper weight"))
        require(rows["x_ls_rv32_1"][5] == "1", (work, "shared cross weight"))
        expected = {name: Counter() for name in names}
        if hw:
            for _path in range(4):
                for p in range(512):
                    b = [(p >> i) & 1 for i in range(9)]
                    saved, mode, req, cap, csr, busy, err, load, cache_ok = b
                    if saved and mode and req:
                        expected[names[0]][(f"auto[{load}]", f"auto[{cap}]",
                                             f"auto[{cache_ok}]")] += 1
                        if err:
                            expected[names[1]][(f"auto[{cap}]", f"auto[{cache_ok}]",
                                                 "c_seal")] += 1
                        if cap and not csr and not busy:
                            expected[names[2]][(f"auto[{load}]", "aligned")] += 1
            for tag in (0, 1):
                for perm in ("none", "some_1", "some_2", "some_3",
                             "some_8", "some_9", "some_a", "some_b"):
                    expected[names[4]][("tagged_cap" if tag else "untagged", perm)] = 1
                    if tag:
                        expected[names[5]][("auto[3]", perm)] = 1
            for tag in (0, 1):
                for index, cause in enumerate(("load_align", "load_fault", "store_align",
                                               "store_fault", "cheri", "illegal")):
                    expected[names[3]][(f"auto[{tag}]", cause)] = 21 + 3 * (tag + index)
        for name in names:
            actual = {key: value for key, value in bins(lsu, name, True).items() if value}
            require(actual == dict(expected[name]), (work, name, actual, expected[name]))
            require(int(rows[name][2]) == len(expected[name]),
                    (work, name, "covered goals", rows[name]))
        for bad, assertion, illegal in (
            (1, "AssertUpdateValidOneHot", "multiple"),
            (2, "AssertUpdateValidOneHot", "multiple"),
            (3, "AssertUpdateValidOneHot", "multiple"),
            (4, "AssertUpdateInvalidNotThree", "three"),
            (5, "AssertRdTagOneHot", "multi"),
            (6, "AssertWrTagAtMostTwo", "multi"),
        ):
            negative = root / f"hw{hw}" / f"bad{bad}"
            output = (negative / "simulation.log").read_text()
            require(re.search(rf"{assertion}: started at \d+ps failed at \d+ps",
                              output) and "FCOV:" in output,
                    (negative, "paired assertion missing"))
            require(re.search(rf"bin {illegal} of coverpoint", output) and
                    output.count("Illegal bin hit") == 1,
                    (negative, "illegal-bin diagnostic missing"))
            # Continue-on-error lets the paired assertion run after the illegal
            # bin; VCS returns zero for $error, so verify failures, not exit code.
            require(f"PASS FCOV accuracy HW={hw} BAD={bad}" in output,
                    (negative, "fixture did not finish"))
        print(f"PASS hw{hw}: 64 forwarding bins x2; 5 replacement bins x1; "
              "legal masks; 4 map bins; six exact cross distributions/weights; "
              "six paired illegal-bin/assertion failures", flush=True)


def run(command, directory, log, negative=False):
    print(f"{directory}: {' '.join(map(str, command))}", flush=True)
    with (directory / log).open("x") as output:
        result = subprocess.run(list(map(str, command)), cwd=directory, stdout=output,
                                stderr=subprocess.STDOUT, timeout=600)
    if negative:
        with (directory / "exit_code.txt").open("x") as output:
            output.write(str(result.returncode))
    else:
        require(result.returncode == 0, (command, directory / log, result.returncode))


def main():
    if len(sys.argv) > 1:
        require(len(sys.argv) == 3 and sys.argv[1] == "--check",
                "Usage: run_fcov_accuracy.py [--check DIRECTORY]")
        check(Path(sys.argv[2]).resolve())
        return
    sim = Path(__file__).resolve().parent.parent
    os.chdir(sim)
    root = Path("temp") / ("fcov_accuracy_" + uuid.uuid4().hex[:12])
    root.mkdir(parents=True, exist_ok=False)
    root = root.resolve()
    scratch = root / "tool_scratch"
    scratch.mkdir()
    os.environ["TMPDIR"] = str(scratch)
    print(f"Artifacts: {root}", flush=True)
    rtl = sim.parent / "rtl"
    sources = [rtl / (name + ".sv") for name in
               ("kudu_cfg_pkg", "cheri_pkg", "csr_pkg", "super_pkg", "wt_fifo")]
    sources += [sim / "fcov" / (name + ".sv") for name in
                ("kudu_fcov_pkg", "kudu_fcov_lsu", "kudu_fcov_top", "tb_fcov_accuracy")]
    for hw in (0, 1):
        build = root / f"hw{hw}"
        build.mkdir()
        command = ["submit", "-i", "vcs", "-full64", "-sverilog",
                   "-timescale=1ns/1ps", "-top", "tb",
                   "-cm", "line+cond+assert", "-o", "simv"]
        if hw:
            command += ["+define+CHERIoT"]
        run(command + sources, build, "compile.log")
        for bad in range(7):
            work = build / (f"bad{bad}" if bad else "positive")
            work.mkdir()
            run(["submit", "-i", build / "simv", f"+BAD={bad}",
                 "-cm", "line+cond+assert", "-cm_dir", work / "run.vdb",
                 "-cm_name", work.name] + (["-covg_cont_on_error"] if bad else []),
                work, "simulation.log", negative=bool(bad))
            if not bad:
                run(["submit", "-i", "urg", "-full64", "-dir", build / "simv.vdb",
                     work / "run.vdb", "-report", work / "report",
                     "-format", "both", "-show", "tests"], work, "urg.log")
    check(root)
    print(f"Native validation complete: {root}", flush=True)


if __name__ == "__main__":
    main()
