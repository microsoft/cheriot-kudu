#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Focused native regression using real committer RTL and its coverage bind.

From sim:
  source /etc/profile.d/modules.sh; source run_dii/load_module_vcs
  python3 fcov/run_cmt_writes.py

All licensed tools use submit -i. Exclusive sim/temp directories preserve every
log, database and text/HTML report. --check DIRECTORY rechecks native reports.
The two hardware elaborations are never merged. Both fixed runtime modes are
checked independently, including the ignored PMODE=1 on RV32-only hardware.
"""

import os
from pathlib import Path
import re
import subprocess
import sys
import uuid


def require(condition, detail):
    if not condition:
        raise AssertionError(detail)


def point(text, name):
    section = text.split(f"Summary for Variable {name}\n", 1)
    require(len(section) == 2, f"Missing native coverpoint section: {name}")
    return section[1].split("Summary for ", 1)[0]


def hits(text, name):
    return {label: int(count) for label, count in re.findall(
        r"^\s*(gpr_[0-9a-f]+|match_|older_commits)\s+(\d+)\s+\d+\s+",
        point(text, name), re.M)}


def check(root):
    for hardware in (0, 1):
        for mode in (0, 1):
            work = root / f"hw{hardware}" / f"pmode{mode}"
            log = (work / "simulation.log").read_text()
            require(f"PASS CMT writes CHERIoTEn={hardware} PMODE={mode}" in log, work)
            require(not re.search(r"(?:Error|Fatal|Warning)-|FCOV:", log), (work, log))
            text = (work / "report/grpinfo.txt").read_text()
            text = text.split("Summary for Group Instance   FC_MA_CMT\n")[1]
            rows = {row[0]: row[1:] for line in text.splitlines()
                    if re.match(r"^cp_\w+\s+\d", line)
                    for row in [line.split()]}
            for removed in ("cp_rf_we", "cp_rf_we2", "cp_waddr0", "cp_waddr1", "cp_waddr2"):
                require(removed not in rows, (work, "obsolete coverpoint", removed))
            require("cp_we_vs_err" in rows, (work, "missing error invariant"))
            # One full address sweep plus explicitly enabled writes from the
            # match/negative scenarios. The suppressed early load adds no p2 hit.
            extras = ({3, 4, 7, 8, 11}, {3, 4, 5, 6, 10}, {1, 2, 7, 9, 12})
            for port in range(3):
                for domain, goals in (("cheri", 15), ("rv32", 31)):
                    name = f"cp_waddr{port}_{domain}"
                    row = rows[name]
                    active = bool(hardware and mode) == (domain == "cheri")
                    expected = {
                        f"gpr_{addr:02x}": ((1 + int(addr in extras[port])) * (mode + 1)
                                          + int(port == 0 and addr == 15)) if active else 0
                        for addr in range(1, goals + 1)
                    }
                    require(int(row[0]) == goals, (work, name, "goals", row))
                    require(int(row[5]) == (hardware if domain == "cheri" else 1),
                            (work, name, "weight", row))
                    require(int(row[2]) == (goals if active else 0),
                            (work, name, "covered goals", row))
                    actual = hits(text, name)
                    require(actual == expected, (work, name, actual, expected))
            for pair in ("0_eq_waddr1", "1_eq_waddr2", "0_eq_waddr2"):
                name = f"cp_waddr{pair}"
                require(int(rows[name][0]) == 1 and int(rows[name][2]) == 1,
                        (work, name, rows[name]))
                require(hits(text, name) == {"match_": mode + 1},
                        (work, name, hits(text, name)))
            require(hits(text, "cp_we_vs_err") == {"older_commits": 1},
                    (work, "older-fault invariant", hits(text, "cp_we_vs_err")))
            print(f"PASS hw{hardware}/pmode{mode}: 15 CHERI / 31 RV32 goals per "
                  "port, exact address/match counts, applicability and error invariant",
                  flush=True)


def run(command, directory, log):
    print(f"{directory}: {' '.join(map(str, command))}", flush=True)
    with (directory / log).open("x") as output:
        subprocess.run(list(map(str, command)), cwd=directory, stdout=output,
                       stderr=subprocess.STDOUT, check=True, timeout=600)


def main():
    if len(sys.argv) > 1:
        if len(sys.argv) != 3 or sys.argv[1] != "--check":
            raise SystemExit("Usage: run_cmt_writes.py [--check EXISTING_RUN_DIRECTORY]")
        check(Path(sys.argv[2]).resolve())
        return
    sim = Path(__file__).resolve().parent.parent
    os.chdir(sim)
    root = Path("temp") / ("cmt_writes_" + uuid.uuid4().hex[:12])
    root.mkdir(parents=True, exist_ok=False)
    root = root.resolve()
    scratch = root / "tool_scratch"
    scratch.mkdir()
    os.environ["TMPDIR"] = str(scratch)
    print(f"Artifacts: {root}", flush=True)
    rtl = sim.parent / "rtl"
    sources = [rtl / (name + ".sv") for name in
               ("kudu_cfg_pkg", "cheri_pkg", "csr_pkg", "super_pkg", "committer")]
    sources += [sim / "fcov" / (name + ".sv") for name in
                ("kudu_fcov_pkg", "kudu_fcov_cmt", "tb_fcov_cmt_writes")]
    for hardware in (0, 1):
        build = root / f"hw{hardware}"
        build.mkdir()
        command = ["submit", "-i", "vcs", "-full64", "-sverilog",
                   "-timescale=1ns/1ps", "-top", "kudu_top",
                   "-cm", "line+cond+assert", "-o", "simv"]
        if hardware:
            command.append("+define+CHERIoT")
        run(command + sources, build, "compile.log")
        for mode in (0, 1):
            work = build / f"pmode{mode}"
            work.mkdir()
            run(["submit", "-i", build / "simv", f"+PMODE={mode}",
                 "-cm", "line+cond+assert", "-cm_dir", work / "run.vdb",
                 "-cm_name", f"pmode{mode}"], work, "simulation.log")
            run(["submit", "-i", "urg", "-full64", "-dir", build / "simv.vdb",
                 work / "run.vdb", "-report", work / "report", "-format", "both",
                 "-show", "tests"], work, "urg.log")
    check(root)
    print(f"Native validation complete: {root}", flush=True)


if __name__ == "__main__":
    main()
