#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Native standalone ISA coverage regression; requires loaded VCS/LSF modules.

From sim: source /etc/profile.d/modules.sh; source run_dii/load_module_vcs
          python3 fcov/run_isa_modes.py

All licensed tools run through submit -i. Each invocation creates an exclusive
directory under sim/temp, keeps native databases/reports/logs, and deletes nothing.
"""

import os
from pathlib import Path
import re
import subprocess
import sys
import uuid


# Independent expected bin census and the representative used by the fixture.
SHARED = {
    "rv32i_u_type": (2, "lui"), "rv32i_uj_type": (1, "jal"),
    "rv32i_sb_type": (6, "beq"), "rv32i_s_type": (3, "sb"),
    "rv32i_i_type": (22, "addi"), "rv32i_r_type": (10, "add"),
    "rv32i_csr": (6, "csrrw"), "rv32m_r_type": (8, "mul"),
    "rv32a_r_type": (11, "lr_w"), "rv32b_r_type": (20, "sh1add"),
    "rv32b_i_type": (12, "clz"), "rv32c_ciw_type": (1, "c_addi4spn"),
    "rv32c_cl_type": (1, "c_lw"), "rv32c_cs_type": (1, "c_sw"),
    "rv32c_ci_type": (7, "c_nop"), "rv32c_cb_type": (5, "c_srli"),
    "rv32c_ca_type": (4, "c_sub"), "rv32c_cj_type": (2, "c_jal"),
    "rv32c_cr_type": (5, "c_jr"), "rv32c_css_type": (1, "c_swsp"),
}
CHERI = {
    "cscrrw": (1, "hit"), "cheriot_r_type": (24, "csetbounds"),
    "cheriot_i_type": (3, "csetboundsimm"), "cheriot_s_type": (1, "csc"),
    "cheriot_u_type": (2, "auipcc"), "cheriot_ciw_type": (1, "c_incaddr4cspn"),
    "cheriot_ci_type": (2, "c_incaddr16csp"), "cheriot_cl_type": (1, "c_clc"),
    "cheriot_cs_type": (1, "c_csc"), "cheriot_css_type": (1, "c_cscsp"),
}
ALIASES = {"rv32i_u_type": "auipc", "rv32c_ciw_type": "c_addi4spn",
           "rv32c_ci_type": "c_addi16sp"}


def check(root):
    """Check persisted native URG instance reports, not source string patterns."""
    for hardware in (0, 1):
        for case in ("direct", "negative", "tap"):
            work = root / f"hw{hardware}" / case
            assert (f"PASS ISA modes CHERIoTEn={hardware} CASE={case}" in
                    (work / "simulation.log").read_text()), work
            text = (work / "report/grpinfo.txt").read_text()
            text = text.split("Summary for Group Instance   FC_ISA_INSTR\n")[1]
            rows = {row[0]: row[1:] for line in text.splitlines()
                    if re.match(r"^(?:x_|cp_)\w+\s+\d", line)
                    for row in [line.split()]}
            crosses = {name: row for name, row in rows.items() if name.startswith("x_")}
            assert len(crosses) == 30, (work, len(crosses))
            assert len(rows) - len(crosses) == 48, (work, len(rows))
            assert rows["cp_cheri_active"][0] == str(hardware + 1), work
            assert rows["cp_cheri_active"][5] == "0", work
            total = covered = 0
            for family, (bins, representative) in {**SHARED, **CHERI}.items():
                name = f"x_{family}_pmode"
                row = crosses[name]
                goals = (bins * hardware if family in CHERI else
                         bins * (hardware + 1) - int(hardware and family in ALIASES))
                assert int(row[0]) == goals, (work, name, row, goals)
                if goals:
                    assert row[5] == "1", (work, name, "weight", row)
                section = text.split(f"Summary for Cross {name}\n")[1]
                section = section.split("Summary for Cross ", 1)[0]
                actual = {(insn, int(mode)): int(count)
                          for insn, mode, count in re.findall(
                              r"^(\w+)\s+mode_(\d+)\s+(\d+)\s+\d+\s+T\d+\s+\d+",
                              section, re.M)}
                expected = {}
                if case == "direct":
                    if family in CHERI:
                        if hardware:
                            expected[(representative, 1)] = 4
                    else:
                        for mode in range(hardware + 1):
                            if not (family == "rv32c_ciw_type" and mode):
                                expected[(representative, mode)] = mode + 2
                        if family in ALIASES:
                            expected[(ALIASES[family], 0)] = 2
                elif case == "negative":
                    if not hardware and family in ALIASES:
                        expected[(ALIASES[family], 0)] = 1
                elif family in ("rv32i_r_type", "rv32a_r_type"):
                    words = ("add", "sub") if family == "rv32i_r_type" else ("amoswap",)
                    for word in words:
                        for mode in range(hardware + 1):
                            expected[(word, mode)] = mode + 1 if hardware else 3
                assert actual == expected, (work, name, actual, expected)
                assert int(row[2]) == len(expected), (work, name, row, expected)
                if family in CHERI:
                    assert rows[f"cp_{family}"][5] == str(hardware), (work, family)
                total += goals
                covered += int(row[2])
            assert total == (290 if hardware else 128), (work, total)
            print(f"PASS hw{hardware}/{case}: 30 crosses, {covered}/{total} goals; "
                  "exact per-bin counts and mode labels verified", flush=True)


def run(command, directory, log):
    print(f"{directory}: {' '.join(map(str, command))}", flush=True)
    with (directory / log).open("x") as output:
        subprocess.run(list(map(str, command)), cwd=directory, stdout=output,
                       stderr=subprocess.STDOUT, check=True)


def main():
    if len(sys.argv) > 1:
        if len(sys.argv) != 3 or sys.argv[1] != "--check":
            raise SystemExit("Usage: run_isa_modes.py [--check EXISTING_RUN_DIRECTORY]")
        check(Path(sys.argv[2]).resolve())
        return
    sim = Path(__file__).resolve().parent.parent
    os.chdir(sim)
    root = Path("temp") / ("isa_modes_" + uuid.uuid4().hex[:12])
    root.mkdir(parents=True, exist_ok=False)
    root = root.resolve()
    print(f"Artifacts: {root}", flush=True)
    rtl = sim.parent / "rtl"
    sources = [rtl / (name + ".sv") for name in
               ("kudu_cfg_pkg", "cheri_pkg", "csr_pkg", "super_pkg", "tracer_pkg")]
    sources += [sim / "fcov" / (name + ".sv") for name in
                ("kudu_fcov_pkg", "kudu_fcov_isa", "tb_fcov_isa_modes")]
    for hardware in (0, 1):
        build = root / f"hw{hardware}"
        build.mkdir()
        command = ["submit", "-i", "vcs", "-full64", "-sverilog",
                   "-timescale=1ns/1ps", "+define+RVFI", "-top", "kudu_top",
                   "-cm", "line+cond", "-o", "simv"]
        if hardware:
            command.append("+define+CHERIoT")
        run(command + sources, build, "compile.log")
        for case in ("direct", "negative", "tap"):
            work = build / case
            work.mkdir()
            run(["submit", "-i", build / "simv", f"+CASE={case}",
                 "-cm", "line+cond", "-cm_dir", work / "run.vdb",
                 "-cm_name", case], work, "simulation.log")
            run(["submit", "-i", "urg", "-full64", "-dir", build / "simv.vdb",
                 work / "run.vdb", "-report", work / "report", "-format", "both",
                 "-show", "tests"], work, "urg.log")
    check(root)
    print(f"Native validation complete: {root}", flush=True)


if __name__ == "__main__":
    main()
