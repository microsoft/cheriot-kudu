#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Focused EX semantic coverage regression; requires VCS/URG through submit -i.

From sim:
  source /etc/profile.d/modules.sh; source run_dii/load_module_vcs
  python3 fcov/run_ex_semantics.py

The run creates an exclusive sim/temp/ex_semantics_<uuid>/ directory and keeps
all logs, databases and URG reports.  --check DIRECTORY rechecks reports only.
"""

from collections import Counter
import os
from pathlib import Path
import re
import subprocess
import sys
import uuid


def require(condition, detail):
    if not condition:
        raise AssertionError(detail)


def instance(text, name):
    parts = text.split(f"Summary for Group Instance   {name}\n", 1)
    require(len(parts) == 2, f"Missing group instance {name}")
    return parts[1].split("Summary for Group", 1)[0]


def point(text, name):
    parts = text.split(f"Summary for Variable {name}\n", 1)
    require(len(parts) == 2, f"Missing coverpoint {name}")
    return parts[1].split("Summary for ", 1)[0]


def counts(text, name):
    section = point(text, name)
    return {label: int(count) for label, count in re.findall(
        r"^\s*([A-Za-z0-9_]+)\s+(\d+)\s+", section, re.M)
        if label not in ("NAME",) and int(count) != 0}


def row_map(text):
    return {row[0]: row[1:] for line in text.splitlines()
            if re.match(r"^(?:cp_|x_)\w+\s+\d", line)
            for row in [line.split()]}


def check_auipcc(report, hardware, work):
    exponents = (0, 31, 28, 28, 28, 28, 0, 7, 31, 0)
    bases = ("zero", "one", "low", "boundary_0ff", "boundary_100",
             "high", "maximum", "zero", "maximum", "zero")
    tops = ("one", "one", "low", "boundary_7f", "boundary_80",
            "high", "zero", "zero", "maximum", "one")
    expected = {name: Counter() for name in
                ("tag", "reserved", "cperms", "otype", "cexp", "base", "top")}
    for n in range(64):
        expected["tag"][f"tag_{n % 2}"] += 1
        expected["reserved"][f"value_{(n // 2) % 2}"] += 1
        expected["cperms"][f"permissions_{n:02x}"] += 1
        otype = n % 8
        otype_bin = ("unsealed" if otype == 0 else
                     f"sentry_{otype}" if otype <= 5 else f"sealed_{otype}")
        expected["otype"][otype_bin] += 1
        expected["cexp"][f"exponent_{exponents[n % 10]:02x}"] += 1
        expected["base"][bases[n % 10]] += 1
        expected["top"][tops[n % 10]] += 1
    goals = dict(tag=2, reserved=2, cperms=64, otype=8, cexp=32, base=7, top=7)
    for name in ("alu_fixture", "alu_fixture1"):
        alu = instance(report, "FC_MA_EX." + name)
        rows = row_map(alu)
        for field, bins in expected.items():
            cp = "cp_auipcc_pcc_" + field
            require(int(rows[cp][0]) == goals[field] and
                    int(rows[cp][5]) == hardware, (work, name, cp, rows[cp]))
            observed = counts(alu, cp)
            require(observed == (dict(bins) if hardware else {}),
                    (work, name, cp, observed, bins if hardware else {}))
        require(counts(alu, "cp_fwd") == {"source_0": 85, "source_1": 4},
                (work, name, counts(alu, "cp_fwd")))
    print(f"PASS hw{hardware}: both ALUs' AUIPCC field counts, gating and weights", flush=True)


def check(root):
    for hardware in (0, 1):
        work = root / f"hw{hardware}"
        log = (work / "simulation.log").read_text()
        require(f"PASS EX semantics CHERIoTEn={hardware}" in log, work)
        require(not re.search(r"(?:Error|Fatal)-|FCOV:", log), (work, log))
        report = (work / "report/grpinfo.txt").read_text()
        check_auipcc(report, hardware, work)
        mult = instance(report, "FC_MA_EX.mult")
        alu = instance(report, "FC_MA_EX.alu_fixture")
        mrows = row_map(mult)
        arows = row_map(alu)

        for name in ("cp_ex2", "cp_full", "cp_ex2_waw_match", "cp_fwd_rd_x0"):
            require(name not in arows, (work, "Removed ALU point still present", name))
        require(int(arows["cp_fwd"][0]) == 2, (work, arows["cp_fwd"]))
        require(counts(alu, "cp_fwd") == {"source_0": 85, "source_1": 4}, work)
        require(counts(alu, "cp_flush_busy") == {"hit": 2}, work)

        require(counts(alu, "cp_shift_rotate_op") ==
                {"sll": 1, "srl": 1, "sra": 1, "rol": 1, "ror": 1}, work)
        require(counts(alu, "cp_shift_rotate_amount") ==
                {"zero": 1, "one": 1, "middle": 2, "maximum": 1}, work)
        require(counts(alu, "cp_shift_operand_form") == {"rs2": 3, "imm": 2}, work)
        require(counts(alu, "cp_sra_negative_operand") == {"negative": 1}, work)
        require(int(arows["x_shift_op_amount"][2]) == 5, (work, arows["x_shift_op_amount"]))
        require(int(arows["x_shift_op_form"][2]) == 5, (work, arows["x_shift_op_form"]))

        require(counts(mult, "cp_div_op_sem") ==
                {"div": 1, "divu": 1, "rem": 1, "remu": 1}, work)
        require(counts(mult, "cp_divisor_class") ==
                {"zero": 1, "one": 1, "minus_one": 1, "other": 1}, work)
        require(counts(mult, "cp_dividend_class") ==
                {"zero": 1, "int_min": 1, "positive": 1, "negative": 1}, work)
        require(counts(mult, "cp_signed_div_overflow") ==
                {"other": 1, "int_min_div_minus_one": 1}, work)
        require(counts(mult, "cp_signed_div_signs") ==
                {"neg_pos": 1, "neg_neg": 1}, work)
        require(counts(mult, "cp_div_completion_path") ==
                {"early": 1, "full_iteration": 3}, work)
        require(counts(mult, "cp_div_complete_op") ==
                {"div": 1, "divu": 1, "rem": 1, "remu": 1}, work)
        require(counts(mult, "cp_mulh_op_sem") ==
                {"mulh": 1, "mulhsu": 1, "mulhu": 1}, work)
        require(counts(mult, "cp_mulh_operand_a_class") ==
                {"zero": 1, "one": 1, "int_min": 1}, work)
        require(counts(mult, "cp_mulh_operand_b_class") ==
                {"one": 1, "int_min": 1, "minus_one": 1}, work)

        occ_bins = 4 if hardware else 2
        for name, goals in (("cp_ex2_busy_op", occ_bins), ("cp_us_op", occ_bins),
                            ("x_ex2_busy_us_op", occ_bins * occ_bins)):
            require(int(mrows[name][0]) == goals and int(mrows[name][1]) == 0 and
                    int(mrows[name][5]) == 1, (work, name, mrows[name]))

        sb_weight = 1 if hardware else 0
        for name in ("cp_setbounds_op", "cp_setbounds_result_tag", "cp_setbounds_reason",
                     "cp_setbounds_rounding", "cp_setbounds_exp_path",
                     "cp_setbounds_exp_class", "cp_setbounds_length_class",
                     "x_setbounds_op_reason", "x_setbounds_op_rounding",
                     "x_setbounds_op_exp_path", "x_setbounds_op_length",
                     "x_setbounds_result_reason"):
            require(int(mrows[name][5]) == sb_weight, (work, name, mrows[name]))
        if hardware:
            require(counts(mult, "cp_setbounds_op") ==
                    {"setbounds": 4, "setboundsexact": 1, "setboundsimm": 1,
                     "setboundsrounddown": 1}, work)
            require(counts(mult, "cp_setbounds_result_tag") ==
                    {"cleared": 4, "valid": 3}, work)
            require(counts(mult, "cp_setbounds_reason") ==
                    {"none": 3, "exact_inexact": 1, "out_of_parent_bounds": 1,
                     "sealed_or_untagged_input": 2}, work)
            exp_path = counts(mult, "cp_setbounds_exp_path")
            require(exp_path["normal"] == 5 and exp_path["overflow_second"] == 1 and
                    exp_path["rndn_explen_gt_expb"] == 1, (work, exp_path))
            require(int(mrows["x_setbounds_op_reason"][2]) == 5, (work, mrows["x_setbounds_op_reason"]))
        else:
            require(counts(mult, "cp_setbounds_op") == {}, work)
            require(counts(mult, "cp_setbounds_reason") == {}, work)
        print(f"PASS hw{hardware}: exact EX semantic bin counts and CHERI applicability", flush=True)


def run(command, directory, log):
    print(f"{directory}: {' '.join(map(str, command))}", flush=True)
    with (directory / log).open("x") as output:
        subprocess.run(list(map(str, command)), cwd=directory, stdout=output,
                       stderr=subprocess.STDOUT, check=True, timeout=900)


def main():
    if len(sys.argv) > 1:
        if len(sys.argv) != 3 or sys.argv[1] != "--check":
            raise SystemExit("Usage: run_ex_semantics.py [--check EXISTING_RUN_DIRECTORY]")
        check(Path(sys.argv[2]).resolve())
        return
    sim = Path(__file__).resolve().parent.parent
    os.chdir(sim)
    root = Path("temp") / ("ex_semantics_" + uuid.uuid4().hex[:12])
    root.mkdir(parents=True, exist_ok=False)
    root = root.resolve()
    scratch = root / "tool_scratch"
    scratch.mkdir()
    os.environ["TMPDIR"] = str(scratch)
    print(f"Artifacts: {root}", flush=True)
    rtl = sim.parent / "rtl"
    sources = [rtl / name for name in
               ("cheri_pkg.sv", "csr_pkg.sv", "super_pkg.sv", "kudu_cfg_pkg.sv",
                )]
    sources += [sim / "fcov" / name for name in
                ("kudu_fcov_pkg.sv", "kudu_fcov_ex.sv", "tb_fcov_ex_semantics.sv")]
    for hardware in (0, 1):
        build = root / f"hw{hardware}"
        build.mkdir()
        command = ["submit", "-i", "vcs", "-full64", "-sverilog",
                   "-timescale=1ns/1ps", "-top", "kudu_top",
                   "-cm", "line+cond+assert", "-o", "simv"]
        if hardware:
            command.append("+define+CHERIoT")
        run(command + sources, build, "compile.log")
        run(["submit", "-i", build / "simv", "-cm", "line+cond+assert",
             "-cm_dir", build / "run.vdb", "-cm_name", f"hw{hardware}"],
            build, "simulation.log")
        run(["submit", "-i", "urg", "-full64", "-dir", build / "simv.vdb",
             build / "run.vdb", "-report", build / "report", "-format", "both",
             "-show", "tests"], build, "urg.log")
    check(root)
    print(f"Native EX semantic validation complete: {root}", flush=True)


if __name__ == "__main__":
    main()
