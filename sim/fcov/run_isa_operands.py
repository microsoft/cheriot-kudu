#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Native family operand regression. Load run_dii/load_module_vcs first.

Runs every licensed tool through submit -i, preserving all existing artifacts.
Use --check DIRECTORY to recheck persisted URG reports without a simulator.
"""
from collections import Counter
import argparse
import os
from pathlib import Path
import random
import re
import subprocess
import uuid

from check_isa_encoding_sets import expected
from generate_isa_operand_crosses import generate
import isa_operand_reference as ref

CASES = ("semantics", "bins", "families", "cd", "tap", "revocation", "pairs", "permissions")


def inputs(root):
    # Read names, not numeric constants: compressed CI/CL order differs.
    enum = re.search(r"typedef enum int unsigned\s*\{(.*?)\}\s*isa_instr_e;", ref.TEXT, re.S)[1]
    ids = {name[4:].lower(): i for i, name in enumerate(re.findall(r"\bISA_\w+", enum))}
    with (root / "expected.hex").open("x") as output:
        for mode in (0, 1):
            for word in range(65536):
                output.write(f"{ids.get(expected(word, mode), 0):08x}\n")
    vectors = []
    rng = random.Random(0x165)
    for section in re.split(r"(?=    cp_\w+: coverpoint)", ref.ENCODINGS):
        match = re.match(r"    cp_(\w+):", section)
        if not match:
            continue
        mode = int(ref.cheri(match[1]))
        for name, literal in re.findall(r"\bbins\s+(\w+)\s*=\s*\{(32'[bh][0-9a-fA-F_?]+)\}", section):
            name = "cscrrw" if name == "hit" else name.rstrip("_")
            base, digits = literal[3], literal[4:].replace("_", "")
            for _ in range(8):
                word = int("".join(str(rng.randrange(2)) if c == "?" else c for c in digits),
                           2 if base == "b" else 16)
                vectors.append((ids[name] << 33) | (mode << 32) | word)
    assert len(vectors) == 1056, len(vectors)
    with (root / "vectors.hex").open("x") as output:
        output.writelines(f"{word:016x}\n" for word in vectors)
    for case, vectors in (("pairs", ref.pair_vectors), ("permissions", ref.permission_vectors)):
        with (root / f"{case}.hex").open("x") as output:
            for name, word, mode, kind, cs1, cs2 in vectors():
                rs1 = min(ref.registers(name, mode, 0) - {0})
                rs2 = min(ref.registers(name, mode, 1) - {0})
                output.write(f"{word:08x} {mode:x} {kind:x} {rs1:x} {rs2:x} {cs1:017x} {cs2:017x}\n")


def instance_report(path):
    return path.read_text().split("Summary for Group Instance   FC_ISA_OPERANDS\n")[1].split(
        "Summary for Group ", 1)[0]


def cross_hits(report, name, dimensions):
    section = report.split(f"Summary for Cross {name}\n")[1].split("Summary for ", 1)[0]
    if "Covered bins" not in section:
        return {}
    section = section.split("Covered bins", 1)[1]
    result = {}
    for line in section.splitlines():
        cols = line.split()
        if len(cols) == dimensions + 2 and cols[0].startswith("auto_ISA_"):
            result[tuple(cols[:dimensions])] = int(cols[dimensions])
    return result


def points(report, name):
    section = report.split(f"Summary for Variable {name}\n")[1].split("Summary for ", 1)[0]
    return {name: int(count) for name, count in re.findall(
        r"^(\w+)[ \t]+(\d+)[ \t]+\d+[ \t]*$", section, re.M)
        if name not in {"TOTAL", "NAME"} and int(count)}


def check(root):
    schema = {"x_instruction_pmode": ["cp_instruction", "cp_pmode"], **generate()[1]}
    for hw in (0, 1):
        expected_goals, _ = ref.denominators(hw)
        assert not {n: c for n, c in expected_goals.items() if c and n not in schema}
        reports = {}
        for case in CASES:
            build = root / f"hw{hw}"
            assert f"PASS ISA operands {case} hardware={hw}" in (build / f"{case}.log").read_text()
            if case == "semantics":
                continue
            report = reports[case] = instance_report(build / f"{case}_report/grpinfo.txt")
            rows = {line.split()[0]: line.split()[1:] for line in report.splitlines()
                    if re.match(r"^(?:cp_|x_)\w+\s+\d", line)}
            assert {n for n in rows if n.startswith("x_")} == set(schema)
            assert {n for n in rows if n.startswith("cp_cd_")} == {"cp_cd_tag"}
            for name in schema:
                assert int(rows[name][0]) == expected_goals[name], (
                    hw, case, name, rows[name][0], expected_goals[name])
                actual = cross_hits(report, name, len(schema[name]))
                assert int(rows[name][2]) == len(actual), (hw, case, name, rows[name], actual)
            assert all(row[5] == "0" for n, row in rows.items() if n.startswith("cp_"))
        report = reports["families"]
        expected_pairs = ref.pair_hits(hw)
        for name, axes in schema.items():
            if "_cs1_cs2_" in name or "_cs1_rs2_" in name:
                actual = cross_hits(reports["pairs"], name, len(axes))
                wanted = expected_pairs.get(name, {})
                assert actual == wanted, (hw, name, "source pair hits",
                    "extra", list(actual.keys() - wanted.keys())[:3],
                    "missing", list(wanted.keys() - actual.keys())[:3],
                    "counts", [(k, actual[k], wanted[k]) for k in actual.keys() &
                               wanted.keys() if actual[k] != wanted[k]][:3])
        focused = ref.permission_hits(hw)
        for name, wanted in focused.items():
            actual = cross_hits(reports["permissions"], name, len(schema[name]))
            assert actual == wanted, (hw, name, "permission hits",
                "extra", list(actual.keys() - wanted.keys())[:3],
                "missing", list(wanted.keys() - actual.keys())[:3],
                "counts", [(k, actual[k], wanted[k]) for k in actual.keys() &
                           wanted.keys() if actual[k] != wanted[k]][:3])
            if "_rs2_cperms" not in name:
                assert len(actual) == expected_goals[name], (hw, name, len(actual), expected_goals[name])
        if not hw:
            assert all(not cross_hits(reports["permissions"], name, len(axes))
                       for name, axes in schema.items() if "permissions" in name or
                       name.endswith(("permission_bits", "permission_relation", "unseal_global")))
        for suffix, insn in (("pcc_immediate", "AUIPCC"), ("immediate", "CSETBOUNDSIMM"),
                             ("immediate", "CINCADDRIMM")):
            name = "x_cheri_" + suffix
            hits = {k: v for k, v in cross_hits(report, name, len(schema[name])).items()
                    if k[0] == "auto_ISA_" + insn}
            assert sum(hits.values()) == (14 if hw else 0), (hw, name, insn, hits)
            if hw and suffix == "immediate":
                assert {k[-1] for k in hits} == {"tag_0", "tag_1"}, hits
        scalar_classes = {"auto_OP_" + n for n in
                          ("ZERO", "ONE", "MINUS_ONE", "MIN_INT", "MAX_INT", "POSITIVE", "NEGATIVE")}
        integer_inputs = {("x_cheri_rs1", "CRRL"), ("x_cheri_rs1", "CRAM"),
                          ("x_cheri_rs2", "CSETBOUNDS"), ("x_cheri_rs2", "CINCADDR")}
        for name, insn in integer_inputs:
            hits = {key: count for key, count in cross_hits(report, name, len(schema[name])).items()
                    if key[0] == "auto_ISA_" + insn}
            assert {key[2] for key in hits} == (scalar_classes if hw else set()), (hw, name, insn, hits)
            if hw:
                assert set(hits.values()) == ({1} if name.endswith("rs2") else {2}), hits
                if name.endswith("rs2"):
                    assert {key[3] for key in hits} == {"tag_0", "tag_1"}, hits
        # Ordinary mnemonic address operands remain scalar only in saved mode 0.
        for family, insn in (("memory", "LB"), ("memory", "SB"), ("atomic", "LR_W"),
                             ("atomic", "SC_W"), ("control", "C_JR"), ("memory", "C_LW")):
            name = f"x_{family}_rs1"
            hits = {k: v for k, v in cross_hits(report, name, len(schema[name])).items()
                    if k[0] == "auto_ISA_" + insn}
            assert len(hits) == 7 and set(hits.values()) == {2 if hw else 4}, (hw, insn, hits)
            name = f"x_{family}_cs1_address"
            hits = {k: v for k, v in cross_hits(report, name, len(schema[name])).items()
                    if k[0] == "auto_ISA_" + insn}
            assert len(hits) == (2 if hw else 0), (hw, insn, hits)
            assert all(v == 7 for v in hits.values())
        # Every hit's sources must be real and scalar axes must not be cursors.
        encoding_by_name = dict(ref.RECORDS)
        for name, axes in schema.items():
            for key, count in cross_hits(report, name, len(axes)).items():
                insn = key[0][9:].lower()
                encoding = encoding_by_name[insn]
                roles = ref.sources(insn, encoding)
                assert name == "x_instruction_pmode" or name.startswith(f"x_{ref.category(insn, encoding)}_")
                for s in (0, 1):
                    if any(a.startswith(f"cp_rs{s+1}_") or a.startswith(f"cp_cs{s+1}_") for a in axes):
                        assert roles[s], (name, key)
                    if f"cp_rs{s+1}_data" in axes and ref.cheri(encoding):
                        assert not ref.cap_source(insn, encoding, 1, s), (name, key)
                if any(a.startswith("cp_cd_") for a in axes):
                    assert insn in ref.DEST, (name, key)
                if "cp_cs1_tag" in axes:
                    assert hw and ref.cap_source(insn, encoding, 1, 0), (name, key)
                    assert not (insn == "cscrrw"), (name, key)
        # Preserve exact retired CD tags, execute/issue trap behavior,
        # scalar results, source-free SCR results and both final revocation tags.
        cd = reports["cd"]
        expected_tag = {
            ("auto_ISA_CMOVE", "tag_1", "tag_1"): 2,
            ("auto_ISA_CCLEARTAG", "tag_1", "tag_0"): 1,
            ("auto_ISA_CSEAL", "tag_1", "tag_0"): 1,
            ("auto_ISA_CUNSEAL", "tag_1", "tag_0"): 1,
        }
        assert cross_hits(cd, "x_cheri_cs1_cd_tag", 3) == (expected_tag if hw else {})
        source_hits = cross_hits(cd, "x_cheri_cs1_address", 3)
        assert sum(v for k, v in source_hits.items() if k[0] == "auto_ISA_CMOVE") == (4 if hw else 0)
        for field in ("tag",):
            for s in (1, 2):
                name = f"x_cheri_cs{s}_cd_{field}"
                hits = cross_hits(cd, name, len(schema[name]))
                assert sum(hits.values()) == ((5 if s == 1 else 2) if hw else 0), (hw, name, hits)
            name = f"x_cheri_cd_no_cs1_{field}"
            hits = cross_hits(cd, name, 2)
            assert sum(hits.values()) == hw, (hw, name, hits)
            assert all(k[0] == "auto_ISA_CSCRRW" for k in hits)
        assert cross_hits(reports["revocation"], "x_cheri_cs1_cd_tag", 3) == ({
            ("auto_ISA_CLC", "tag_1", "tag_0"): 1,
            ("auto_ISA_CLC", "tag_1", "tag_1"): 1,
        } if hw else {})
        tap = {"auto_ISA_ADD": 1 if hw else 2, "auto_ISA_SUB": 1,
               "auto_ISA_AMOADD": 1, "auto_ISA_SC_W": 1}
        if hw:
            tap["auto_ISA_CSEAL"] = 1
        assert points(reports["tap"], "cp_instruction") == tap
        bins = {"auto_ISA_ADD": 2, "auto_ISA_CLZ": 1, "auto_ISA_ADDI": 1,
                "auto_ISA_CSRRWI": 1, "auto_ISA_C_MV": 1}
        if hw:
            bins.update(auto_ISA_CSEAL=1, auto_ISA_CRRL=1, auto_ISA_CSCRRW=1)
        assert points(reports["bins"], "cp_instruction") == bins, (hw, points(reports["bins"], "cp_instruction"))
        assert sum(cross_hits(reports["bins"], "x_arithmetic_rs1", 3).values()) == 2
        totals = Counter()
        for name, goals in expected_goals.items():
            family = next((f for f in ("arithmetic", "muldiv", "bitmanip", "control",
                                       "memory", "atomic", "system", "cheri")
                           if name.startswith("x_" + f + "_")), "mode")
            totals[family] += goals
        print(f"PASS hw{hw}: {len(schema)} crosses; {sum(expected_goals.values())} exact goals; {dict(totals)}",
              flush=True)


def run(command, cwd, log):
    with (cwd / log).open("x") as output:
        subprocess.run(list(map(str, command)), cwd=cwd, stdout=output,
                       stderr=subprocess.STDOUT, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    if args.check:
        check(args.check.resolve())
        return
    sim = Path(__file__).resolve().parent.parent
    os.chdir(sim)
    root = Path("temp") / ("isa_operands_families_" + uuid.uuid4().hex[:12])
    root.mkdir(parents=True, exist_ok=False)
    root = root.resolve()
    print(f"Artifacts: {root}", flush=True)
    inputs(root)
    rtl = sim.parent / "rtl"
    sources = [rtl / (name + ".sv") for name in
               ("cheri_pkg", "csr_pkg", "super_pkg", "kudu_cfg_pkg", "tracer_pkg")]
    sources += [sim / "fcov/kudu_fcov_pkg.sv", rtl / "compressed_decoder.sv",
                sim / "fcov/kudu_fcov_isa.sv", sim / "fcov/tb_fcov_isa_operands.sv"]
    for hw in (0, 1):
        build = root / f"hw{hw}"
        build.mkdir()
        cmd = ["submit", "-i", "vcs", "-full64", "-sverilog", "-timescale=1ns/1ps",
               "+define+RVFI", "-top", "kudu_top", "-cm", "line+cond", "-o", "simv"]
        if hw:
            cmd.append("+define+CHERIoT")
        run(cmd + sources, build, "compile.log")
        for case in CASES:
            run(["submit", "-i", "./simv", f"+CASE={case}", "-cm", "line+cond",
                 "-cm_dir", f"{case}.vdb"], build, f"{case}.log")
            if case != "semantics":
                run(["submit", "-i", "urg", "-full64", "-dir", "simv.vdb",
                     f"{case}.vdb", "-format", "text", "-report", f"{case}_report"],
                    build, f"{case}_urg.log")
    check(root)
    print(f"Native validation complete: {root}", flush=True)


if __name__ == "__main__":
    main()
