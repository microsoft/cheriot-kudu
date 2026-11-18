#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generate the repetitive, explicit family crosses in cg_isa_operands.

Default is a read-only freshness check; --write updates only the cross block.
Semantic eligibility remains in the SystemVerilog operand-role helpers.
"""
import argparse
from pathlib import Path

FAMILIES = ("arithmetic", "muldiv", "bitmanip", "control", "memory",
            "atomic", "system", "cheri")
FIELDS = ("tag", "reserved", "cperms", "otype", "cexp", "base", "top")
BEGIN = "    // BEGIN GENERATED FAMILY CROSSES"
END = "    // END GENERATED FAMILY CROSSES"


def generate():
    blocks = [BEGIN, "    // Regenerate with fcov/generate_isa_operand_crosses.py --write."]
    schema = {}

    def cross(family, suffix, axes, guard, excludes, tag=False, cap=False):
        name = f"x_{family}_{suffix}"
        axes = ["cp_instruction", *axes]
        if tag and "cp_cs1_tag" not in axes:
            axes.append("cp_cs1_tag")
        assert len(axes) <= 4
        schema[name] = axes
        guard = f"operand_family(instruction) == OF_{family.upper()} && ({guard})"
        if tag:
            guard += " && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)"
            excludes = [*excludes, "!capability_source_goal(cp_instruction, 0)"]
            if "cp_rs1_addr" in axes:
                excludes.append("(cp_rs1_addr == 0 && cp_cs1_tag != 0)")
        lines = [f"    {name}: cross {', '.join(axes)}", f"        iff ({guard}) {{"]
        if cap or family == "cheri":
            lines += ["      option.weight = kudu_top.CHERIoTEn ? 1 : 0;"]
        terms = [f"operand_family(cp_instruction) != OF_{family.upper()}", *excludes]
        terms = [term.replace("cp_instruction", "isa_instr_e'(cp_instruction)")
                 .replace("cp_immediate", "immediate_class_e'(cp_immediate)")
                 for term in terms]
        lines += [f"      ignore_bins unused = {name} with",
                  "        (" + " ||\n         ".join(terms) + ");", "    }"]
        blocks.append("\n".join(lines))

    source = lambda s: f"source_available(t, instruction, {s})"
    scalar = lambda s: f"{source(s)} && !capability_source(instruction, mode, {s})"
    immediate = ("!(immediate_goal(cp_instruction, 0, cp_immediate) || "
                 "(kudu_top.CHERIoTEn && immediate_goal(cp_instruction, 1, cp_immediate)))")
    for family in FAMILIES:
        blocks.append(f"    // {family.upper()}: only actual source/destination roles contribute goals.")
        for s in (0, 1):
            if family == "system" and s:
                continue
            r = s + 1
            # CHERI RS1 scalar inputs are CRRL/CRAM, which have no CS1.
            tag = family == "cheri" and s == 1
            cross(family, f"rs{r}", [f"cp_rs{r}_addr", f"cp_rs{r}_data"], scalar(s),
                  [f"!integer_register_goal(cp_instruction, {s}, cp_rs{r}_addr)",
                   f"(cp_rs{r}_addr == 0 && cp_rs{r}_data != OP_ZERO)"], tag)
            # The CS1-tag/RS2-size pair below already covers this CHERI projection.
            if not tag:
                cross(family, f"rs{r}_size", [f"cp_rs{r}_size"], scalar(s),
                      [f"!integer_source_goal(cp_instruction, {s})"])
        if family != "system":
            cross(family, "source_addresses", ["cp_rs1_addr", "cp_rs2_addr"],
                  f"{source(0)} && {source(1)}",
                  ["!source_register_goal(cp_instruction, 0, cp_rs1_addr)",
                   "!source_register_goal(cp_instruction, 1, cp_rs2_addr)"], family == "cheri")
        if family not in ("cheri", "system"):
            cross(family, "source_data", ["cp_rs1_data", "cp_rs2_data"],
                  f"{scalar(0)} && {scalar(1)}",
                  ["!integer_source_goal(cp_instruction, 0)",
                   "!integer_source_goal(cp_instruction, 1)"])
        if family not in ("muldiv", "atomic"):
            cross(family, "immediate", ["cp_immediate"], "!t.rvfi.trap || t.is_ex",
                  [immediate], family == "cheri")
            if family == "cheri":
                cross(family, "pcc_immediate", ["cp_immediate"], "!t.rvfi.trap || t.is_ex",
                      [immediate, "cp_instruction != ISA_AUIPCC"])
            for s in (0, 1):
                # No CHERI instruction has both an integer register and an immediate.
                if family in ("cheri", "system") or (s == 1 and family in ("arithmetic", "bitmanip")):
                    continue
                cross(family, f"rs{s+1}_immediate", [f"cp_rs{s+1}_data", "cp_immediate"],
                      scalar(s), [f"!integer_source_goal(cp_instruction, {s})", immediate])
        if family not in ("control", "memory", "atomic", "cheri"):
            continue
        for s in (0, 1):
            if s and family != "cheri":
                continue
            r = s + 1
            cap_guard = f"{source(s)} && capability_source(instruction, mode, {s})"
            cross(family, f"cs{r}_address", [f"cp_rs{r}_addr"], cap_guard,
                  [f"!capability_source_goal(cp_instruction, {s})",
                   f"!source_register(cp_instruction, 1, {s}, cp_rs{r}_addr)"],
                  tag=True, cap=True)
            for field in FIELDS:
                # The CS1 address cross already includes its tag.
                if not s and field != "tag":
                    cross(family, f"cs{r}_{field}", [f"cp_cs{r}_{field}"], cap_guard,
                          [f"!capability_source_goal(cp_instruction, {s})"], tag=True, cap=True)
                if field != "tag" or family not in ("control", "cheri"):
                    continue
                exclusions = [
                    f"!source_destination_goal(cp_instruction, {s}, CF_{field.upper()}, "
                    f"cp_cs{r}_{field}, cp_cd_{field})"]
                if field == "tag" and s:
                    exclusions.append(
                        "!source_destination_goal(cp_instruction, 0, CF_TAG, cp_cs1_tag, cp_cd_tag)")
                cross(family, f"cs{r}_cd_{field}", [f"cp_cs{r}_{field}", f"cp_cd_{field}"],
                      cap_guard + " && destination_available(t, instruction, mode)",
                      exclusions, tag=True, cap=True)
        if family in ("control", "cheri"):
            for field in ("tag",):
                # JAL/PCC and read-only CSPECIALRW have no source operand.
                cross(family, f"cd_no_cs1_{field}", [f"cp_cd_{field}"],
                      "destination_available(t, instruction, mode) && !source_available(t, instruction, 0)",
                      [f"!destination_field_goal(cp_instruction, CF_{field.upper()}, cp_cd_{field})",
                       "(uses_source(cp_instruction, 0) && cp_instruction != ISA_CSCRRW)"],
                      cap=True)
        if family == "cheri":
            for field in FIELDS:
                cross(family, f"cs1_cs2_{field}", [f"cp_cs1_{field}", f"cp_cs2_{field}"],
                      f"{source(0)} && capability_source(instruction, mode, 0) && "
                      f"{source(1)} && capability_source(instruction, mode, 1)",
                      ["!capability_source_goal(cp_instruction, 0)",
                       "!capability_source_goal(cp_instruction, 1)"], tag=True, cap=True)
        if family in ("memory", "atomic", "cheri"):
            for field in FIELDS:
                for axis, suffix in (("data", ""), ("size", "_size")):
                    cross(family, f"cs1_rs2_{field}{suffix}",
                          [f"cp_cs1_{field}", f"cp_rs2_{axis}"],
                          f"{source(0)} && capability_source(instruction, mode, 0) && {scalar(1)}",
                          ["!capability_source_goal(cp_instruction, 0)",
                           "!integer_source_goal(cp_instruction, 1)",
                           "capability_source(cp_instruction, 1, 1)"], tag=True, cap=True)
    blocks.append(END)
    return "\n\n".join(blocks), schema


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    path = Path(__file__).with_name("kudu_fcov_isa.sv")
    text = path.read_text()
    block, schema = generate()
    if BEGIN in text:
        start, end = text.index(BEGIN), text.index(END) + len(END)
    else:
        start = text.index("    x_instruction_rs1:")
        end = text.index("\n  endgroup", start)
    updated = text[:start] + block + text[end:]
    if args.write:
        path.write_text(updated)
    elif updated != text:
        raise SystemExit("Family cross block is stale; run with --write")
    print(f"PASS: {len(schema)} generated family crosses, at most four axes")


if __name__ == "__main__":
    main()
