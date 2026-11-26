#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generate the repetitive, explicit family crosses in cg_isa_operands.

Default is a read-only freshness check; --write updates only the generated block.
Semantic eligibility remains in the SystemVerilog operand-role helpers.
"""
import argparse
from pathlib import Path

FAMILIES = ("arithmetic", "muldiv", "bitmanip", "control", "memory",
            "atomic", "system", "cheri")
FIELDS = ("tag", "reserved", "cperms", "otype", "cexp", "base", "top")
PERMISSION_BITS = ("global", "load_global", "store", "load_mutable", "store_local",
                   "load", "capability", "system_register", "execute", "unseal",
                   "seal", "user0")
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
                  "        (" + " ||\n         ".join(terms) + ");"]
        # Architectural invariants, paired with AssertIsaTaggedCapEncoding and
        # AssertIsaJumpLinkTagged: no tagged capability has the reserved bit
        # set or CEXP 1..6 (exponent above 24), and a jump always links a
        # tagged PCC-derived capability.
        if "cp_cs1_tag" in axes and "cp_cs1_reserved" in axes:
            lines += ["      illegal_bins tagged_reserved = binsof(cp_cs1_reserved) intersect {1} &&",
                      "                                     binsof(cp_cs1_tag) intersect {1};"]
        if "cp_cs1_tag" in axes and "cp_cs1_cexp" in axes:
            lines += ["      illegal_bins tagged_above_max = binsof(cp_cs1_cexp) intersect {[1:6]} &&",
                      "                                      binsof(cp_cs1_tag) intersect {1};"]
        if family == "control" and "cp_cd_tag" in axes:
            lines += ["      illegal_bins untagged_link = binsof(cp_cd_tag) intersect {0};"]
        lines += ["    }"]
        blocks.append("\n".join(lines))

    source = lambda s: f"source_available(t, instruction, {s})"
    scalar = lambda s: f"{source(s)} && !capability_source(instruction, mode, {s})"
    cap1 = f"{source(0)} && capability_source(instruction, mode, 0)"
    cap2 = f"{source(1)} && capability_source(instruction, mode, 1)"

    def point(name, expression, guard, bins):
        blocks.append("\n".join([
            f"    {name}: coverpoint {expression}", f"        iff ({guard}) {{",
            "      option.weight = 0;", *("      " + line for line in bins), "    }"]))

    for name, mask, detail in (
            ("access", "001111", {"memory_capability", "load_capability", "data_only"}),
            ("target", "010000", {"execute"}),
            ("sealing", "100000", {"sealing"})):
        second = name == "sealing"
        r = 2 if second else 1
        bins = []
        for category, low, high in (
                ("memory_capability", 24, 31), ("load_capability", 20, 23),
                ("store_capability", 16, 16), ("data_only", 17, 19),
                ("execute", 8, 15), ("sealing", 0, 7)):
            array = category in detail and low != high
            values = f"[{low}:{high}]" if array else str(low)
            bins.append(f"bins {category}{'[]' if array else ''} = {{{values}}};")
        point(f"cp_cs{r}_{name}_permissions",
              f"fcov_cperm_profile(cs{r}.cperms, 6'b{mask})", cap2 if second else cap1, bins)

    for name, expression, guard, states in (
            ("cp_cs1_permission_bits", "expand_perms(cs1.cperms)",
             f"{cap1} && instruction == ISA_CGETPERM", ((0,), (1,))),
            ("cp_cs1_mask_permissions",
             "{expand_perms(cs1.cperms), t.rvfi.rs2_rdata[PERMS_W-1:0]}",
             f"{cap1} && {scalar(1)} && instruction == ISA_CANDPERM",
             ((0, 0), (0, 1), (1, 0), (1, 1)))):
        bins = []
        for bit, permission in enumerate(PERMISSION_BITS):
            for state in states:
                pattern = ["?"] * (12 * len(state))
                for axis, value in enumerate(state):
                    pattern[(axis + 1) * 12 - bit - 1] = str(value)
                bins.append(f"wildcard bins {permission}_{''.join(map(str, state))} = "
                            f"{{{len(pattern)}'b{''.join(pattern)}}};")
        point(name, expression, guard, bins)
    point("cp_permission_relation",
          "fcov_permission_relation(expand_perms(cs1.cperms), expand_perms(cs2.cperms))",
          f"{cap1} && {cap2} && instruction inside {{ISA_CTESTSUB, ISA_CSETEQX}}",
          ["bins equal = {PR_EQUAL};", "bins cs2_subset = {PR_CS2_SUBSET};",
           "bins cs1_subset = {PR_CS1_SUBSET};", "bins incomparable = {PR_INCOMPARABLE};"])
    point("cp_store_permissions", "fcov_store_permissions(cs1.cperms, cs2.cperms)",
          f"{cap1} && {cap2} && instruction inside {{ISA_CSC, ISA_C_CSC, ISA_C_CSCSP}}",
          ["bins no_store_or_capability[] = {0, 1};",
           "bins capability_no_store[] = {4, 5};", "bins data_store_only[] = {8, 9};",
           "bins capability_store[] = {12, 13};", "bins store_local[] = {14, 15};"])
    point("cp_unseal_global", "{cs1.cperms[5], cs2.cperms[5]}",
          f"{cap1} && {cap2} && instruction == ISA_CUNSEAL", ["bins global_pair[] = {[0:3]};"])
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
    access = ("ISA_LB, ISA_LH, ISA_LW, ISA_LBU, ISA_LHU, ISA_SB, ISA_SH, ISA_SW, "
              "ISA_C_LW, ISA_C_SW, ISA_C_LWSP, ISA_C_SWSP, ISA_LR_W, ISA_SC_W, "
              "ISA_AMOSWAP, ISA_AMOADD, ISA_AMOXOR, ISA_AMOAND, ISA_AMOOR, "
              "ISA_AMOMIN, ISA_AMOMAX, ISA_AMOMINU, ISA_AMOMAXU, "
              "ISA_CLC, ISA_CSC, ISA_C_CLC, ISA_C_CLCSP, ISA_C_CSC, ISA_C_CSCSP")
    for family in ("memory", "atomic", "cheri"):
        cross(family, "access_permissions", ["cp_cs1_access_permissions"],
              f"{cap1} && instruction inside {{{access}}}",
              [f"!(cp_instruction inside {{{access}}})"], tag=True, cap=True)
    for family, suffix, axes, instructions, guard in (
            ("control", "target_permissions", ["cp_cs1_target_permissions"],
             "ISA_JALR, ISA_C_JR, ISA_C_JALR", cap1),
            ("cheri", "sealing_permissions", ["cp_cs2_sealing_permissions", "cp_cs2_tag"],
             "ISA_CSEAL, ISA_CUNSEAL", f"{cap1} && {cap2}"),
            ("cheri", "permission_bits", ["cp_cs1_permission_bits"],
             "ISA_CGETPERM", cap1),
            ("cheri", "mask_permissions", ["cp_cs1_mask_permissions"],
             "ISA_CANDPERM", f"{cap1} && {scalar(1)}"),
            ("cheri", "permission_relation", ["cp_permission_relation", "cp_cs2_tag"],
             "ISA_CTESTSUB, ISA_CSETEQX", f"{cap1} && {cap2}"),
            ("cheri", "store_permissions", ["cp_store_permissions", "cp_cs2_tag"],
             "ISA_CSC, ISA_C_CSC, ISA_C_CSCSP", f"{cap1} && {cap2}"),
            ("cheri", "unseal_global", ["cp_unseal_global", "cp_cs2_tag"],
             "ISA_CUNSEAL", f"{cap1} && {cap2}")):
        cross(family, suffix, axes, f"{guard} && instruction inside {{{instructions}}}",
              [f"!(cp_instruction inside {{{instructions}}})"], tag=True, cap=True)
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
