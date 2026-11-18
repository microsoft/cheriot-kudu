# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Independent architectural operand/bin oracle for the native ISA regression."""
from collections import Counter
from itertools import product
from pathlib import Path
import re

TEXT = Path(__file__).with_name("kudu_fcov_isa.sv").read_text()
ENCODINGS = TEXT[TEXT.index("    cp_rv32i_u_type:"):
                 TEXT.index("    // Cross every instruction encoding")]
RECORDS = []
for section in re.split(r"(?=    cp_\w+: coverpoint)", ENCODINGS):
    match = re.match(r"    cp_(\w+):", section)
    if match:
        for name in re.findall(r"\bbins\s+(\w+)\s*=", section):
            RECORDS.append(("cscrrw" if name == "hit" else name.rstrip("_"), match[1]))
assert len(RECORDS) == 165

C1 = set("c_addi4spn c_lw c_sw c_addi c_addi16sp c_slli c_lwsp c_srli c_srai c_andi "
         "c_beqz c_bnez c_sub c_xor c_or c_and c_jr c_jalr c_add c_swsp".split())
C2 = set("c_sw c_sub c_xor c_or c_and c_mv c_add c_swsp".split())
SYSTEM = set("fence fencei ecall ebreak mret dret wfi".split())
B_UNARY = set("zexth clz ctz cpop sextb sexth orcb rev8".split())
CH_BINARY = set("csetbounds csetboundsex csetboundsrndn cseal cunseal candperm csetaddr "
                "cincaddr csub csethigh ctestsub cseteqx".split())
CAP2 = set("cseal cunseal csub ctestsub cseteqx csc c_csc c_cscsp".split())
INT_MEMORY = set("sb sh sw jalr lb lh lw lbu lhu c_lw c_sw c_lwsp c_swsp c_jr c_jalr".split())
ALIASES = {"auipc", "c_addi4spn", "c_addi16sp"}
FIELDS = ("tag", "reserved", "cperms", "otype", "cexp", "base", "top")
DOMAINS = dict(tag=range(2), reserved=range(2), cperms=range(64), otype=range(8),
               cexp=range(32), base=range(7), top=range(7))
DEST = set("cscrrw csetbounds csetboundsex csetboundsrndn cseal cunseal candperm csetaddr "
           "cincaddr csethigh cmove ccleartag csetboundsimm cincaddrimm clc auipcc auicgp "
           "c_incaddr4cspn c_incaddr16csp c_clcsp c_clc jal jalr c_jal c_jalr".split())
TRANSFORMS = set("csetbounds csetboundsex csetboundsrndn csetboundsimm cseal cunseal candperm "
                 "csetaddr cincaddr cmove ccleartag cincaddrimm auicgp c_incaddr4cspn c_incaddr16csp".split())
BOUNDS = set("csetbounds csetboundsex csetboundsrndn csetboundsimm".split())


def cheri(family):
    return family.startswith("cheriot") or family == "cscrrw"


def category(name, encoding):
    if cheri(encoding):
        return "cheri"
    if encoding.startswith("rv32m"):
        return "muldiv"
    if encoding.startswith("rv32b"):
        return "bitmanip"
    if encoding.startswith("rv32a"):
        return "atomic"
    if name in set("jal jalr beq bne blt bge bltu bgeu c_beqz c_bnez c_jal c_j c_jr c_jalr".split()):
        return "control"
    if name in INT_MEMORY - {"jalr", "c_jr", "c_jalr"}:
        return "memory"
    if name in SYSTEM | {"c_ebreak"} or encoding == "rv32i_csr":
        return "system"
    return "arithmetic"


def sources(name, family):
    if family.startswith("rv32c"):
        return name in C1, name in C2
    if cheri(family):
        return name != "auipcc", name in CH_BINARY or name in {"csc", "c_csc", "c_cscsp"}
    if family in {"rv32i_u_type", "rv32i_uj_type"} or name in SYSTEM:
        return False, False
    if family == "rv32i_csr":
        return not name.endswith("i"), False
    two = (family in {"rv32i_sb_type", "rv32i_s_type", "rv32i_r_type", "rv32m_r_type",
                      "rv32a_r_type", "rv32b_r_type"} and name not in B_UNARY | {"lr_w"})
    return True, two


def cap_source(name, family, mode, second):
    if not mode or not sources(name, family)[second]:
        return False
    if second:
        return name in CAP2
    if cheri(family):
        return name not in {"crrl", "cram"}
    return name in INT_MEMORY or family == "rv32a_r_type"


def registers(name, mode, second):
    allowed = set(range(16 if mode else 32))
    if not second:
        if name == "cscrrw":
            return allowed - {0}
        if name == "auicgp":
            return {3}
        if name in set("c_addi4spn c_addi16sp c_lwsp c_swsp c_incaddr4cspn c_incaddr16csp c_clcsp c_cscsp".split()):
            return {2}
        if name in set("c_lw c_sw c_srli c_srai c_andi c_beqz c_bnez c_sub c_xor c_or c_and c_clc c_csc".split()):
            return set(range(8, 16))
        if name in set("c_addi c_slli c_jr c_jalr c_add".split()):
            return allowed - {0}
    else:
        if name in set("c_sw c_sub c_xor c_or c_and c_csc".split()):
            return set(range(8, 16))
        if name in {"c_mv", "c_add"}:
            return allowed - {0}
    return allowed


def immediate_goals(name, family):
    if name in {"c_addi4spn", "c_incaddr4cspn", "c_slli", "c_srli", "c_srai"}:
        return 3
    if name in {"c_lw", "c_sw", "c_lwsp", "c_swsp", "c_clc", "c_csc", "c_clcsp", "c_cscsp"}:
        return 3
    if name == "c_addi":
        return 6
    if name in {"c_li", "c_andi"}:
        return 7
    if name in {"c_addi16sp", "c_incaddr16csp", "c_lui"}:
        return 4
    if name in {"c_j", "c_jal", "c_beqz", "c_bnez"}:
        return 5
    if name in {"slli", "srli", "srai", "rori", "bclri", "bexti", "binvi", "bseti",
                "csrrwi", "csrrsi", "csrrci", "csetboundsimm"}:
        return 4
    if family in {"rv32i_u_type", "rv32i_uj_type", "rv32i_sb_type", "cheriot_u_type"}:
        return 5
    if family == "rv32i_s_type" or (
            family == "rv32i_i_type" and name not in SYSTEM) or name in {"clc", "csc", "cincaddrimm"}:
        return 7
    return 0


def permissions(code):
    result = {"GL"} if code & 32 else set()
    lower = code & 31
    if lower >= 24:
        base, bits = {"LD", "MC", "SD"}, ("LG", "LM", "SL")
    elif lower >= 20:
        base, bits = {"LD", "MC"}, ("LG", "LM")
    elif lower == 16:
        return result | {"SD", "MC"}
    elif lower >= 16:
        base, bits = set(), ("SD", "LD")
    elif lower >= 8:
        base, bits = {"EX", "MC", "LD"}, ("LG", "LM", "SR")
    else:
        base, bits = set(), ("US", "SE", "U0")
    return result | base | {bit for i, bit in enumerate(bits) if code & (1 << i)}


def destination_values(name, field):
    if field == "tag" and name in {"ccleartag", "csethigh"}:
        return (0,)
    if field == "otype":
        if name == "cunseal":
            return (0,)
        if name in {"c_jal", "c_jalr"}:
            return (4, 5)
    if field == "cexp" and name in BOUNDS:
        low = 27 if name == "csetboundsimm" else 8 if name == "csetboundsrndn" else 7
        return [0, *range(low, 32)]
    return DOMAINS[field]


def allowed_pair(name, second, field, source, dest):
    if field == "tag":
        if name == "cmove" and not second:
            return source == dest
        if name in TRANSFORMS:
            return dest <= source
    if second:
        return not (name == "cunseal" and field == "cperms" and not source & 32 and dest & 32)
    if name not in TRANSFORMS:
        return True
    if field == "reserved":
        return source == dest
    if field == "cperms":
        if name == "candperm":
            return permissions(dest) <= permissions(source)
        if name == "cunseal":
            return dest in {source, source & 31}
        return source == dest
    if field == "otype":
        return name in {"cseal", "cunseal"} or source == dest
    if field in {"cexp", "base", "top"}:
        return name in BOUNDS or source == dest
    return True


def denominators(hardware):
    goals = Counter()
    per_instruction = {}
    for name, encoding in RECORDS:
        family = category(name, encoding)
        prefix = f"x_{family}_"
        modes = [m for m in range(hardware + 1)
                 if not ((cheri(encoding) and not m) or (name in ALIASES and m))]
        counts = Counter()
        if not modes:
            per_instruction[name] = counts
            continue
        counts["x_instruction_pmode"] = len(modes)
        has = sources(name, encoding)
        caps = [bool(hardware and cap_source(name, encoding, 1, s)) for s in (0, 1)]
        regs = [set().union(*(registers(name, m, s) for m in modes)) if has[s] else set()
                for s in (0, 1)]
        integers = [set().union(*(registers(name, m, s) for m in modes
                                  if not cap_source(name, encoding, m, s))) if has[s] else set()
                    for s in (0, 1)]
        for s in (0, 1):
            r = s + 1
            factor = 2 if family == "cheri" and s and caps[0] else 1
            counts[prefix + f"rs{r}"] = factor * sum(1 if a == 0 else 7 for a in integers[s])
            if not (family == "cheri" and s):
                counts[prefix + f"rs{r}_size"] = factor * (33 if integers[s] else 0)
            if caps[s]:
                addresses = registers(name, 1, s)
                counts[prefix + f"cs{r}_address"] = 2 * len(addresses) - int(not s and 0 in addresses)
                for field in FIELDS:
                    if not s and field != "tag":
                        counts[prefix + f"cs{r}_{field}"] = 2 * len(DOMAINS[field])
                    if name in DEST and field == "tag":
                        for src in DOMAINS[field]:
                            for dst in destination_values(name, field):
                                if allowed_pair(name, s, field, src, dst):
                                    factor = (sum(allowed_pair(name, 0, "tag", t, dst)
                                                  for t in range(2)) if field == "tag" and s else
                                              1 if field == "tag" else 2)
                                    counts[prefix + f"cs{r}_cd_{field}"] += factor
        counts[prefix + "source_addresses"] = len(regs[1]) * (
            (2 * len(regs[0]) - int(0 in regs[0])) if family == "cheri" else len(regs[0]))
        counts[prefix + "source_data"] = 49 if all(integers) else 0
        imm = immediate_goals(name, encoding)
        if family == "cheri":
            counts[prefix + ("pcc_immediate" if name == "auipcc" else "immediate")] = imm * (2 if caps[0] else 1)
        else:
            counts[prefix + "immediate"] = imm
            for s in (0, 1):
                counts[prefix + f"rs{s+1}_immediate"] = 7 * imm if integers[s] else 0
        if hardware and name in DEST and (not has[0] or name == "cscrrw"):
            for field in ("tag",):
                counts[prefix + f"cd_no_cs1_{field}"] = len(destination_values(name, field))
        if all(caps):
            for field in FIELDS:
                counts[prefix + f"cs1_cs2_{field}"] = len(DOMAINS[field]) ** 2 * (
                    1 if field == "tag" else 2)
        if caps[0] and has[1] and not caps[1]:
            for field in FIELDS:
                count = len(DOMAINS[field]) * (1 if field == "tag" else 2)
                counts[prefix + f"cs1_rs2_{field}"] = count * 7
                counts[prefix + f"cs1_rs2_{field}_size"] = count * 33
        goals.update(counts)
        per_instruction[name] = counts
    return goals, per_instruction


REPRESENTATIVES = {
    "tag": (0, 1), "reserved": (0, 1), "cperms": (0, 0x15, 0x35, 63),
    "otype": tuple(range(8)), "cexp": (0, 1, 19, 31),
    "base": (0, 1, 2, 255, 256, 257, 511), "top": (0, 1, 2, 127, 128, 129, 255),
}
CAP_LAYOUT = {"tag": (64, 1), "reserved": (63, 1), "cperms": (57, 6),
              "otype": (54, 3), "cexp": (49, 5), "top": (41, 8), "base": (32, 9)}


def cap_value(field, value, tag):
    result = (tag << 64) | (0x35 << 57) | (19 << 49) | (129 << 41) | (257 << 32) | 17
    shift, width = CAP_LAYOUT[field]
    return (result & ~(((1 << width) - 1) << shift)) | (value << shift)


def pair_vectors():
    words = {}
    for name, width, base, digits in re.findall(
            r"\bbins\s+(\w+)\s*=\s*\{(16|32)'([bh])([0-9a-fA-F_?]+)\}", ENCODINGS):
        words[name.rstrip("_")] = int(digits.replace("_", "").replace("?", "0"),
                                      2 if base == "b" else 16)
    scalars = tuple(dict.fromkeys(
        (0, 1, 0xffffffff, 0x80000000, 0x7fffffff, 17, 0x80000011) +
        tuple(1 << bit for bit in range(32))))
    for name, encoding in RECORDS:
        if not cap_source(name, encoding, 1, 0) or not sources(name, encoding)[1]:
            continue
        both_caps = cap_source(name, encoding, 1, 1)
        for field in FIELDS:
            values = REPRESENTATIVES[field]
            pairs = product(values, values if both_caps else scalars)
            for a, b in pairs:
                for tag1, tag2 in product((0, 1), (0, 1) if both_caps else (0,)):
                    # The tag field itself already supplies its two tag axes.
                    if field == "tag" and (tag1 or tag2):
                        continue
                    cs1 = cap_value(field, a, tag1)
                    cs2 = cap_value(field, b, tag2) if both_caps else b
                    for mode in (0, 1):
                        yield name, words[name], mode, 0, cs1, cs2
        for kind in (1, 2, 3, 4):  # Execute trap, issue trap, interrupt, invalid.
            yield name, words[name], 1, kind, cap_value("tag", 1, 0), (
                cap_value("tag", 0, 0) if both_caps else 17)


def cap_bin(field, capability):
    shift, width = CAP_LAYOUT[field]
    value = (capability >> shift) & ((1 << width) - 1)
    if field == "tag":
        return f"tag_{value}"
    if field == "reserved":
        return f"value_{value}"
    if field == "cperms":
        return f"permissions_{value:02x}"
    if field == "otype":
        return "unsealed" if not value else f"{'sentry' if value <= 5 else 'sealed'}_{value}"
    if field == "cexp":
        return f"exponent_{value:02x}"
    midpoint = 256 if field == "base" else 128
    if value < 2:
        return ("zero", "one")[value]
    if value < midpoint - 1:
        return "low"
    if value in (midpoint - 1, midpoint):
        return f"boundary_{value:0{(width + 3) // 4}x}"
    return "maximum" if value == 2 * midpoint - 1 else "high"


def scalar_bin(value):
    named = {0: "ZERO", 1: "ONE", 0xffffffff: "MINUS_ONE",
             0x80000000: "MIN_INT", 0x7fffffff: "MAX_INT"}
    return "auto_OP_" + named.get(value, "NEGATIVE" if value & 0x80000000 else "POSITIVE")


def pair_hits(hardware):
    result = {}
    encoding_by_name = dict(RECORDS)
    for name, word, mode, kind, cs1, cs2 in pair_vectors():
        if not hardware or not mode or kind in (2, 3, 4):
            continue
        encoding = encoding_by_name[name]
        family = category(name, encoding)
        for field in FIELDS:
            axes = ("auto_ISA_" + name.upper(), cap_bin(field, cs1))
            tag = () if field == "tag" else (cap_bin("tag", cs1),)
            if cap_source(name, encoding, 1, 1):
                cross = f"x_{family}_cs1_cs2_{field}"
                key = axes + (cap_bin(field, cs2),) + tag
                result.setdefault(cross, Counter())[key] += 1
            else:
                for suffix, value in (("", scalar_bin(cs2)), ("_size", f"bits_{cs2.bit_length()}")):
                    cross = f"x_{family}_cs1_rs2_{field}{suffix}"
                    result.setdefault(cross, Counter())[axes + (value,) + tag] += 1
    return result
