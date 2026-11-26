#!/usr/bin/env python3
"""Exhaustively check compressed coverage bins; optionally execute SV classifiers.

Run with --classifiers using a Python interpreter with pyslang installed to
constant-evaluate the actual package functions. No simulator or output files.
"""
import argparse
import ast
import re
from pathlib import Path
from generate_isa_operand_crosses import generate


HERE = Path(__file__).resolve().parent
ISA = (HERE / "kudu_fcov_isa.sv").read_text()
CSR = (HERE / "kudu_fcov_csr.sv").read_text()


def bits(item, high, low):
    return (item >> low) & ((1 << (high - low + 1)) - 1)


def item_filter(expression):
    expression = expression.replace(
        "{item[12], item[6:2]}", "((item[12] << 5) | item[6:2])")
    expression = re.sub(r"(\d+)'b([01]+)",
                        lambda m: str(int(m[2], 2)), expression)
    expression = re.sub(r"item\[(\d+)(?::(\d+))?\]",
                        lambda m: "bits(item,%s,%s)" % (m[1], m[2] or m[1]),
                        expression)
    expression = expression.replace("&&", " and ").replace("||", " or ")
    tree = ast.parse(" ".join(expression.split()), mode="eval")
    allowed = (ast.Expression, ast.BoolOp, ast.And, ast.Or, ast.Compare,
               ast.Eq, ast.NotEq, ast.BinOp, ast.LShift, ast.BitOr,
               ast.Call, ast.Name, ast.Load, ast.Constant)
    for node in ast.walk(tree):
        assert isinstance(node, allowed), ast.dump(node)
        if isinstance(node, ast.Name):
            assert node.id in ("item", "bits")
        if isinstance(node, ast.Call):
            assert isinstance(node.func, ast.Name) and node.func.id == "bits"
    code = compile(tree, "<bin-with>", "eval")
    return lambda item: eval(code, {"__builtins__": {}, "bits": bits}, {"item": item})


def coverage_sets():
    result = {}
    for match in re.finditer(
            r"(cp_(?:rv32c|cheriot)_\w+_type):\s*coverpoint.*?\{(.*?)\n    \}",
            ISA, re.S):
        for declaration in match[2].split(";"):
            found = re.search(r"\bbins\s+(\w+)\s*=\s*\{([^}]+)\}", declaration)
            if not found or "16'" not in found[2]:
                continue
            name, values = found[1], found[2]
            if "16'b" in values:
                pattern = re.search(r"16'b([01?]+)", values)[1]
                mask = int(pattern.replace("0", "1").replace("?", "0"), 2)
                value = int(pattern.replace("?", "0"), 2)
                members = {n for n in range(65536) if n & mask == value}
            else:
                values = [int(v, 16) for v in re.findall(r"16'h([0-9a-f]+)", values)]
                members = set(range(values[0], values[-1] + 1))
            filtered = re.search(r"\bwith\s+\((.*)\)", declaration.split("iff")[0], re.S)
            if filtered:
                predicate = item_filter(filtered[1])
                members = {n for n in members if predicate(n)}
            assert name not in result, name
            result[name] = members
    assert len(result) == 33, sorted(result)
    return result


def expected(insn, cheri):
    q, f = insn & 3, insn >> 13
    rd, rs2 = bits(insn, 11, 7), bits(insn, 6, 2)
    imm = (bits(insn, 12, 12) << 5) | rs2
    if q == 0:
        if f == 0 and bits(insn, 12, 5):
            return "c_incaddr4cspn" if cheri else "c_addi4spn"
        return {2: "c_lw", 6: "c_sw", **({3: "c_clc", 7: "c_csc"} if cheri else {})}.get(f)
    if q == 1:
        if f == 0:
            return "c_nop" if insn == 1 else ("c_addi" if rd and imm else None)
        if f == 2:
            return "c_li" if rd else None
        if f == 3 and imm and rd:
            return ("c_incaddr16csp" if cheri else "c_addi16sp") if rd == 2 else "c_lui"
        if f == 4:
            sub = bits(insn, 11, 10)
            if sub < 2:
                return ("c_srli", "c_srai")[sub] if not bits(insn, 12, 12) and rs2 else None
            if sub == 2:
                return "c_andi"
            if not bits(insn, 12, 12):
                return ("c_sub", "c_xor", "c_or", "c_and")[bits(insn, 6, 5)]
        return {1: "c_jal", 5: "c_j", 6: "c_beqz", 7: "c_bnez"}.get(f)
    if q == 2:
        if f == 0:
            return "c_slli" if not bits(insn, 12, 12) and rd and rs2 else None
        if f == 2:
            return "c_lwsp" if rd else None
        if f == 3 and cheri:
            return "c_clcsp" if rd else None
        if f == 4:
            if insn == 0x9002:
                return "c_ebreak"
            if rd:
                return ("c_add" if rs2 else "c_jalr") if insn & 0x1000 else ("c_mv" if rs2 else "c_jr")
        return {6: "c_swsp", **({7: "c_cscsp"} if cheri else {})}.get(f)
    return None


def check_operands():
    """Keep the operand identities aligned with independently reported encodings."""
    enum = re.search(r"typedef enum int unsigned\s*\{(.*?)\}\s*isa_instr_e;", ISA, re.S)[1]
    identities = re.findall(r"\bISA_\w+", enum)
    decoder = re.search(
        r"function automatic isa_instr_e instruction_id\b(.*?)endfunction", ISA, re.S)[1]
    encoding_groups = ISA[ISA.index("    cp_rv32i_u_type:"):
                          ISA.index("    // Cross every instruction encoding")]
    instructions = []
    for match in re.finditer(
            r"(?:wildcard\s+)?bins\s+(\w+)\s*=\s*\{([^}]+)\}"
            r"(?:\s+with\s+\((.*?)\))?(?:\s+iff\s+\((.*?)\))?\s*;",
            encoding_groups, re.S):
        name, values, condition, _ = match.groups()
        identity = "ISA_" + ("cscrrw" if name == "hit" else name.rstrip("_")).upper()
        instructions.append(identity)
        if "32'" in values:
            branch = re.search(
                re.escape(values) + r":(.*?)(?=\n      (?:32'|default:))",
                decoder, re.S)[1]
            assert f"return {identity};" in branch, identity
        else:
            branch = next(
                guard for guard, result in re.findall(
                    r"    if \((.*?)\)\n      return (ISA_\w+);", decoder, re.S)
                if result == identity)
            assert f"word16 inside {{{values}}}" in branch, identity
            if condition:
                predicate = " ".join(condition.replace("item", "word16").split())
                assert predicate in " ".join(branch.split()), identity
    assert len(instructions) == len(set(instructions)) == 165
    assert set(identities) == {"ISA_UNKNOWN", *instructions}
    crosses = re.findall(r"\b(x_\w+):\s*cross\s+([\w,\s]+?)(?=\s+iff\b|[;{])", ISA)
    assert all(2 <= len(axes.split(",")) <= 4 for _, axes in crosses)
    operand_crosses = [(name, axes) for name, axes in crosses if "cp_instruction" in axes]
    generated, schema = generate()
    assert generated in ISA
    operands = ISA.split("  covergroup cg_isa_operands", 1)[1].split("  endgroup", 1)[0]
    assert set(re.findall(r"\b(cp_cd_\w+):\s*coverpoint", operands)) == {"cp_cd_tag"}
    family_axes = [(name.split("_")[1], tuple(sorted(axes))) for name, axes in schema.items()]
    assert len(family_axes) == len(set(family_axes)), "redundant operand cross axes within a family"
    assert len(operand_crosses) == len(schema) + 1
    assert [(name, [axis.strip() for axis in axes.split(",")])
            for name, axes in operand_crosses if "cp_pmode" in axes] == [
                ("x_instruction_pmode", ["cp_instruction", "cp_pmode"])]
    for name, axes in operand_crosses:
        if name == "x_instruction_pmode":
            continue
        assert [axis.strip() for axis in axes.split(",")] == schema[name]
        assert len(schema[name]) == len(set(schema[name]))
    for fragment in (
            "mem_cap_t'(t.rvfi.rs1_rdata)", "mem_cap_t'(t.rvfi.rs2_rdata)",
            "mem_cap_t'(t.rvfi.rd_wdata)",
            "!t.rvfi.intr && instruction != ISA_UNKNOWN",
            "tracer.fill_cmt_info(t, tracer.is_cmt0[i], 1'b0)",
            "sample_entry(t, final_cheri_mode_q[i]);",
            "t.rvfi.rd_wdata[MemW-1] &= ~tracer.trvk_clrtag;",
            "if (!t.rvfi.valid) return;"):
        assert fragment in ISA, fragment
    print(f"PASS: 165 operand identities match encoding bins; "
          f"{len(operand_crosses)} operand crosses, mode only crossed with instruction; "
          "family schema and unique axes")


def check_encodings():
    sets = coverage_sets()
    cap = {"c_incaddr4cspn", "c_incaddr16csp", "c_clcsp", "c_clc", "c_csc", "c_cscsp"}
    aliases = {"c_addi4spn", "c_addi16sp"}
    for cheri in (False, True):
        observed = [[] for _ in range(65536)]
        for name, members in sets.items():
            if (name in cap and not cheri) or (name in aliases and cheri):
                continue
            for insn in members:
                observed[insn].append(name)
        for insn, matches in enumerate(observed):
            want = expected(insn, cheri)
            assert matches == ([] if want is None else [want]), (
                hex(insn), cheri, matches, want)
    assert re.search(r"bins\s+irq_fast\s*=\s*\{\[6'h30:6'h3e\]\};", CSR)
    assert "iff (!t.ir_dec.cheri_op.auipcc)" in ISA
    assert ISA.count("iff (!t.ir_dec.cheri_op.cincaddrimm)") == 2
    assert ISA.count("cheri_mode && has_legal_cheri_op(t.ir_dec)") == 20
    for guard in (
            "wire cheri_cov_en = kudu_top.CHERIoTEn && tracer.cheri_pmode_i;",
            "trace_cheri_mode_q[tracer.wr_ptr] <= cheri_cov_en;",
            "trace_cheri_mode_q[(tracer.wr_ptr + 1) % 64] <= cheri_cov_en;",
            "amo_cheri_mode_q <= cheri_cov_en;",
            "mode = kudu_top.CHERIoTEn && saved_cheri_mode;",
            "u_cg_isa_instr.sample(t, mode, mode);"):
        assert guard in ISA, guard
    instruction_points = re.findall(
        r"\b(cp_\w+):\s*coverpoint\s+t\.rvfi\.insn(?:\[15:0\])?", ISA)
    mode_crosses = re.findall(
        r"\b(x_\w+_pmode):\s*cross\s+(cp_\w+),\s*cp_cheri_active", ISA)
    assert len(instruction_points) == 30
    assert len(mode_crosses) == len(instruction_points)
    assert sorted(point for _, point in mode_crosses) == sorted(instruction_points)
    assert "cp_cheri_active: coverpoint cheri_active" in ISA
    assert "bins mode[] = {[0:kudu_top.CHERIoTEn]};" in ISA
    assert ISA.count("ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};") == 10
    assert "binsof(cp_rv32i_u_type.auipc)" in ISA
    assert "binsof(cp_rv32c_ci_type.c_addi16sp)" in ISA
    check_operands()
    print("PASS: 33 compressed bins, all 65,536 words in both alias modes; "
          "fast IRQ range, saved-metadata guards and 30 instruction-mode crosses")


def check_classifiers():
    import pyslang
    import isa_operand_reference as ref

    comp = pyslang.ast.Compilation()
    rtl = HERE.parent.parent / "rtl"
    for name in ("kudu_cfg_pkg", "cheri_pkg", "csr_pkg", "super_pkg", "tracer_pkg"):
        comp.addSyntaxTree(pyslang.syntax.SyntaxTree.fromFile(str(rtl / (name + ".sv"))))
    comp.addSyntaxTree(pyslang.syntax.SyntaxTree.fromFile(str(HERE / "kudu_fcov_pkg.sv")))
    cases = []
    for funct7, funct3, category in [
            (0x20, 4, "IC_BITMANIP"), (0x20, 6, "IC_BITMANIP"), (0x20, 7, "IC_BITMANIP"),
            (0x20, 0, "IC_ALU_RR"), (0x20, 5, "IC_ALU_SHIFT"),
            (0, 4, "IC_ALU_RR"), (0, 6, "IC_ALU_RR"), (0, 7, "IC_ALU_RR"),
            (0, 1, "IC_ALU_SHIFT"), (1, 0, "IC_MUL"), (1, 4, "IC_DIV")]:
        cases.append(("d.insn = 32'h%08x;" % ((funct7 << 25) | (funct3 << 12) | 0x33),
                      category))
    cases += [
        ("d.insn = 32'h00000003; d.rs_cheri = 1;", "IC_LS_INT"),
        ("d.insn = 32'h00000023; d.rs_cheri = 1;", "IC_LS_INT"),
        ("d.rs_cheri = 1; d.is_jal = 1;", "IC_JAL"),
        ("d.rs_cheri = 1; d.is_jalr = 1;", "IC_JALR"),
        ("d.is_csr = 1; d.cheri_op.cscrrw = 1;", "IC_SCR"),
        ("d.is_csr = 1;", "IC_CSR"),
        ("d.cheri_op.clc = 1;", "IC_LS_CAP"),
        ("d.cheri_op.csetaddr = 1;", "IC_CHERI_MODIFY"),
        ("d.cheri_op.cseal = 1;", "IC_CHERI_SEAL"),
        ("d.cheri_op.cgetaddr = 1;", "IC_CHERI_INSPECT"),
        ("d.errs.illegal_insn = 1; d.cheri_op.cscrrw = 1; d.is_csr = 1;", "IC_ILLEGAL"),
        ("d.errs.illegal_c_insn = 1; d.is_jal = 1;", "IC_ILLEGAL"),
    ]
    text = ["module fcov_isa_classifier_check; import super_pkg::*; import kudu_fcov_pkg::*;"]
    for index, (setup, category) in enumerate(cases):
        text += ["function automatic bit test%d();" % index,
                 "ir_dec_t d; d = '0;", setup,
                 "return fcov_instr_cat(d) == %s; endfunction" % category,
                 "localparam bit ok%d = test%d();" % (index, index)]
    groups = {
        "SC_ALU": ["IC_ALU_RI", "IC_ALU_RR", "IC_ALU_SHIFT", "IC_BITMANIP"],
        "SC_MULDIV": ["IC_MUL", "IC_DIV"], "SC_CTRL": ["IC_BRANCH", "IC_JAL", "IC_JALR"],
        "SC_MEM": ["IC_LS_INT", "IC_LS_CAP"], "SC_ATOMIC": ["IC_AMO"],
        "SC_SYSREG": ["IC_CSR", "IC_SCR", "IC_SYS"],
        "SC_CHERI": ["IC_CHERI_INSPECT", "IC_CHERI_MODIFY", "IC_CHERI_SEAL"],
        "SC_BAD": ["IC_ILLEGAL"],
    }
    for group, categories in groups.items():
        for category in categories:
            text.append("localparam bit ok_%s = fcov_instr_scat(%s) == %s;" %
                        (category, category, group))
    # Evaluate the saved-decode qualifier independently of the bound tracer.
    text.append(re.search(r"function automatic bit has_legal_cheri_op\b.*?endfunction",
                          ISA, re.S)[0])
    qualifiers = [
        ("", 0),
        ("d.rs_cheri = 1;", 0),
        ("d.cheri_op.auipcc = 1;", 1),
        ("d.cheri_op.cincaddrimm = 1;", 1),
        ("d.cheri_op.clc = 1;", 1),
        ("d.cheri_op.csc = 1; d.errs.illegal_insn = 1;", 0),
        ("d.cheri_op.cincaddrimm = 1; d.errs.illegal_c_insn = 1;", 0),
        ("d.cheri_op.cgetaddr = 1; d.errs.perm_vio = 1;", 1),
    ]
    for index, (setup, want) in enumerate(qualifiers):
        text += ["function automatic bit qualifier%d();" % index,
                 "ir_dec_t d; d = '0;", setup,
                 "return has_legal_cheri_op(d) == 1'b%d; endfunction" % want,
                 "localparam bit ok_qualifier%d = qualifier%d();" % (index, index)]
    categories = {
        "memory_capability": ("PC_MEMORY", 24), "load_capability": ("PC_LOAD", 20),
        "store_capability": ("PC_STORE", 16), "data_only": ("PC_DATA", 17),
        "execute": ("PC_EXECUTE", 8), "sealing": ("PC_SEAL", 0),
    }
    for code in range(64):
        category = ref.permission_category(code)
        symbol, representative = categories[category]
        checks = [f"fcov_cperm_category(6'd{code}) == {symbol}"]
        for mask, detailed in (
                (15, {"memory_capability", "load_capability", "store_capability", "data_only"}),
                (16, {"execute"}), (32, {"sealing"})):
            profile = code & 31 if category in detailed else representative
            checks.append(f"fcov_cperm_profile(6'd{code}, 6'd{mask}) == 5'd{profile}")
        permissions = ref.permissions(code)
        projection = sum(int(bit in permissions) << (5 - index)
                         for index, bit in enumerate(("GL", "LG", "LM", "SD", "MC", "SL")))
        checks.append(f"fcov_maskable_permissions(6'd{code}) == 6'd{projection}")
        text.append(f"localparam bit ok_permission{code} = " + " && ".join(checks) + ";")
    text.append("endmodule")
    comp.addSyntaxTree(pyslang.syntax.SyntaxTree.fromText("\n".join(text)))
    top = next(t for t in comp.getRoot().topInstances if t.name == "fcov_isa_classifier_check")
    errors = [d for d in comp.getAllDiagnostics() if d.isError()]
    assert not errors, errors
    values = [s for s in top.body if s.name.startswith("ok")]
    assert len(values) == len(cases) + 19 + len(qualifiers) + 64
    for symbol in values:
        assert str(symbol.value) == "1'b1", (symbol.name, str(symbol.value))
    print("PASS: actual SV functions, %d categories, 19 coarse mappings, "
          "%d saved-metadata qualifiers, all 64 compressed permission encodings" %
          (len(cases), len(qualifiers)))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--classifiers", action="store_true", help="also run pyslang constant evaluation")
    args = parser.parse_args()
    check_encodings()
    if args.classifiers:
        check_classifiers()
    else:
        print("Classifier execution not requested; use --classifiers with pyslang.")
