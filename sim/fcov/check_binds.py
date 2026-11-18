"""Check that every bind port connection in sim/fcov/kudu_fcov_bind.sv resolves.

Why this exists
---------------
An undeclared identifier in a module instance port connection is not an error:
the implicit-net rules turn it into a 1-bit wire.  A misspelled or
out-of-scope signal in a bind therefore produces a covergroup that samples a
constant 0 forever and still reports coverage.  `default_nettype none does not
help, because the implicit net is created in the *target* module's scope, which
has its own nettype setting.

slang only catches the subset where the width happens to disagree.  This script
checks explicit connection roots against declarations in the target modules.
This is a source-level sanity check, not a SystemVerilog scope/type resolver:
struct fields, generate scopes and preprocessor/configuration selection require
the companion check_syntax.py --matrix elaboration check.

Run from the repo root:

    python sim/fcov/check_binds.py
"""
import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
RTL = os.path.join(ROOT, "rtl")
BIND = os.path.join(os.path.dirname(os.path.abspath(__file__)), "kudu_fcov_bind.sv")

KEYWORDS = set("""
if else begin end module endmodule input output inout logic wire reg bit int
integer parameter localparam assign always always_comb always_ff always_latch
posedge negedge or and not xor case casez casex endcase default for while do
function endfunction task endtask typedef enum struct union packed signed
unsigned generate endgenerate genvar bind covergroup endgroup coverpoint bins
illegal_bins ignore_bins wildcard cross option type_option iff with return
automatic static const void this super null unique priority import export
package endpackage interface endinterface modport initial final assert assume
cover property endproperty sequence endsequence disable inside dist
""".split())

# Regexes for declarations we care about.
RE_MODULE = re.compile(r"^\s*module\s+(\w+)", re.M)
RE_ENDMODULE = re.compile(r"^\s*endmodule", re.M)
RE_DECL = re.compile(
    r"^\s*(?:input|output|inout)?\s*"
    r"(?:var\s+)?"
    r"(?:wire|logic|reg|bit|int|integer|byte|shortint|longint|"
    r"[A-Za-z_]\w*_[te])\s*"
    r"(?:signed|unsigned)?\s*"
    r"(?:\[[^;]*?\]\s*)*"
    r"([A-Za-z_]\w*(?:\s*,\s*[A-Za-z_]\w*)*)",
    re.M,
)
RE_PORT_NAME = re.compile(r"^\s*(?:input|output|inout)\b[^;,)]*?([A-Za-z_]\w*)\s*[,)]",
                          re.M)
RE_INSTANCE = re.compile(r"^\s*([A-Za-z_]\w*)\s*(?:#\s*\([^;]*?\)\s*)?([A-Za-z_]\w*)\s*\(",
                         re.M)
RE_GENVAR_FOR = re.compile(r"\bfor\s*\(\s*genvar\s+(\w+)")


def module_bodies():
    """Return {module_name: source_text} for every module in rtl/."""
    out = {}
    for path in glob.glob(os.path.join(RTL, "*.sv")):
        with open(path, encoding="utf-8", errors="replace") as f:
            src = f.read()
        src = re.sub(r"//[^\n]*", "", src)
        src = re.sub(r"/\*.*?\*/", "", src, flags=re.S)
        for m in RE_MODULE.finditer(src):
            name = m.group(1)
            end = RE_ENDMODULE.search(src, m.end())
            out[name] = src[m.start():end.end() if end else len(src)]
    return out


RE_STRUCT_BODY = re.compile(r"\btypedef\s+(?:struct|union)\b[^{;]*\{.*?\}\s*\w*\s*;",
                            re.S)


def declared_names(body):
    # Struct and union *fields* are not signals.  Scanning them as if they were
    # is how `.cycle2(cycle2)` and `.is_mult(is_mult)` slipped through: those
    # names exist only inside alupl_reg_t / flags_t, so the bind silently
    # created a 1-bit implicit wire and the coverpoints sampled a constant.
    # Enum bodies are kept, because enum members *are* visible in module scope.
    fields = RE_STRUCT_BODY.sub(
        lambda m: re.sub(r"[^\n]", " ", m.group(0)), body)

    names = set()
    for m in RE_DECL.finditer(fields):
        for n in m.group(1).split(","):
            n = n.strip()
            if n and n not in KEYWORDS:
                names.add(n)
    for m in RE_PORT_NAME.finditer(fields):
        names.add(m.group(1))
    # Parameters, genvars and typedef'd struct/enum declarations.
    for m in re.finditer(r"\b(?:parameter|localparam)\s+(?:\w+\s+)*?(\w+)\s*=", fields):
        names.add(m.group(1))
    for m in re.finditer(r"^\s*(\w+)\s+(\w+)\s*(?:,\s*\w+\s*)*;", fields, re.M):
        if m.group(1) not in KEYWORDS:
            names.add(m.group(2))
    for m in RE_GENVAR_FOR.finditer(fields):
        names.add(m.group(1))
    # Members of enums typedef'd inside the module: these are visible in the
    # module's scope and so may legitimately appear in a bind expression.
    for m in re.finditer(r"\btypedef\s+enum\b[^{;]*\{(.*?)\}", body, re.S):
        for item in m.group(1).split(","):
            item = item.split("=")[0].strip()
            if re.fullmatch(r"[A-Za-z_]\w*", item or ""):
                names.add(item)
    return names


def package_symbols():
    """Every enum member, parameter and typedef name defined in rtl/*_pkg.sv.

    A bind connection may legitimately name one of these (they are visible in
    the target module via its package imports), so they must not be reported
    as unresolved.
    """
    names = set()
    for path in glob.glob(os.path.join(RTL, "*_pkg.sv")):
        with open(path, encoding="utf-8", errors="replace") as f:
            src = f.read()
        src = re.sub(r"//[^\n]*", "", src)
        src = re.sub(r"/\*.*?\*/", "", src, flags=re.S)
        # Enum members: an identifier alone on a line inside a braced list.
        for m in re.finditer(r"^\s*([A-Za-z_]\w*)\s*(?:=[^,\n]*)?\s*,?\s*$", src, re.M):
            names.add(m.group(1))
        for m in re.finditer(r"\b(?:parameter|localparam)\s+(?:\w+\s+)*?(\w+)\s*=", src):
            names.add(m.group(1))
        for m in re.finditer(r"\}\s*(\w+)\s*;", src):
            names.add(m.group(1))
        for m in re.finditer(r"\bfunction\s+automatic\s+\w+\s+(\w+)", src):
            names.add(m.group(1))
    return names


def instances(body):
    """Return {instance_name: module_name} for instantiations in a module body."""
    out = {}
    for m in RE_INSTANCE.finditer(body):
        mod, inst = m.group(1), m.group(2)
        if mod in KEYWORDS or inst in KEYWORDS:
            continue
        out[inst] = mod
    return out


def strip_comments(text):
    return re.sub(r'"(?:\\.|[^"\\])*"|//[^\n]*|/\*.*?\*/',
                  lambda m: m.group(0) if m.group(0).startswith('"') else
                  re.sub(r"[^\n]", " ", m.group(0)), text, flags=re.S)


def parenthesized(text, start):
    """Return (contents, end) for arbitrarily nested connection expressions."""
    if text[start] != "(":
        raise ValueError("expected '('")
    depth = 0
    for token in re.finditer(r'"(?:\\.|[^"\\])*"|[()]', text[start:]):
        char = token.group(0)
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if not depth:
                end = start + token.end()
                return text[start + 1:end - 1], end
    raise ValueError("unterminated bind expression")


def parse_binds(text, insts, problems=None):
    """Yield (target_module, cov_module, [(port, expr, line)])."""
    if problems is None:
        problems = []
    text = strip_comments(text)
    for m in re.finditer(
            r"\bbind\s+([\w.]+)\s+(\w+)\s*", text):
        target, cov = m.group(1), m.group(2)
        pos = m.end()
        try:
            if text[pos:pos + 1] == "#":
                pos += 1
                while text[pos].isspace():
                    pos += 1
                _, pos = parenthesized(text, pos)
            instance = re.match(r"\s*\w+\s*\(", text[pos:])
            if not instance:
                raise ValueError("expected bind instance and port list")
            opening = pos + instance.end() - 1
            body, _ = parenthesized(text, opening)
        except (IndexError, ValueError) as error:
            problems.append("cannot parse bind to %s: %s" % (target, error))
            continue
        # A hierarchical bind target names an instance path; the last element
        # is what identifies the module whose scope the connections resolve in.
        if "." in target:
            path = target.split(".")
            mod = path[0]
            for p in path[1:]:
                mod = insts.get(mod, {}).get(p, None)
                if mod is None:
                    break
            if mod is None:
                problems.append("cannot resolve bind target path '%s'" % target)
                continue
            target = mod
        conns = []
        pos = 0
        while True:
            c = re.search(r"\.(\w+)\s*\(", body[pos:])
            if c is None:
                break
            start = pos + c.end() - 1
            ln = text[:opening + 1 + pos + c.start()].count("\n") + 1
            try:
                expr, pos = parenthesized(body, start)
            except ValueError as error:
                problems.append("cannot parse bind port %s: %s" % (c.group(1), error))
                break
            conns.append((c.group(1), expr.strip(), ln))
        yield target, cov, conns


def main():
    mods = module_bodies()
    decls = {k: declared_names(v) for k, v in mods.items()}
    insts = {k: instances(v) for k, v in mods.items()}

    with open(BIND, encoding="utf-8") as f:
        bind_text = f.read()

    problems = []
    n_conn = 0
    pkgsyms = package_symbols()
    for target, cov, conns in parse_binds(bind_text, insts, problems):
        if target not in mods:
            problems.append("bind target module '%s' not found in rtl/" % target)
            continue
        for port, expr, ln in conns:
            n_conn += 1
            # Do not mistake literal digits, strings or system functions for
            # signal roots. Keep function arguments available for checking.
            tokens = re.sub(r'"(?:\\.|[^"\\])*"', "", expr)
            tokens = re.sub(r"(?:\d[\d_]*\s*)?'[sS]?[bBoOdDhH]\s*[0-9a-fA-F_xXzZ?]+",
                            "", tokens)
            tokens = re.sub(r"'[01xXzZ]\b|\$\w+|\b[A-Za-z_]\w*::", "", tokens)
            for tok in re.finditer(
                    r"[A-Za-z_]\w*(?:\s*\[[^\]]*\])*"
                    r"(?:\s*\.\s*[A-Za-z_]\w*(?:\s*\[[^\]]*\])*)*", tokens):
                raw = re.sub(r"\[[^\]]*\]", "", tok.group(0))
                parts = [p.strip() for p in raw.split(".")]
                head = parts[0]
                if head in KEYWORDS or head in pkgsyms:
                    continue

                # Walk the path: keep descending while each element names an
                # instance in the current module.  Stop at the first element
                # that is a signal -- everything after that is a struct field
                # select, which this checker does not verify.
                cur_mod, ok, bad = target, True, None
                for depth, p in enumerate(parts):
                    scope_names = decls.get(cur_mod, set())
                    child = insts.get(cur_mod, {})
                    if p in child:
                        cur_mod = child[p]
                        continue
                    if p in scope_names:
                        break
                    ok, bad = False, (p, cur_mod)
                    break

                if not ok:
                    problems.append(
                        "%s:%d  .%s(%s): '%s' not declared in module '%s'"
                        % (os.path.basename(BIND), ln, port, expr, bad[0], bad[1]))

    for p in problems:
        print("ERROR: " + p)
    print("-" * 70)
    print("checked %d bind connections; %d unresolved" % (n_conn, len(problems)))
    print("Source-root check only; fields, indices and generate/configuration scopes")
    print("still require check_syntax.py --matrix elaboration.")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
