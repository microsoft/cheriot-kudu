"""Count coverage source declarations, not simulator-expanded bins or instances.

Inline and multiline declarations are counted alike.  auto_cps counts
coverpoints without explicit bins (including those with only options).
Unpacked bins[], transition bins and automatic bins are not expanded.
"""
import collections
import re

from check_syntax import coverage_sources


def strip_comments(text):
    return re.sub(r'"(?:\\.|[^"\\])*"|//[^\n]*|/\*.*?\*/',
                  lambda m: m.group(0) if m.group(0).startswith('"') else
                  re.sub(r"[^\n]", " ", m.group(0)), text, flags=re.S)


def mask_strings(text):
    return re.sub(r'"(?:\\.|[^"\\])*"', '""', text)


def declaration_body(text, start):
    """Return the body of a coverpoint / cross, or '' for an auto declaration."""
    parens = 0
    for i in range(start, len(text)):
        char = text[i]
        if char == "(":
            parens += 1
        elif char == ")":
            parens -= 1
        elif not parens and char == ";":
            return ""
        elif not parens and char == "{":
            depth = 1
            for j in range(i + 1, len(text)):
                if text[j] == "{":
                    depth += 1
                elif text[j] == "}":
                    depth -= 1
                    if not depth:
                        return text[i + 1:j]
            raise ValueError("unterminated coverage declaration body")
    raise ValueError("unterminated coverage declaration")


def census(sources):
    groups = collections.defaultdict(collections.Counter)
    bindings = collections.Counter()
    for source in sources:
        text = strip_comments(source)
        code = mask_strings(text)
        for cg in re.finditer(r"\bcovergroup\s+(\w+)\b(.*?)\bendgroup\b", text, re.S):
            body = mask_strings(cg.group(2))
            name = re.search(r'\boption\s*\.\s*name\s*=\s*(?:\{\s*)?"([^"]+)"',
                             cg.group(2))
            group = name.group(1).split(".")[0] if name else cg.group(1)
            row = groups[group]
            row["types"] += 1
            for cp in re.finditer(r"\bcoverpoint\b", body):
                row["cps"] += 1
                cp_body = declaration_body(body, cp.end())
                if not re.search(r"\b(?:bins|illegal_bins|ignore_bins)\b", cp_body):
                    row["auto_cps"] += 1
            row["crosses"] += len(re.findall(r"\bcross\b", body))
            for kind in re.findall(r"\b(bins|illegal_bins|ignore_bins)\s+\w+", body):
                row[kind] += 1
            # Count source new() declarations separately from type definitions.
            row["new_decls"] += len(re.findall(
                r"\b" + re.escape(cg.group(1)) + r"\s+\w+\s*=\s*new\s*\(", code))
        for bind in re.finditer(r"\bbind\s+[\w.]+\s+(\w+)\b", code):
            bindings[bind.group(1)] += 1
    return groups, bindings


def main():
    sources = []
    for path in coverage_sources():
        with open(path, encoding="utf-8") as source:
            sources.append(source.read())
    groups, bindings = census(sources)
    columns = ("types", "new_decls", "cps", "auto_cps", "crosses",
               "bins", "illegal_bins", "ignore_bins")
    print("Coverage source declarations (regular/illegal/ignore bins are separate):")
    print("%-16s %s" % ("group", " ".join("%12s" % col for col in columns)))
    total = collections.Counter()
    for group, row in groups.items():
        total.update(row)
        print("%-16s %s" % (group, " ".join("%12d" % row[col] for col in columns)))
    print("%-16s %s" % ("TOTAL", " ".join("%12d" % total[col] for col in columns)))
    print("\nBind declarations by coverage module:")
    for module, count in sorted(bindings.items()):
        print("  %-28s %d" % (module, count))
    print("  %-28s %d" % ("TOTAL", sum(bindings.values())))
    print("\nTypes and new() declarations are source counts; binds may create multiple")
    print("instances per target hierarchy/configuration, including nested coverage modules.")
    print("No elaborated instance count or expanded bin count is inferred here.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
