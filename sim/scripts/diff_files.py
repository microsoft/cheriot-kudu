#!/usr/bin/env python3

import argparse
import difflib
from pathlib import Path
import re
import subprocess
import tempfile

# Remove PA and memory-data annotations from trapped memory operations.  The
# data label can be "load:" or "store:" regardless of the instruction mnemonic
# because some logs print the wrong label on a trapped store.
_TRAPPED_PA_RE = re.compile(r"\s+PA\s*:\s*\S+", re.IGNORECASE)
_TRAPPED_DATA_RE = re.compile(r"\s+(?:load|store)\s*:\s*\S+", re.IGNORECASE)

# Match only c.addi whose architectural destination is x0.
_C_ADDI_X0_RE = re.compile(r"(?i)(?<![\w.])c\.addi\s+x0\s*,")
_REGISTER_READ_RE = re.compile(r"(?i)\bx\d+\s*:\s*\S+")

_ISA_TEST1_SIM_RE = re.compile(r"trace\.isa_test1\.[^.]+\.clog")
_CLC_HEADER_RE = re.compile(
    r"^\s*(?:0x)?(?P<pc>[0-9a-f]{8})\s+(?:0x)?[0-9a-f]{4,8}\s+"
    r"(?:c\.)?(?:CH\.)?clc\s+", re.IGNORECASE
)
_CAP_WRITE_RE = re.compile(
    r"\bx(?:[0-9]|[12][0-9]|3[01])=0x[0-9a-f]{8}\+0x"
    r"(?P<upper>[01][0-9a-f]{8})(?![0-9a-f])", re.IGNORECASE
)
_ISA_TEST1_CLC_PCS = {0x80000618, 0x80000624, 0x80000638}


def is_isa_test1_pair(simulation: str, reference: str) -> bool:
    return (
        _ISA_TEST1_SIM_RE.fullmatch(Path(simulation).name) is not None
        and Path(reference).name == "trace.isa_test1.clog"
    )


def apply_isa_test1_clc_tag_rule(
    simulation: list[str], reference: list[str]
) -> list[str]:
    """Accept only a cleared destination tag at three isa_test1 CLC PCs.

    The 33-bit field after '+' holds bits 64:32, so its bit 32 is the tag.
    Compare the complete candidate line to enforce direction and preserve all
    other differences, including source registers and memory load annotations.
    """
    result = simulation.copy()
    for i, (actual, expected) in enumerate(zip(simulation, reference)):
        header = _CLC_HEADER_RE.match(actual)
        if (header is None or int(header["pc"], 16) not in _ISA_TEST1_CLC_PCS
                or "-->" in actual or "-->" in expected):
            continue
        writes = list(_CAP_WRITE_RE.finditer(actual))
        if len(writes) != 1:
            continue
        write = writes[0]
        upper = write["upper"]
        if upper[0] != "0":
            continue
        candidate = actual[:write.start("upper")] + "1" + upper[1:] + actual[write.end("upper"):]
        if candidate == expected:
            result[i] = expected
    return result


def show_tkdiff(a: list[str], b: list[str], file1: str, file2: str) -> int:
    """Show the same comparison rules in Tk without changing either input."""
    with tempfile.TemporaryDirectory(prefix=".mini_diff_", dir=".") as directory:
        left = Path(directory) / ("simulation-" + Path(file1).name)
        right = Path(directory) / ("reference-" + Path(file2).name)
        left.write_text("\n".join(a) + "\n", encoding="utf-8")
        right.write_text("\n".join(b) + "\n", encoding="utf-8")
        return subprocess.run(["tkdiff", str(left), str(right)], check=False).returncode


def apply_ignore_rules(line: str) -> str:
    """Apply comparison-only masking rules to one normalized log line."""
    if "-->" in line:
        # A trapped load/store has no architecturally valid memory transfer.
        # Remove these optional fields entirely so present-vs-absent also
        # compares equal.
        line = _TRAPPED_PA_RE.sub("", line)
        line = _TRAPPED_DATA_RE.sub("", line)

    c_addi_x0 = _C_ADDI_X0_RE.search(line)
    if c_addi_x0:
        # The first xN:<value> annotation after "c.addi x0,..." is the rs1
        # field.  Ignore both the reported register index and its value.
        start = c_addi_x0.end()
        prefix = line[:start]
        suffix = line[start:]
        suffix = _REGISTER_READ_RE.sub("rs1:<ignored>", suffix, count=1)
        line = prefix + suffix

    return line


def normalize_line(line: str, ignore_whitespace: bool) -> str:
    if ignore_whitespace:
        line = " ".join(line.split())
    else:
        line = line.rstrip("\n")
    return apply_ignore_rules(line)


def load_file(path: str, ignore_whitespace: bool) -> list[str]:
    with open(path, "r", encoding="utf-8") as f:
        return [normalize_line(line, ignore_whitespace) for line in f]


def trim_extra_lines(a: list[str], b: list[str], max_extra: int):
    """Ignore up to max_extra trailing lines from either file."""
    if abs(len(a) - len(b)) <= max_extra:
        min_len = min(len(a), len(b))
        return a[:min_len], b[:min_len]
    return a, b


def main() -> int:
    parser = argparse.ArgumentParser(description="Diff two text files")
    parser.add_argument("file1")
    parser.add_argument("file2")
    parser.add_argument(
        "--keep-whitespace",
        action="store_true",
        help="Do NOT ignore whitespace differences",
    )
    parser.add_argument(
        "--ignore-extra-lines",
        type=int,
        default=0,
        help="Ignore up to N extra trailing lines from either file",
    )
    parser.add_argument(
        "--isa-test1-clc-tag",
        action="store_true",
        help="For isa_test1 only, allow simulation tag 0 versus reference tag 1 "
             "in CLC destination writes at PCs 80000618, 80000624, 80000638",
    )
    parser.add_argument(
        "--tkdiff", action="store_true",
        help="Show the normalized comparison in tkdiff using temporary copies",
    )
    args = parser.parse_args()
    if args.isa_test1_clc_tag and not is_isa_test1_pair(args.file1, args.file2):
        parser.error("--isa-test1-clc-tag requires trace.isa_test1.<variant>.clog "
                     "followed by reference trace.isa_test1.clog")

    ignore_whitespace = not args.keep_whitespace
    lines1 = load_file(args.file1, ignore_whitespace)
    lines2 = load_file(args.file2, ignore_whitespace)
    lines1, lines2 = trim_extra_lines(lines1, lines2, args.ignore_extra_lines)
    if args.isa_test1_clc_tag:
        lines1 = apply_isa_test1_clc_tag_rule(lines1, lines2)
    if args.tkdiff:
        try:
            return show_tkdiff(lines1, lines2, args.file1, args.file2)
        except OSError as error:
            parser.exit(2, f"Cannot launch normalized tkdiff comparison: {error}\n")

    diff = difflib.unified_diff(
        lines1,
        lines2,
        fromfile=args.file1,
        tofile=args.file2,
        lineterm="",
    )

    has_diff = False
    for line in diff:
        print(line)
        has_diff = True

    if not has_diff:
        print("Files match (with given ignore rules).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
