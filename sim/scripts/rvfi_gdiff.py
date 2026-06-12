#!/usr/bin/env python3

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Optional


# Ignore complete rs1 / rs2 lines.
# Example:
# rs1       : x00  rdata=0x0000000000000000
# rs2       : x00  rdata=0x0000000000000000
IGNORE_FIELD_RE = re.compile(r"^\s*(pc_wdata|order|rs1|rs2)\s*:")
HEX16_RE = re.compile(r"0x([0-9a-fA-F]{16})")


def shorten_16_digit_hex(match):
    hex_digits = match.group(1)

    if hex_digits.startswith("00000000"):
        return "0x" + hex_digits[8:]

    return match.group(0)


def normalize_line(line: str) -> Optional[str]:
    """
    Normalize one RVFI trace line.

    Rules:
      - remove anything after ';'
      - remove trailing whitespace
      - ignore rs1 and rs2 fields
    """
    line = line.rstrip("\n")

    # Remove comments after semicolon.
    # Example:
    #   insn : 0x400046b7 ; lui x13, 0x40004
    # becomes:
    #   insn : 0x400046b7
    line = line.split(";", 1)[0]

    # Remove trailing whitespace left by comment removal.
    line = line.rstrip()

    # Ignore rs1 / rs2 fields.
    if IGNORE_FIELD_RE.match(line):
        return None
    if re.match(r"^\s*pc_rdata\s*:", line):
        line = HEX16_RE.sub(shorten_16_digit_hex, line)
    if re.match(r"^\s*mem_addr\s*:", line):
        line = HEX16_RE.sub(shorten_16_digit_hex, line)

    return line


def normalize_file(in_path: str, out_path: str) -> None:
    with open(in_path, "r", encoding="utf-8", errors="replace") as inp:
        with open(out_path, "w", encoding="utf-8") as out:
            for line in inp:
                norm = normalize_line(line)
                if norm is None:
                    continue

                out.write(norm)
                out.write("\n")


def find_diff_tool(user_tool: Optional[str]) -> str:
    if user_tool is not None:
        tool = shutil.which(user_tool)
        if tool is None:
            print("ERROR: diff tool not found: {}".format(user_tool), file=sys.stderr)
            sys.exit(1)
        return tool

    for candidate in ["tkdiff", "meld", "kdiff3", "code"]:
        tool = shutil.which(candidate)
        if tool is not None:
            return tool

    print(
        "ERROR: could not find tkdiff, meld, kdiff3, or code in PATH",
        file=sys.stderr,
    )
    sys.exit(1)


def launch_diff(tool: str, left: str, right: str) -> int:
    name = os.path.basename(tool)

    if name == "code":
        cmd = [tool, "--diff", left, right]
    else:
        cmd = [tool, left, right]

    return subprocess.call(cmd)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Graphically diff two RVFI packet traces after normalization."
    )

    parser.add_argument("left", help="First RVFI trace file")
    parser.add_argument("right", help="Second RVFI trace file")

    parser.add_argument(
        "--tool",
        default=None,
        help="GUI diff tool to use, for example: tkdiff, meld, kdiff3, code",
    )

    parser.add_argument(
        "--keep",
        action="store_true",
        help="Keep normalized temporary files",
    )

    args = parser.parse_args()

    if not os.path.isfile(args.left):
        print("ERROR: left file does not exist: {}".format(args.left), file=sys.stderr)
        return 1

    if not os.path.isfile(args.right):
        print("ERROR: right file does not exist: {}".format(args.right), file=sys.stderr)
        return 1

    tool = find_diff_tool(args.tool)

    tmpdir = tempfile.mkdtemp(prefix="rvfi_gdiff_")

    left_norm = os.path.join(tmpdir, "left.normalized.rvfi")
    right_norm = os.path.join(tmpdir, "right.normalized.rvfi")

    try:
        normalize_file(args.left, left_norm)
        normalize_file(args.right, right_norm)

        print("Normalized left : {}".format(left_norm))
        print("Normalized right: {}".format(right_norm))
        print("Launching       : {}".format(os.path.basename(tool)))

        rc = launch_diff(tool, left_norm, right_norm)

        if args.keep:
            print("Kept normalized files in: {}".format(tmpdir))
        else:
            shutil.rmtree(tmpdir, ignore_errors=True)

        return rc

    except Exception as e:
        print("ERROR: {}".format(e), file=sys.stderr)

        if args.keep:
            print("Kept temporary directory: {}".format(tmpdir), file=sys.stderr)
        else:
            shutil.rmtree(tmpdir, ignore_errors=True)

        return 1


if __name__ == "__main__":
    sys.exit(main())
