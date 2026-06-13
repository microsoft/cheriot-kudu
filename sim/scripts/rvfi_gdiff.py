#!/usr/bin/env python3

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Optional


HEX_RE = re.compile(r"0x([0-9a-fA-F]+)")
HEX16_RE = re.compile(r"0x([0-9a-fA-F]{16})")
MASK64 = (1 << 64) - 1
MASK32 = (1 << 32) - 1


class NormalizeState:
    def __init__(self) -> None:
        self.in_leading_hash_comments = True
        self.kept_first_hash_rvfi_packet = False


def shorten_16_digit_hex(match):
    hex_digits = match.group(1)

    if hex_digits.startswith("00000000"):
        return "0x" + hex_digits[8:]

    return match.group(0)


def format_hex(width_bits: int, value: int) -> str:
    if width_bits == 64:
        return "0x{:016x}".format(value & MASK64)
    if width_bits == 32:
        return "0x{:08x}".format(value & MASK32)
    raise ValueError("unsupported width_bits: {}".format(width_bits))


def normalize_rd_wdata_low64(line: str) -> str:
    """
    Normalize only the wdata= field on an rd line to low 64 bits.

    Example:
      rd        : x12  wdata=0x2fc00180000000000
        -> rd        : x12  wdata=0xfc00180000000000
    """
    if re.match(r"^\s*rd\s*:", line) is None:
        return line

    return re.sub(
        r"(wdata=)0x([0-9a-fA-F]+)",
        lambda mm: mm.group(1) + format_hex(64, int(mm.group(2), 16)),
        line,
        count=1,
    )


def normalize_mem_data_low32(line: str) -> str:
    """
    Normalize mem_rdata/mem_wdata-style fields to low 32 bits.

    Supported examples:
      mem_rdata : 0x123456789abcdef0
      mem_wdata : 0x123456789abcdef0
      mem       : ... rdata=0x123456789abcdef0 ... wdata=0x...
    """
    field_match = re.match(r"^\s*([A-Za-z0-9_]+)\s*:", line)
    if field_match is None:
        return line

    field = field_match.group(1)

    if field in ("mem_rdata", "mem_wdata"):
        return HEX_RE.sub(
            lambda mm: format_hex(32, int(mm.group(1), 16)),
            line,
            count=1,
        )

    if field == "mem":
        line = re.sub(
            r"(rdata=)0x([0-9a-fA-F]+)",
            lambda mm: mm.group(1) + format_hex(32, int(mm.group(2), 16)),
            line,
            count=1,
        )
        line = re.sub(
            r"(wdata=)0x([0-9a-fA-F]+)",
            lambda mm: mm.group(1) + format_hex(32, int(mm.group(2), 16)),
            line,
            count=1,
        )

    return line


def should_ignore_leading_hash_comment(line: str, state: NormalizeState) -> bool:
    """
    Ignore # comments at the beginning of the file, except preserve the first
    leading "# --- RVFI packet" line.

    Blank lines before / inside the leading comment block are ignored.
    Once the first nonblank non-# line appears, later # lines are preserved.
    """
    stripped = line.strip()

    if not state.in_leading_hash_comments:
        return False

    if stripped == "":
        return True

    if stripped.startswith("#"):
        if stripped.startswith("# --- RVFI packet") and not state.kept_first_hash_rvfi_packet:
            state.kept_first_hash_rvfi_packet = True
            return False
        return True

    state.in_leading_hash_comments = False
    return False


def normalize_line(
    line: str,
    state: NormalizeState,
    rd64: bool = False,
    mem32: bool = False,
    ign_rs: bool = False,
) -> Optional[str]:
    """
    Normalize one RVFI trace line.

    Rules:
      - ignore leading # comments at beginning of file, except keep the first "# --- RVFI packet"
      - preserve RVFI packet headers such as "--- RVFI packet"
      - always ignore order and pc_wdata lines
      - remove semicolon comments, matching the original script behavior
      - optionally ignore rs1/rs2 lines with --irs
      - optionally compare rd wdata low64 with --rd64
      - optionally compare mem_rdata/mem_wdata low32 with --mem32
      - preserve original pc_rdata/mem_addr leading-zero shortening
    """
    line = line.rstrip("\n")

    if should_ignore_leading_hash_comment(line, state):
        return None

    # Keep original rvfi_gdiff.py behavior: remove comments after semicolon.
    line = line.split(";", 1)[0].rstrip()

    if line == "":
        return None

    if re.match(r"^\s*(order|pc_wdata)\s*:", line):
        return None

    if ign_rs and re.match(r"^\s*(rs1|rs2)\s*:", line):
        return None

    if rd64:
        line = normalize_rd_wdata_low64(line)

    if mem32:
        line = normalize_mem_data_low32(line)

    if re.match(r"^\s*pc_rdata\s*:", line):
        line = HEX16_RE.sub(shorten_16_digit_hex, line)

    if re.match(r"^\s*mem_addr\s*:", line):
        line = HEX16_RE.sub(shorten_16_digit_hex, line)

    return line


def normalize_file(
    in_path: str,
    out_path: str,
    rd64: bool = False,
    mem32: bool = False,
    ign_rs: bool = False,
) -> None:
    state = NormalizeState()

    with open(in_path, "r", encoding="utf-8", errors="replace") as inp:
        with open(out_path, "w", encoding="utf-8") as out:
            for line in inp:
                norm = normalize_line(
                    line,
                    state,
                    rd64=rd64,
                    mem32=mem32,
                    ign_rs=ign_rs,
                )
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

    parser.add_argument(
        "--rd64",
        action="store_true",
        help="Compare only low 64 bits of wdata= on rd lines",
    )

    parser.add_argument(
        "--mem32",
        action="store_true",
        help="Compare only low 32 bits of mem_rdata/mem_wdata",
    )

    parser.add_argument(
        "--irs",
        action="store_true",
        help="Ignore rs1 and rs2 lines",
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
        normalize_file(
            args.left,
            left_norm,
            rd64=args.rd64,
            mem32=args.mem32,
            ign_rs=args.irs,
        )
        normalize_file(
            args.right,
            right_norm,
            rd64=args.rd64,
            mem32=args.mem32,
            ign_rs=args.irs,
        )

        print("Normalized left : {}".format(left_norm))
        print("Normalized right: {}".format(right_norm))
        if args.rd64:
            print("Normalization   : rd wdata low64")
        if args.mem32:
            print("Normalization   : mem rdata/wdata low32")
        if args.irs:
            print("Normalization   : ignoring rs1/rs2")
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
