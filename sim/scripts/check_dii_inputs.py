#!/usr/bin/env python3

import re
import sys
from collections import defaultdict

if len(sys.argv) != 2:
    print(f"Usage: {sys.argv[0]} <input_file>")
    sys.exit(1)

filename = sys.argv[1]

# Regex to extract the hex address inside mem[X,0x...]
addr_re = re.compile(r"mem\[\s*X\s*,\s*(0x[0-9A-Fa-f]+)\s*\]")

addr_count = defaultdict(int)
line_numbers = defaultdict(list)

try:
    with open(filename) as f:
        for lineno, line in enumerate(f, start=1):
            m = addr_re.search(line)
            if m:
                addr = int(m.group(1), 16)
                addr_count[addr] += 1
                line_numbers[addr].append(lineno)
except FileNotFoundError:
    print(f"Error: file not found: {filename}")
    sys.exit(1)

# Report duplicates
duplicates_found = False
for addr, count in addr_count.items():
    if count > 1:
        duplicates_found = True
        lines = ", ".join(map(str, line_numbers[addr]))
        print(f"Duplicate address {addr:#010x} appears {count} times (lines {lines})")

if not duplicates_found:
    print("No duplicate addresses found.")

