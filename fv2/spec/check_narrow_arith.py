#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Check that the generated spec calls the integer-division stubs only at the
call sites E2E_NARROW_ARITH (stub.sv) was justified for. Run after every spec
regeneration: python3 check_narrow_arith.py <ibexspec.sv>"""
import re, sys

src = open(sys.argv[1]).read().split("\n")
expect = {"sail_emod_int": {"getCapLength", "is_aligned_addr"},
          "sail_tmod_int": {"execute_REM"},
          "sail_tdiv_int": {"execute_DIV"}}
fn, seen, ok = None, {k: set() for k in expect}, True
for ln, line in enumerate(src, 1):
    m = re.search(r"function automatic .*?\b(\w+)\s*\(", line)
    if m:
        fn = m.group(1)
        continue
    for stub in expect:
        if re.search(r"\b%s\s*\(" % stub, line):
            seen[stub].add(fn)
            if fn not in expect[stub]:
                ok = False
                print(f"UNEXPECTED {stub} in {fn} (line {ln})")
# The divisors at the emod sites must be powers of two.
for ln, line in enumerate(src, 1):
    m = re.search(r"is_aligned_addr\((\w+), (\w+)\)", line)
    if m and "function" not in line:
        ctx = "\n".join(src[max(0, ln - 6):ln])
        if not (re.search(m.group(2) + r" = 128'h0+8;", ctx) or
                re.search(m.group(2) + r" = unsigned'\(128'\(signed'\(\{width\}\)\)\);", ctx)):
            ok = False
            print(f"UNCHECKED is_aligned_addr divisor at line {ln}")
for stub in expect:
    print(stub, sorted(x for x in seen[stub] if x))
print("NARROW_ARITH_CHECK:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
