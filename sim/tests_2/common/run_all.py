#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Run every directed test in sim/tests_2 (or those named on --tests).

Options are those of each test's run.py (see kudu_test.py), plus --tests.
All runs share the RTL builds and are packed into --jobs farm batches.
"""

import argparse
import sys

sys.dont_write_bytecode = True
import kudu_test  # noqa: E402


def main():
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("--tests", help="comma-separated test directory names (default: all)")
    args, rest = parser.parse_known_args()
    tests = kudu_test.load_tests()
    if args.tests:
        wanted = args.tests.split(",")
        missing = sorted(set(wanted) - {t.name for t in tests})
        if missing:
            print("ERROR: unknown test(s): " + ", ".join(missing), file=sys.stderr)
            return 2
        tests = [t for t in tests if t.name in wanted]
    if "-h" in rest or "--help" in rest:
        print("run_all.py [--tests a,b,...] <options below>\n")
    return kudu_test.main(tests, rest)


if __name__ == "__main__":
    sys.exit(main())
