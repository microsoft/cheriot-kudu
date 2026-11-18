#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_csr_mtval_mstatush directed test.

Reproduces KUDU-041: illegal CSR access reports mtval = 0
Reproduces KUDU-042: mstatush is not implemented
Reproduces KUDU-043: CDBG_CTRL has no effect

Expected on HEAD: XFAIL (KUDU-042 open) with DEFER for KUDU-043.

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, DLY_DATA, T1M, main  # noqa: E402

TEST = Test(
    "rtl_bug_csr_mtval_mstatush", ["KUDU-041", "KUDU-042", "KUDU-043"],
    [Run("rv32", "simv32", "rv32", ["+PMODE=0"] + T1M)]
    + [Run(pm + "_" + v, "simv", flavour, ["+PMODE=" + pm[-1]] + T1M + d)
       for pm, flavour in (("pmode0", "rv32"), ("pmode1", "cheri"))
       for v, d in (("default", []), ("delayed", DLY_DATA))],
    r"CSR MTVAL MSTATUSH PMODE=\S+ PASS failures=0 cases=16",
    [(r"^FAIL MTVAL ", "KUDU-041"), (r"^FAIL MSTATUSH ", "KUDU-042"),
     (r"^FAIL CDBG ", "KUDU-043")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
