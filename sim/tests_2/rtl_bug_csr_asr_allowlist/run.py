#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_csr_asr_allowlist directed test.

Reproduces KUDU-017: Counter writes allowed without PCC.ASR
Reproduces KUDU-018: Unimplemented CSR without ASR reports a CHERI fault

Expected on HEAD: PASS (bug fixed).

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Test, T1M, cheri_dly, main  # noqa: E402

TEST = Test(
    "rtl_bug_csr_asr_allowlist", ["KUDU-017", "KUDU-018"], cheri_dly(T1M),
    r"CSR ASR PASS failures=0 cases=8",
    [(r"^FAIL csrw 0x0b[08][02]\b", "KUDU-017"), (r"^FAIL csr[rw] 0x0323\b", "KUDU-018")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
