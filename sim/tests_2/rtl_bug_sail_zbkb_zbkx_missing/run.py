#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_sail_zbkb_zbkx_missing: Kudu vs CHERIoT Sail: Zbkb/Zbkx encodings (pack, packh, brev8, zip, unzip,
xperm4, xperm8) trap as illegal on Kudu but are legal in Sail. Kudu implements
B (Zba/Zbb/Zbc/Zbs), not scalar crypto, so this is a documented model
divergence (bug_logs.md, Sail divergences), not a KUDU bug.

Expected on HEAD: DEFER (divergence waived). To confirm against Sail, run the
built ELF (programs/<name>.cheri/<name>.elf in the work dir) on the Sail emulator.

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, T1M, main  # noqa: E402

TEST = Test(
    "rtl_bug_sail_zbkb_zbkx_missing", [],
    [Run("cheriot", "simv", "cheri", ["+PMODE=1"] + T1M)],
    r"SAIL ZBKB ZBKX PASS failures=0x0+ cases=0x00000008",
    [(r"", "SAIL-ZBKB")], known={"SAIL-ZBKB": "Waived"}, regression=False)

if __name__ == "__main__":
    sys.exit(main([TEST]))
