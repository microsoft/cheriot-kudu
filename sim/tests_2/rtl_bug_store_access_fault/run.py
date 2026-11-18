#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_store_access_fault block-level test.

Reproduces KUDU-002: store bus error reported as load access fault.

tb_store_access_fault.sv instantiates the real load_store_unit (CHERIoTEn=1,
cheri_pmode_i=0) and drives decoded aligned `lw x3,0(x1)` / `sw x2,0(x1)`
requests through the normal data-bus handshake, without forcing internal
state. Controls: successful LW and SW, and a LW bus error (mcause 5). The
checks: a SW bus error with immediate grant/response and one with delayed
grant/response must report mcause 7 (store/AMO access fault) and
mtval 0x80001000. Each case prints "PASS <case>" or "FAIL <case>: observed
mcause=..."; the run ends with "PASS: all access-fault checks". Before the
fix (cd63cce) both SW cases reported mcause 5.

The script compiles the TB with vcs against the repository's rtl/ (packages
plus load_store_unit.sv) in the run directory, then runs it.

Expected on HEAD: PASS (bug fixed).

Run from anywhere: ./run.py [--work <new dir>] (see ../common/kudu_test.py and
sim/testplan/direct_tests.md). --build is not used.
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, main  # noqa: E402

SCRIPT = r"""
R=$REPO/rtl
vcs -full64 -sverilog -timescale=1ns/1ps +define+CHERIoT \
  $R/cheri_pkg.sv $R/csr_pkg.sv $R/super_pkg.sv $R/load_store_unit.sv \
  $TEST_DIR/tb_store_access_fault.sv -top tb_store_access_fault \
  -o simv -Mdir=csrc -l compile.log > compile.out 2>&1
rc=$?
if [ $rc -ne 0 ] || [ ! -x simv ]; then
  tail -n 40 compile.log
  echo "ERROR: vcs compile failed (exit $rc)"
  exit 1
fi
./simv
"""

TEST = Test(
    "rtl_bug_store_access_fault", ["KUDU-002"],
    [Run("blk", None, None, script=SCRIPT, est=60)],
    r"^PASS: all access-fault checks",
    [(r"^FAIL SW access fault ", "KUDU-002"), (r"STORE_ACCESS_FAULT_REPRO", "KUDU-002")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
