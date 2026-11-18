#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_wfi_debug_halt_blk block-level test.

Reproduces KUDU-003: WFI sleep is not woken by a debug halt request.

tb_wfi_debug_halt.sv instantiates the real ir_decoder and issuer
(CHERIoTEn=1, cheri_pmode_i=0, M-mode, MIE=0) with the execution pipelines
tied ready and the scoreboard empty. The decoder decodes a real WFI
(0x10500073); no internal state is forced. Controls: a halt request during
normal execution enters debug mode; a pending interrupt wakes WFI (MIE=0) and
a halt then works. The check: after WFI has stopped fetching, debug_req_i is
held for 32 cycles with no interrupt pending; the core must take the
halt-request redirect to DmHaltAddr and enter debug mode
("TRIGGER halt during WFI PASS"). Before the fix (802d481) CSM_SLEEP only
left on irq_pending_i, so the run printed "TRIGGER halt during WFI FAIL" and
stopped with $fatal. The run ends with "PASS: sleeping core honors debug
halt". The stepped-WFI part of KUDU-003 is covered by rtl_bug_issuer_debug
(case I5).

The script compiles the TB with vcs against the repository's rtl/ (packages,
ir_decoder.sv, issuer.sv) in the run directory, then runs it.

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
  $R/cheri_pkg.sv $R/csr_pkg.sv $R/super_pkg.sv $R/ir_decoder.sv $R/issuer.sv \
  $TEST_DIR/tb_wfi_debug_halt.sv -top tb_wfi_debug_halt \
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
    "rtl_bug_wfi_debug_halt_blk", ["KUDU-003"],
    [Run("blk", None, None, script=SCRIPT, est=60)],
    r"^PASS: sleeping core honors debug halt",
    [(r"^TRIGGER halt during WFI FAIL", "KUDU-003")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
