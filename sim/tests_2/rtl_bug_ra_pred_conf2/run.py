#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_ra_pred_conf2 test.

Reproduces KUDU-048: in pipeline configuration 2 (no IR stage 1) the
RA-prediction / predicted-PCC outputs of ir_stage (ir_cjalr_pcc_set,
ir_cjalr_rcap) were left undriven, so they were X at the top level.

The program (cheri flavour, PMODE=1, from the RA review "ra_odd") runs 6000
iterations of `cmove cra, <sealed backward sentry with an odd address>;
cret`, so the core issues one cjalr return per iteration, with an
interrupt handler that counts interrupts taken with an odd mepcc. It
prints "RA_ODD nodd=.. nirq=.. nexc=.. PASS" (FAIL if any mepcc was odd).
For the tests_2 port the program also unmasks external interrupt line 0 in
the TB intr_mask register so the irq run actually takes interrupts.

ra_chk.sv is compiled as an extra top-level module (shadow build, conf2).
It checks that ir_cjalr_pcc_set is never X, that every issued instruction
was checked at IR against a PCC equal to the architectural ex1_pcc_cap_q
(C1), and that no fetch leaves populated memory (C3). Its final block
prints "RA_CHK FAIL KUDU-048 x_err=N" for X cycles, "RA_CHK FAIL ..." for
other errors or when no cjalr issued, and "RA_CHK PASS ..." otherwise. The
pass verdict needs both "RA_ODD ... PASS" and "RA_CHK PASS".

Runs: base, delayed memory (ws) and random external interrupts (irq).

Expected on HEAD: PASS (bug fixed; conf2 ties the outputs to 0).

Needs the checker and conf2, so the runner builds a shadow simv/simv32 in the
work directory (--build is not used).

Run from anywhere: ./run.py [--work <new dir>] (see ../common/kudu_test.py and
sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "common"))
from kudu_test import Run, Shadow, Test, main  # noqa: E402

BASE = ["+PMODE=1", "+TIMEOUT=3000000"]
WS = ["+INSTR_GNT_WMAX=2", "+INSTR_RESP_WMAX=3", "+DATA_GNT_WMAX=2", "+DATA_RESP_WMAX=3"]

TEST = Test(
    "rtl_bug_ra_pred_conf2", ["KUDU-048"],
    [Run("base", "simv", "cheri", BASE, est=10),
     Run("ws", "simv", "cheri", BASE + WS, est=15),
     Run("irq", "simv", "cheri", BASE + ["+INTR_RATE=4"], est=10)],
    r"(?s)^RA_ODD nodd=00000000 .* PASS$.*^RA_CHK PASS",
    [(r"RA_CHK FAIL KUDU-048 ", "KUDU-048")],
    shadow=Shadow(extra=[HERE / "ra_chk.sv"]),
    conf="2")

if __name__ == "__main__":
    sys.exit(main([TEST]))
