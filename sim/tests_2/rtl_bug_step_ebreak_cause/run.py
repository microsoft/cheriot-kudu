#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""rtl_bug_step_ebreak_cause directed test.

Reproduces KUDU-071: a completed single step reports dcsr.cause EBREAK/TRIGGER
instead of STEP when the next instruction is an ebreak or an execute-trigger
match.

The program is the round-4 directed debug suite (shared case framework
cases_common.S + a programmable, register-transparent debug ROM that logs
dcsr/dpc/mcause/mepc of every debug entry into a mailbox), reduced to the two
KUDU-071 cases. Each case is preceded by a reset case (0).
  case 33: start stepping with an ebreak (ebreakm=1), step an addi whose
           successor is an ebreak. Expected (Debug spec 0.13.2 4.4): the step
           halts with cause STEP (4) at dpc = ebreak, and the ebreak enters
           debug with cause EBREAK on the next resume (3 entries).
  case 34: the same with an execute trigger (tdata2) on the next instruction:
           STEP first, then TRIGGER (2) on the next resume (4 entries).
HEAD reports the step completion with cause EBREAK (dcsr 0x40008047) /
TRIGGER (0x40008087); the ROM then skips the ebreak, so case 33 sees only 2
entries (check 3301) and case 34 only 3 (check 3401).
Output: "CASE <n> PASS|FAIL r0= n= fid= got= exp= ..." plus per-entry log
lines, then "DBGT DONE fails=N".

Runs (+DBGROM=debug_rom; the ROM is built per flavour by build_prog.sh, gcc at
0x84000000 for rv32 and clang + link_dbgrom.ld with -DCHERIOT for cheri):
  rv32     simv32, rv32 program
  cheriot  simv +PMODE=0, rv32 program
  cheri    simv +PMODE=1, CHERIoT program

Expected on HEAD: XFAIL (KUDU-071, Open) on all three runs: "CASE 33 FAIL",
"CASE 34 FAIL", "DBGT DONE fails=2". A fixed RTL gives "DBGT DONE fails=0".

Run from anywhere: ./run.py [--build <dir with simv/simv32>] [--work <new dir>]
(see ../common/kudu_test.py and sim/testplan/direct_tests.md).
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "common"))
from kudu_test import Run, Test, main  # noqa: E402

ARGS = ["+DBGROM=debug_rom", "+TIMEOUT=2000000"]

TEST = Test(
    "rtl_bug_step_ebreak_cause",
    ["KUDU-071"],
    [Run("rv32", "simv32", "rv32", ARGS, est=5),
     Run("cheriot", "simv", "rv32", ["+PMODE=0"] + ARGS, est=5),
     Run("cheri", "simv", "cheri", ["+PMODE=1"] + ARGS, est=5)],
    r"^DBGT DONE fails=0$",
    [(r"^CASE 3[34] FAIL", "KUDU-071")])

if __name__ == "__main__":
    sys.exit(main([TEST]))
