// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Single-step cases S13/S14 (from the round-4 cases_s.S). Log entry 0 is the
// ebreak that starts stepping.


// S13: step onto an ebreak (ebreakm = 1): the step completes first
// (cause 4, dpc = ebreak), the ebreak enters debug on the next resume
case_33:
    STEP_BEGIN c33_3
c33_1: addi x5, x0, 1
c33_2: ebreak
c33_3: nop
    CHKM 3301, MB_CNT, 3
    STEPCHK 3302, 1, c33_2
    CHKDPC 3303, 2, c33_2
    CHKCAUSE 3304, 2, 1
    j case_end

// S14: step onto an instruction with an execute trigger: step halts with
// cause 4 (Debug Spec 4.4), trigger fires on the next resume (cause 2)
case_34:
    SET_TRIG c34_2, none
    STEP_BEGIN c34_3
c34_1: addi x5, x0, 1
c34_2: addi x5, x5, 1
c34_3: nop
    CHKM 3401, MB_CNT, 4
    STEPCHK 3402, 1, c34_2
    CHKDPC 3403, 2, c34_2
    CHKCAUSE 3404, 2, 2
    STEPCHK 3405, 3, c34_3
    CHKREG 3406, 5, 2
    j case_end

