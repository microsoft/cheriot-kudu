// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Debug ROM for rtl_bug_halt_step_cause. The test writes the integer address
// of its mailbox to TB scratch_reg1 (0x8380_0004) and the case number to
// mb[0], then raises debug_req. CHERI checks are off in debug mode, so the ROM
// uses untagged integer addresses. The ROM is register-transparent: it works
// in c5/c6 only and saves them in DSCRATCHC0/1 (SCR 25/26).
//
// Mailbox (32-bit words):
//   0 case   1 ROM entry count   2/3 dpc at entry 1/2   6/7 dcsr at entry 1/2
//   16 step target (set by the test)
//
// Cases: 1 record only, 2 step (entry 1 sets dcsr.step and resumes at the
// step target; entry 2 clears dcsr.step and resumes at dpc).

.section .text
.globl _start

_start:
    cspecialw 25, c5         // DSCRATCHC0
    cspecialw 26, c6         // DSCRATCHC1
    li x5, 0x83800000
    csw x0, 0x140(c5)        // deassert debug_req
    clw x5, 4(c5)            // x5 = mailbox address
    clw x6, 4(c5)
    addi x6, x6, 1
    csw x6, 4(c5)            // entry count++
    addi x6, x6, -1
    bnez x6, 1f
    cspecialr c6, 24         // DEPCC (RV32 dpc is illegal at PMODE=1)
    csw x6, 8(c5)            // mb[2] = dpc
    csrr x6, 0x7b0
    csw x6, 24(c5)           // mb[6] = dcsr
    j 2f
1:  addi x6, x6, -1
    bnez x6, 2f              // entries after the second are counted only
    cspecialr c6, 24
    csw x6, 12(c5)           // mb[3] = dpc
    csrr x6, 0x7b0
    csw x6, 28(c5)           // mb[7] = dcsr
2:  clw x6, 0(c5)            // case number
    addi x6, x6, -2
    beqz x6, case_step
    j rom_exit

case_step:
    clw x6, 4(c5)
    addi x6, x6, -1
    bnez x6, step_done
    csrsi 0x7b0, 4           // dcsr.step
    cspecialr c6, 24         // DEPCC (main PCC)
    clw x5, 64(c5)           // mb[16] = step target
    csetaddr c6, c6, x5
    cspecialw 24, c6
    j rom_exit

step_done:
    csrci 0x7b0, 4           // dcsr.step = 0

rom_exit:
    cspecialr c5, 25
    cspecialr c6, 26
    dret
