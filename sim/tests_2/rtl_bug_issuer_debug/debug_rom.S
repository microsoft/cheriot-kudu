// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Debug ROM for rtl_bug_issuer_debug. The test writes the integer address of
// its mailbox to TB scratch_reg1 (0x8380_0004) and the case number to mb[0],
// then raises debug_req. CHERI checks are off in debug mode, so the ROM uses
// untagged integer addresses. The ROM is register-transparent: it works in
// c5/c6 only and saves them in DSCRATCHC0/1 (SCR 25/26), so it can halt
// anywhere, including inside the trap handler.
//
// Mailbox (32-bit words):
//   0 case   1 ROM entry count   2/3 dpc at entry 1/2   6/7 dcsr at entry 1/2
//   10 x15 at entry 1   11 x14 at entry 1   16 step target (set by the test)
//
// Cases: 1 record only, 2/5 step, 3 step with MIE set, 4 step with ebreakm.

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
    csw x15, 40(c5)          // mb[10] = x15 (progress counter of the test)
    csw x14, 44(c5)          // mb[11] = x14 (link register of the test)
    j 2f
1:  addi x6, x6, -1
    bnez x6, 2f              // entries after the second are counted only
    cspecialr c6, 24         // DEPCC (RV32 dpc is illegal at PMODE=1)
    csw x6, 12(c5)           // mb[3] = dpc
    csrr x6, 0x7b0
    csw x6, 28(c5)           // mb[7] = dcsr
2:  clw x6, 0(c5)            // case number
    addi x6, x6, -2
    beqz x6, case_step
    addi x6, x6, -1
    beqz x6, case_step_irq
    addi x6, x6, -1
    beqz x6, case_step_ebreak
    addi x6, x6, -1
    beqz x6, case_step
    j rom_exit

// Entry 1: dcsr.step = 1 and resume at the step target (mb[16]).
// Entry 2: dcsr.step = 0 and resume at dpc.
case_step:
    clw x6, 4(c5)
    addi x6, x6, -1
    bnez x6, step_done
    csrsi 0x7b0, 4           // dcsr.step
    j redirect

case_step_irq:
    clw x6, 4(c5)
    addi x6, x6, -1
    bnez x6, step_irq_done
    csrsi 0x7b0, 4           // dcsr.step
    csrsi mstatus, 8         // MIE = 1; MEIP is already pending
    j redirect
step_irq_done:
    csrci mstatus, 8         // MIE = 0
    j step_done

case_step_ebreak:
    clw x6, 4(c5)
    addi x6, x6, -1
    bnez x6, step_ebreak_done
    csrsi 0x7b0, 4           // dcsr.step
    li x6, 0x8000
    csrs 0x7b0, x6           // dcsr.ebreakm
    j redirect
step_ebreak_done:
    li x6, 0x8000
    csrc 0x7b0, x6
    cspecialr c6, 24         // DEPCC
    cincoffset c6, c6, 4     // skip the ebreak
    cspecialw 24, c6
    j step_done

step_done:
    csrci 0x7b0, 4           // dcsr.step = 0
    j rom_exit

redirect:
    cspecialr c6, 24         // DEPCC (main PCC)
    clw x5, 64(c5)           // mb[16] = step target
    csetaddr c6, c6, x5
    cspecialw 24, c6

rom_exit:
    cspecialr c5, 25
    cspecialr c6, 26
    dret
