// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Debug ROM for step_exec. The test writes the integer mailbox address to TB
// scratch_reg1 (0x8380_0004). Register-transparent: uses c5/c6 only, saved in
// DSCRATCHC0/1 (SCR 25/26).
//
// Mailbox words: 0 phase, 1 entries, 2 entries in phase STEPPING,
//   3 dcsr at last entry, 4 dcsr at CLEAR entry, 5 ROM-computed value,
//   6 STEPPING entries whose dcsr.cause is not STEP (4).
// Phases: 1 SET (set dcsr.step, -> 2), 2 STEPPING (count only),
//   3 CLEAR (compute a value with step still set, clear step, -> 4), 4 DONE.

.option norvc
.section .text
.globl _start

_start:
    cspecialw 25, c5
    cspecialw 26, c6
    li x5, 0x83800000
    csw x0, 0x140(c5)        // deassert debug_req
    clw x5, 4(c5)            // mailbox
    clw x6, 4(c5)
    addi x6, x6, 1
    csw x6, 4(c5)            // entries++
    csrr x6, 0x7b0
    csw x6, 12(c5)           // dcsr at this entry
    clw x6, 0(c5)
    addi x6, x6, -1
    beqz x6, ph_set
    addi x6, x6, -1
    beqz x6, ph_stepping
    addi x6, x6, -1
    beqz x6, ph_clear
    j rom_exit

ph_stepping:
    clw x6, 8(c5)
    addi x6, x6, 1
    csw x6, 8(c5)
    csrr x6, 0x7b0
    srli x6, x6, 6
    andi x6, x6, 7
    addi x6, x6, -4
    beqz x6, rom_exit
    clw x6, 24(c5)
    addi x6, x6, 1
    csw x6, 24(c5)
    j rom_exit

ph_clear:
    csrr x6, 0x7b0
    csw x6, 16(c5)
    // runs in debug mode with dcsr.step still 1: expect 1682
    li x6, 7
    slli x6, x6, 4
    addi x6, x6, 3           // 115
    xori x6, x6, 0x5a        // 41
    mul x6, x6, x6           // 1681
    csw x6, 20(c5)
    clw x6, 20(c5)
    addi x6, x6, 1
    bnez x6, 1f
    li x6, 0
1:  csw x6, 20(c5)
    li x6, 4
    csw x6, 0(c5)            // phase DONE
    csrci 0x7b0, 4           // dcsr.step = 0
    j rom_exit

ph_set:
    li x6, 2
    csw x6, 0(c5)            // phase STEPPING
    cspecialr c5, 25
    cspecialr c6, 26
    csrsi 0x7b0, 4           // dcsr.step = 1, last instruction before dret
    dret

rom_exit:
    cspecialr c5, 25
    cspecialr c6, 26
    dret
