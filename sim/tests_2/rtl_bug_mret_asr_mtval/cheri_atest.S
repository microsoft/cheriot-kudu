// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.option norelax
.section .text
.globl cheri_atest

.macro ADDRESS reg, symbol
    lui \reg, %hi(\symbol)
    addi \reg, \reg, %lo(\symbol)
.endm

// c10 holds the results array across the deliberate trap.
.align 4
mret_asr_handler:
    csrr t0, mcause
    csw t0, 0(c10)
    csrr t0, mtval
    csw t0, 4(c10)
    li t0, 1
    csw t0, 8(c10)

    auipcc c8, 0
    ADDRESS t0, after_fault
    csetaddr c8, c8, t0
    cspecialw mepcc, c8
    mret

cheri_atest:
    cincoffset csp, csp, -40
    csc cra, 0(csp)
    csc c8, 8(csp)
    csc c9, 16(csp)
    csc c10, 24(csp)
    csc ct0, 32(csp)

    cmove c10, ca0
    csw zero, 0(c10)
    csw zero, 4(c10)
    csw zero, 8(c10)

    auipcc c8, 0
    ADDRESS t0, mret_asr_handler
    csetaddr c8, c8, t0
    cspecialw mtcc, c8

    auipcc c9, 0
    ADDRESS t0, no_asr_mret
    csetaddr c9, c9, t0
    li t0, 0xff7f
    candperm c9, c9, t0
    cjalr c0, 0(c9)

    // Reaching here means the jump did not take effect.
    li t0, 0xbad
    csw t0, 8(c10)
    j after_fault

no_asr_mret:
    // MRET itself requires PCC.Access_System_Registers.  This instruction is
    // fetched with a valid executable PCC whose ASR bit was cleared above.
    mret
    li t0, 0xdead
    csw t0, 8(c10)

after_fault:
    clc cra, 0(csp)
    clc c8, 8(csp)
    clc c9, 16(csp)
    clc c10, 24(csp)
    clc ct0, 32(csp)
    cincoffset csp, csp, 40
    cret
