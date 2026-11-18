// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.option norelax
.option norvc
.section .text
.globl cheri_atest

.macro ADDRESS reg, symbol
    lui \reg, %hi(\symbol)
    addi \reg, \reg, %lo(\symbol)
.endm

.balign 16
alignment_handler:
    csrr t0, mcause
    csw t0, 0(c10)
    csrr t0, mtval
    csw t0, 4(c10)
    li t0, 1
    csw t0, 8(c10)
    cspecialw mepcc, c11
    mret

cheri_atest:
    cincoffset csp, csp, -40
    csc cra, 0(csp)
    csc c8, 8(csp)
    csc c9, 16(csp)
    csc c12, 24(csp)
    cspecialr c9, mtcc
    csc c9, 32(csp)
    cmove c10, ca0
    cincoffset c12, ca1, 4
    cgetaddr t0, c12
    csw t0, 12(c10)
    csw t0, 28(c10)
    auipcc c8, 0
    ADDRESS t0, alignment_handler
    csetaddr c8, c8, t0
    cspecialw mtcc, c8

    auipcc c11, 0
    ADDRESS t0, after_store
    csetaddr c11, c11, t0
    // Distinct preceding access makes stale mtval deterministic.
    csw zero, 12(c12)
    csc cnull, 0(c12)
after_store:
    cincoffset c10, c10, 16
    auipcc c11, 0
    ADDRESS t0, after_load
    csetaddr c11, c11, t0
    csw zero, 12(c12)
    clc ca3, 0(c12)
after_load:
    clc c9, 32(csp)
    cspecialw mtcc, c9
    clc cra, 0(csp)
    clc c8, 8(csp)
    clc c9, 16(csp)
    clc c12, 24(csp)
    cincoffset csp, csp, 40
    cret
