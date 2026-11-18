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

// c10 holds the observation structure capability while deliberate illegal traps
// are skipped.  All checked instructions are 32-bit words.
.align 4
sail_zbkb_zbkx_trap_handler:
    csrr a4, mcause
    clw a5, 0(c10)
    addi a5, a5, 1
    csw a5, 0(c10)
    clw a5, 4(c10)
    bnez a5, 1f
    csw a4, 4(c10)
1:
    cspecialr ca1, mepcc
    cincoffset ca1, ca1, 4
    cspecialw mepcc, ca1
    mret

cheri_atest:
    cincoffset csp, csp, -48
    csc cra, 0(csp)
    csc c8, 8(csp)
    csc c9, 16(csp)
    csc c10, 24(csp)
    csc ca1, 32(csp)
    csc ct0, 40(csp)

    cmove c10, ca0
    cspecialr c9, mtcc

    csw zero, 0(c10)
    csw zero, 4(c10)
    csw zero, 8(c10)
    csw zero, 12(c10)
    csw zero, 16(c10)
    csw zero, 20(c10)
    csw zero, 24(c10)
    csw zero, 28(c10)

    auipcc c8, 0
    ADDRESS t0, sail_zbkb_zbkx_trap_handler
    csetaddr c8, c8, t0
    cspecialw mtcc, c8

    li t0, 0x11223344
    li t1, 0x55667788
    li t2, 0
    .word 0x0862f3b3 // packh t2, t0, t1 (Sail Zbkb)
    csw t2, 8(c10)

    li t0, 0x44332211
    li t1, 0x00010203
    li t2, 0
    .word 0x2862c3b3 // xperm8 t2, t0, t1 (Sail Zbkx)
    csw t2, 12(c10)

    li t0, 0x01234567
    li t2, 0
    .word 0x6872d393 // brev8 t2, t0 (Sail Zbkb)
    csw t2, 16(c10)

    li t0, 0x01234567
    li t2, 0
    .word 0x08f29393 // zip t2, t0 (Sail Zbkb, RV32)
    csw t2, 20(c10)

    li t0, 0x10131c1f
    li t2, 0
    .word 0x08f2d393 // unzip t2, t0 (Sail Zbkb, RV32)
    csw t2, 24(c10)

    li t0, 0x13579bdf
    csw t0, 28(c10)

    cspecialw mtcc, c9
    clc cra, 0(csp)
    clc c8, 8(csp)
    clc c9, 16(csp)
    clc c10, 24(csp)
    clc ca1, 32(csp)
    clc ct0, 40(csp)
    cincoffset csp, csp, 48
    cret
