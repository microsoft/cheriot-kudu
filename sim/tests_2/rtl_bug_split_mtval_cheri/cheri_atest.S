// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// PMODE=1: misaligned clw/clh/csw/csh straddling the end of DRAM (0x80080000
// unmapped -> data bus error on the second half). Records mcause/mtval/rd.
.option norelax
.option norvc
.section .text
.globl cheri_atest

.macro OP op, off, val
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x12, \val
    \op x12, \off(c5)
    csw x12, 8(c10)
    cincoffset c10, c10, 12
.endm
.macro REP16 op, off, val
  .rept 16
    OP \op, \off, \val
  .endr
.endm

.balign 16
trap_handler:
    csrr x14, mcause
    csw x14, 0(c10)
    csrr x14, mtval
    csw x14, 4(c10)
    cspecialr c15, mepcc
    cincoffset c15, c15, 4
    cspecialw mepcc, c15
    mret

cheri_atest:
    cincoffset csp, csp, -64
    csc cra, 0(csp)
    csc c8, 8(csp)
    csc c9, 16(csp)
    cspecialr c8, mtcc
    csc c8, 24(csp)
    csc c3, 32(csp)
    csc c4, 40(csp)
    cmove c10, ca0

    cspecialr c3, mtdc
    lui x11, 0x80000
    csetaddr c6, c3, x11
    lui x11, 0x4000
    csetbounds c6, c6, x11

    auipcc c8, 0
    lui x11, %hi(trap_handler)
    addi x11, x11, %lo(trap_handler)
    csetaddr c8, c8, x11
    cspecialw mtcc, c8

    lui x11, 0x80080
    addi x11, x11, -16
    csetaddr c5, c6, x11

    REP16 clw,  13, 0x5eadbeef
    REP16 clw,  14, 0x5eadbeef
    REP16 clw,  15, 0x5eadbeef
    REP16 clh,  15, 0x5eadbeef
    REP16 clhu, 15, 0x5eadbeef
    REP16 csw,  13, 0x11223344
    REP16 csw,  14, 0x11223344
    REP16 csw,  15, 0x11223344
    REP16 csh,  15, 0x11223344

    clc c8, 24(csp)
    cspecialw mtcc, c8
    clc cra, 0(csp)
    clc c8, 8(csp)
    clc c9, 16(csp)
    clc c3, 32(csp)
    clc c4, 40(csp)
    cincoffset csp, csp, 64
    cret
