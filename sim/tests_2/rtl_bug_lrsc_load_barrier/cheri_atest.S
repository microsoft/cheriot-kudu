// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// LR/SC/AMO/load through a capability that was just loaded by CLC from a
// revoked heap object (load barrier must clear the tag before use).
.option norelax
.option norvc
.section .text
.globl cheri_atest

// record (32 B): 0 rd, 4 tag(c1) after, 8 mem, 12 trapped, 16 mcause, 20 mtval
.macro OBS_INIT
    csw zero, 12(c10)
    csw zero, 16(c10)
    csw zero, 20(c10)
.endm

#define LR_X5_C1      .word ((2 << 27) | (0 << 20) | (1 << 15) | (2 << 12) | (5 << 7) | 0x2f)
#define SC_X5_X6_C1   .word ((3 << 27) | (6 << 20) | (1 << 15) | (2 << 12) | (5 << 7) | 0x2f)
#define AMOADD_X5_X6_C1 .word ((0 << 27) | (6 << 20) | (1 << 15) | (2 << 12) | (5 << 7) | 0x2f)
#define LR_X12_C7     .word ((2 << 27) | (0 << 20) | (7 << 15) | (2 << 12) | (12 << 7) | 0x2f)

// op: 0 lr.w, 1 sc.w (after lr on a good cap), 2 clw, 3 csw, 4 amoadd.w
.macro CASE slot, op, nops
    OBS_INIT
    li x5, 0xdeadbeef
    li x6, 0x5a5a5a5a
.if \op == 1
    LR_X12_C7                 // make a reservation using the good register cap
.endif
    clc c1, 0(\slot)
    .rept \nops
    nop
    .endr
.if \op == 0
    LR_X5_C1
.elseif \op == 1
    SC_X5_X6_C1
.elseif \op == 2
    clw x5, 0(c1)
.elseif \op == 3
    csw x6, 0(c1)
.else
    AMOADD_X5_X6_C1
.endif
    csw x5, 0(c10)
    cgettag x12, c1
    csw x12, 4(c10)
    clw x12, 0(c7)
    csw x12, 8(c10)
    li x12, 0x12345678
    csw x12, 0(c7)
    cincoffset c10, c10, 32
.endm

.macro CASES slot, op
    CASE \slot, \op, 0
    CASE \slot, \op, 2
    CASE \slot, \op, 4
    CASE \slot, \op, 8
.endm

.balign 16
trap_handler:
    csrr x14, mcause
    csw x14, 16(c10)
    csrr x14, mtval
    csw x14, 20(c10)
    li x14, 1
    csw x14, 12(c10)
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

    // TSMAP word for heap base 0x80020000: 0x83000000 + (0x20000>>8)*4 = 0x83000800 bit 0
    lui x11, 0x83000
    addi x11, x11, 0x400
    addi x11, x11, 0x400
    csetaddr c9, c6, x11
    li x12, 1
    csw x12, 0(c9)

    // revoked object c7 @0x80020000 len 16; slot c8 @0x80030000 holds it
    lui x11, 0x80020
    csetaddr c7, c6, x11
    li x12, 16
    csetbounds c7, c7, x12
    li x12, 0x12345678
    csw x12, 0(c7)
    lui x11, 0x80030
    csetaddr c8, c6, x11
    csc c7, 0(c8)

    // non-revoked object c4 @0x80028000; slot c9 @0x80030010 holds it
    lui x11, 0x80028
    csetaddr c4, c6, x11
    li x12, 16
    csetbounds c4, c4, x12
    lui x11, 0x80030
    addi x11, x11, 16
    csetaddr c9, c6, x11
    csc c4, 0(c9)

    CASES c8, 0
    CASES c8, 1
    CASES c8, 2
    CASES c8, 3
    CASES c8, 4
    // control: non-revoked object (lr and clw must succeed)
    cmove c7, c4
    li x12, 0x12345678
    csw x12, 0(c7)
    CASE c9, 0, 0
    CASE c9, 2, 0

    clc c8, 24(csp)
    cspecialw mtcc, c8
    clc cra, 0(csp)
    clc c8, 8(csp)
    clc c9, 16(csp)
    clc c3, 32(csp)
    clc c4, 40(csp)
    cincoffset csp, csp, 64
    cret
