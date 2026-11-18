// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// KUDU-032 / KUDU-036: AMO through a capability lacking SD (or LD), PMODE=1.
// c10 = observation pointer (8 words per case), c12 = data word capability.
.option norelax
.option norvc
.section .text
.globl cheri_atest

.macro ADDRESS reg, symbol
    lui \reg, %hi(\symbol)
    addi \reg, \reg, %lo(\symbol)
.endm

// obs: 0 rd, 4 unused, 8 memory, 12 trapped, 16 mcause, 20 mtval,
//      24 mstatus in handler, 28 unused
// op: 0 = amoswap.w x7, x6, (c14); 1 = amoadd.w x7, x6, (c14);
//     2 = csw x6, 0(c14)
// c14 = c12 restricted to permission mask; c13 = resume address for handler.
.macro CASE mask, op, lbl
    li t0, 0x11223344
    csw t0, 0(c12)
    csw zero, 12(c10)
    csw zero, 16(c10)
    csw zero, 20(c10)
    csw zero, 24(c10)
    li t0, \mask
    candperm c14, c12, t0
    li t1, 0xaabbccdd
    li t2, 0xdeadbeef
    auipcc c13, 0
    ADDRESS t0, \lbl
    csetaddr c13, c13, t0
    csrsi mstatus, 8
.if \op == 0
    .word ((1 << 27) | (6 << 20) | (14 << 15) | (2 << 12) | (7 << 7) | 0x2f)
.elseif \op == 1
    .word ((0 << 27) | (6 << 20) | (14 << 15) | (2 << 12) | (7 << 7) | 0x2f)
.else
    csw t1, 0(c14)
.endif
\lbl:
    csw t2, 0(c10)
    clw t0, 0(c12)
    csw t0, 8(c10)
    cincoffset c10, c10, 32
.endm

.balign 16
trap_handler:
    csrr t0, mcause
    csw t0, 16(c10)
    csrr t0, mtval
    csw t0, 20(c10)
    csrr t0, mstatus
    csw t0, 24(c10)
    li t0, 1
    csw t0, 12(c10)
    cspecialw mepcc, c13
    mret

cheri_atest:
    cincoffset csp, csp, -24
    csc cra, 0(csp)
    csc c8, 8(csp)
    cspecialr c8, mtcc
    csc c8, 16(csp)
    cmove c12, ca1
    auipcc c8, 0
    ADDRESS t0, trap_handler
    csetaddr c8, c8, t0
    cspecialw mtcc, c8

    CASE 0x21, 0, after_c0      // amoswap, LD only (GL|LD)
    CASE 0x21, 1, after_c1      // amoadd,  LD only
    CASE 0x05, 0, after_c2      // amoswap, SD only (GL|SD)
    CASE 0x25, 0, after_c3      // amoswap, LD+SD
    CASE 0x21, 2, after_c4      // csw,     LD only

    clc c8, 16(csp)
    cspecialw mtcc, c8
    clc cra, 0(csp)
    clc c8, 8(csp)
    cincoffset csp, csp, 24
    cret
