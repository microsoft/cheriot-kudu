// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// KUDU-033: a load of the second word written by a misaligned store or a CSC,
// issued right behind the store, must not see the stale dcache line.
// c10 = observation pointer (load, load + 1, reload), c11 = 3-word buffer.
.option norvc
.option norelax
.section .text
.globl cheri_atest

// op: 0 = csw at +2, 1 = csh at +3, 2 = csw at +4 (aligned control),
//     3 = csc cnull at +0 (clears words 0 and 1)
.macro CASE op, gap
    li t1, 0x11111111
    csw zero, 0(c11)
    csw t1, 4(c11)
    csw zero, 8(c11)
    nop
    nop
    nop
    nop
    clw t2, 4(c11)              // warm the dcache line holding c11+4
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    li t1, 0xaabbccdd
.if \op == 0
    csw t1, 2(c11)
.elseif \op == 1
    csh t1, 3(c11)
.elseif \op == 2
    csw t1, 4(c11)
.else
    csc cnull, 0(c11)
.endif
    .rept \gap
    nop
    .endr
    clw t2, 4(c11)
    addi t0, t2, 1
    csw t2, 0(c10)
    csw t0, 4(c10)
    nop
    nop
    nop
    nop
    clw t2, 4(c11)
    csw t2, 8(c10)
    cincoffset c10, c10, 16
.endm

// Every op is tried with gaps 0..3 between the store and the load, three
// times each (12 observations), so the window is hit even when wait states
// shift the store response.
.macro SWEEP op
    .rept 3
    .irp gap, 0, 1, 2, 3
    CASE \op, \gap
    .endr
    .endr
.endm

cheri_atest:
    SWEEP 0
    SWEEP 1
    SWEEP 2
    SWEEP 3
    cret
