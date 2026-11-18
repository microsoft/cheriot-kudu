// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// KUDU-033: a load of the second word written by a misaligned store, issued
// right behind the store, must not see the stale dcache line.
// a0 = observation pointer (load, load + 1, reload), a1 = 3-word buffer.
.option norvc
.option norelax
.section .text
.globl rv32_atest

// op: 0 = sw at +2, 1 = sh at +3, 2 = sw at +4 (aligned control)
.macro CASE op, gap
    li t1, 0x11111111
    sw zero, 0(a1)
    sw t1, 4(a1)
    sw zero, 8(a1)
    nop
    nop
    nop
    nop
    lw t2, 4(a1)                // warm the dcache line holding a1+4
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
    sw t1, 2(a1)
.elseif \op == 1
    sh t1, 3(a1)
.else
    sw t1, 4(a1)
.endif
    .rept \gap
    nop
    .endr
    lw t2, 4(a1)
    addi t3, t2, 1
    sw t2, 0(a0)
    sw t3, 4(a0)
    nop
    nop
    nop
    nop
    lw t2, 4(a1)
    sw t2, 8(a0)
    addi a0, a0, 16
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

rv32_atest:
    SWEEP 0
    SWEEP 1
    SWEEP 2
    ret
