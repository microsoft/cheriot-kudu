// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.option norvc
.option norelax
.section .data
.balign 8
sc_word:
    .word 0
.section .text
.globl rv32_atest

.macro CASE gap
    la t0, sc_word
    li t1, 0x11223344
    sw t1, 0(t0)
    li t1, 0xaabbccdd
    .word ((3 << 27) | (6 << 20) | (5 << 15) | (2 << 12) | (7 << 7) | 0x2f)
    .rept \gap
    nop
    .endr
    lw t3, 0(t0)
    addi t4, t3, 1
    sw t2, 0(a0)
    sw t3, 4(a0)
    sw t4, 8(a0)
    lw t5, 0(t0)
    sw t5, 12(a0)
    addi a0, a0, 16
.endm

rv32_atest:
    CASE 0
    CASE 16
    ret
