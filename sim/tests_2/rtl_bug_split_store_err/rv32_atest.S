// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Split stores/loads where exactly one half hits an unmapped address.
// Records mcause/mtval/rd and the memory word of the mapped half.
.option norelax
.option norvc
.section .text
.globl sw_test
.balign 64
sw_h:
    csrr t5, mcause
    sw t5, 0(a1)
    csrr t5, mtval
    sw t5, 4(a1)
    csrr t5, mepc
    addi t5, t5, 4
    csrw mepc, t5
    mret

// first-half fault: mapped word 0x80000000 (vector code, saved/restored)
.macro ST1 op, off, val
    sw x0, 0(a1)
    sw x0, 4(a1)
    li t2, 0x80000000
    sw x0, 0(t2)
    li t0, 0x7ffffff0
    li t1, \val
    \op t1, \off(t0)
    lw t3, 0(t2)
    sw t3, 8(a1)
    addi a1, a1, 12
.endm
// second-half fault: mapped word 0x8007fffc
.macro ST2 op, off, val
    sw x0, 0(a1)
    sw x0, 4(a1)
    li t2, 0x8007fffc
    sw x0, 0(t2)
    li t0, 0x8007fff0
    li t1, \val
    \op t1, \off(t0)
    lw t3, 0(t2)
    sw t3, 8(a1)
    addi a1, a1, 12
.endm
.macro LD1 op, off
    sw x0, 0(a1)
    sw x0, 4(a1)
    li t0, 0x7ffffff0
    li t1, 0xdeadbeef
    \op t1, \off(t0)
    sw t1, 8(a1)
    addi a1, a1, 12
.endm
.macro R8 m, op, off, val
  .rept 8
    \m \op, \off, \val
  .endr
.endm

sw_test:
    csrr t6, mtvec
    la t5, sw_h
    csrw mtvec, t5
    li t2, 0x80000000
    lw a2, 0(t2)
    mv a1, a0
    R8 ST1, sw, 13, 0x11223344
    R8 ST1, sw, 14, 0x11223344
    R8 ST1, sw, 15, 0x11223344
    R8 ST1, sh, 15, 0x11223344
    R8 ST2, sw, 13, 0x11223344
    R8 ST2, sw, 14, 0x11223344
    R8 ST2, sw, 15, 0x11223344
    R8 ST2, sh, 15, 0x11223344
    R8 LD1, lw, 13
    R8 LD1, lw, 14
    R8 LD1, lw, 15
    R8 LD1, lhu, 15
    li t2, 0x80000000
    sw a2, 0(t2)
    .word 0x0000100f
    csrw mtvec, t6
    sub a0, a1, a0
    ret
