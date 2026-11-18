// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Misaligned accesses straddling the end of DRAM (0x80080000 is unmapped and
// returns a data bus error). Records mcause/mtval/rd per access.
.option norelax
.option norvc
.section .text
.globl smt_test
.balign 64
smt_h:
    csrr t5, mcause
    sw t5, 0(a1)
    csrr t5, mtval
    sw t5, 4(a1)
    csrr t5, mepc
    addi t5, t5, 4
    csrw mepc, t5
    mret

.macro OP op, off, val
    sw x0, 0(a1)
    sw x0, 4(a1)
    li t0, 0x8007fff0
    li t1, \val
    \op t1, \off(t0)
    sw t1, 8(a1)
    addi a1, a1, 12
.endm

.macro REP16 op, off, val
  .rept 16
    OP \op, \off, \val
  .endr
.endm

smt_test:
    csrr t6, mtvec
    la t5, smt_h
    csrw mtvec, t5
    mv a1, a0
    REP16 lw,  13, 0xdeadbeef
    REP16 lw,  14, 0xdeadbeef
    REP16 lw,  15, 0xdeadbeef
    REP16 lh,  15, 0xdeadbeef
    REP16 lhu, 15, 0xdeadbeef
    REP16 sw,  13, 0x11223344
    REP16 sw,  14, 0x11223344
    REP16 sw,  15, 0x11223344
    REP16 sh,  15, 0x11223344
    csrw mtvec, t6
    sub a0, a1, a0
    ret
