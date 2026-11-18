// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.option norvc
.option norelax
.section .text
.globl rv32_atest

// Record the initial write, the RMW old value, and the resulting CSR value.
.macro RECORD csr, operation, initial, operand, immediate=0
    li t1, \initial
    csrw \csr, t1
    csrr t2, \csr
    sw t2, 0(a0)
    .if \immediate
        \operation t0, \csr, \operand
    .else
        li t1, \operand
        \operation t0, \csr, t1
    .endif
    sw t0, 4(a0)
    csrr t0, \csr
    sw t0, 8(a0)
    addi a0, a0, 12
.endm

.macro MATRIX csr
    RECORD \csr, csrrw,  0x80000100, 0x80000300
    RECORD \csr, csrrs,  0x80000100, 0x00000200
    RECORD \csr, csrrc,  0x80000300, 0x00000200
    // t1 is a nonzero register index even when its value is zero.
    RECORD \csr, csrrs,  0x80000100, 0
    RECORD \csr, csrrc,  0x80000100, 0
    RECORD \csr, csrrsi, 0x80000100, 8, 1
    RECORD \csr, csrrci, 0x80000108, 8, 1
    RECORD \csr, csrrsi, 0x80000100, 0, 1
    RECORD \csr, csrrci, 0x80000100, 0, 1
.endm

rv32_atest:
    addi sp, sp, -32
    sw s0, 0(sp)
    sw s1, 4(sp)
    sw s2, 8(sp)
    sw s3, 12(sp)
    sw s4, 16(sp)
    csrrci s3, mstatus, 8
    csrrw s4, mie, zero
    csrr s0, mscratch
    csrr s1, mtvec
    csrr s2, mepc

    MATRIX mscratch
    MATRIX mtvec
    MATRIX mepc

    csrw mtvec, s1
    csrw mepc, s2
    csrw mscratch, s0
    csrw mie, s4
    csrw mstatus, s3
    lw s0, 0(sp)
    lw s1, 4(sp)
    lw s2, 8(sp)
    lw s3, 12(sp)
    lw s4, 16(sp)
    addi sp, sp, 32
    ret
