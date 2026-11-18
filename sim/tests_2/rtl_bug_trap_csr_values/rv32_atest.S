// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.option norvc
.option norelax
.section .text
.globl rv32_atest
.globl dret_site
.globl ecall_site

// a0 points at six 32-bit observation words:
//   dret mcause, mtval, mepc; ecall mcause, mtval, mepc.
rv32_atest:
    addi sp, sp, -32
    sw ra, 0(sp)
    sw s0, 4(sp)
    sw s1, 8(sp)
    sw s2, 12(sp)
    sw s3, 16(sp)

    mv s0, a0
    la t0, result_ptr
    sw s0, 0(t0)

    csrrci s1, mstatus, 8
    csrrw s2, mtvec, zero
    csrrw s3, mscratch, zero

    la t0, trap_handler
    csrw mtvec, t0

    li t0, 1
    csrw mscratch, t0
dret_site:
    .word 0x7b200073

    li t0, 2
    csrw mscratch, t0
ecall_site:
    ecall

    csrw mscratch, s3
    csrw mtvec, s2
    csrw mstatus, s1
    lw ra, 0(sp)
    lw s0, 4(sp)
    lw s1, 8(sp)
    lw s2, 12(sp)
    lw s3, 16(sp)
    addi sp, sp, 32
    ret

.align 2
trap_handler:
    csrr t0, mscratch
    csrr t1, mcause
    csrr t2, mtval
    csrr t3, mepc
    la t4, result_ptr
    lw t4, 0(t4)
    li t5, 1
    beq t0, t5, 1f
    li t5, 2
    beq t0, t5, 2f
    j 3f
1:
    sw t1, 0(t4)
    sw t2, 4(t4)
    sw t3, 8(t4)
    j 3f
2:
    sw t1, 12(t4)
    sw t2, 16(t4)
    sw t3, 20(t4)
3:
    addi t3, t3, 4
    csrw mepc, t3
    mret

.section .bss
.align 2
result_ptr:
    .word 0
