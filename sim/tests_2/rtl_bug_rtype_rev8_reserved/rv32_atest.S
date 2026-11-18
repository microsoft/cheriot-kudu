// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.option norvc
.option norelax
.section .text
.globl rv32_atest

rv32_atest:
    addi sp, sp, -16
    sw ra, 0(sp)
    sw s0, 4(sp)
    sw s1, 8(sp)
    mv s0, a0

    csrr s1, mtvec
    la t0, rtype_rev8_trap_handler
    csrw mtvec, t0

    sw zero, 0(s0)
    sw zero, 4(s0)
    li t1, 0xa5a5a5a5
    sw t1, 8(s0)
    sw zero, 12(s0)

    li t0, 0x11223344
    // Reserved in ratified RV32 Zba/Zbb/Zbc/Zbs: opcode OP, funct7=0110100,
    // rs2=11000, funct3=101. Kudu currently decodes it as rev8.
    .word 0x6982d333
    sw t1, 8(s0)

    li t0, 0x13579bdf
    sw t0, 12(s0)

    csrw mtvec, s1
    lw ra, 0(sp)
    lw s0, 4(sp)
    lw s1, 8(sp)
    addi sp, sp, 16
    ret

.align 2
rtype_rev8_trap_handler:
    csrr t2, mcause
    lw t3, 0(s0)
    addi t3, t3, 1
    sw t3, 0(s0)
    sw t2, 4(s0)
    csrr t4, mepc
    addi t4, t4, 4
    csrw mepc, t4
    mret
