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
    mv s0, a0
    li t6, 0

    // Disable the branch predictor through CPUCTRL, keep dcache_en set, and
    // execute FENCE.I so the following jumps are fetched with pdt_en=0.
    csrr t0, 0x7c0
    sw t0, 0(s0)
    li t1, 0x08
    csrw 0x7c0, t1
    csrr t2, 0x7c0
    sw t2, 4(s0)
    .word 0x0000100f  // fence.i (assembler march omits zifencei)

    li t3, 0x11111111
    jal x0, jal_target
    li t3, 0xdead0001
    ori t6, t6, 1
jal_target:
    sw t3, 8(s0)

    li t4, 0x22222222
    la t0, jalr_target
    jalr x0, 0(t0)
    li t4, 0xdead0002
    ori t6, t6, 2
jalr_target:
    sw t4, 12(s0)

    lw t0, 0(s0)
    csrw 0x7c0, t0

    mv a0, t6
    lw ra, 0(sp)
    lw s0, 4(sp)
    addi sp, sp, 16
    ret
