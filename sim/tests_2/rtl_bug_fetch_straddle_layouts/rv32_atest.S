// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// KUDU-013 harness.  test_main.c writes a code sequence into a RAM buffer;
// rv32_atest() jumps to it and records any trap.  The sequence always ends in
// a 64-bit word "addi a4,x0,0x44; addi a5,x0,0x55" followed by
// "jalr x0,0(s3)", which returns here.

.option norelax

.equ O_TRAPPED, 0
.equ O_MCAUSE,  4
.equ O_MEPC,    8
.equ O_MTVAL,   12
.equ O_A4,      16
.equ O_A3,      20

.section .data
.balign 4
cur_obs:
    .word 0

.section .text
.globl rv32_atest

// void rv32_atest(struct obs *r, unsigned entry)
rv32_atest:
    addi sp, sp, -32
    sw s0, 0(sp)
    sw s1, 4(sp)
    sw s2, 8(sp)
    sw s3, 12(sp)
    sw s4, 16(sp)
    sw ra, 20(sp)
    sw zero, O_TRAPPED(a0)
    sw zero, O_MCAUSE(a0)
    sw zero, O_MEPC(a0)
    sw zero, O_MTVAL(a0)
    sw zero, O_A4(a0)
    sw zero, O_A3(a0)
    la t0, cur_obs
    sw a0, 0(t0)
    mv s2, a0
    mv t5, a1
    .word 0x0000100f            // fence.i (march lacks zifencei)

    csrr s0, mtvec
    csrrci s1, mstatus, 8
    la t0, f_handler
    csrw mtvec, t0
    la s3, region_done
    li s4, 3
    li t6, 0x7fffffff
    li a2, 0
    li a3, 0
    li a6, 0
    li a4, 0xdead0004
    li a5, 0xdead0005
    jr t5                       // rs1 != ra: not predicted, fetch restarts at entry
region_done:
    sw a4, O_A4(s2)
    sw a3, O_A3(s2)
    csrw mtvec, s0
    csrw mstatus, s1
    lw s0, 0(sp)
    lw s1, 4(sp)
    lw s2, 8(sp)
    lw s3, 12(sp)
    lw s4, 16(sp)
    lw ra, 20(sp)
    addi sp, sp, 32
    ret

.balign 4
f_handler:
    la t4, cur_obs
    lw t4, 0(t4)
    lw t3, O_TRAPPED(t4)
    addi t3, t3, 1
    sw t3, O_TRAPPED(t4)
    csrr t3, mcause
    sw t3, O_MCAUSE(t4)
    csrr t3, mepc
    sw t3, O_MEPC(t4)
    csrr t3, mtval
    sw t3, O_MTVAL(t4)
    csrw mepc, s3
    mret
