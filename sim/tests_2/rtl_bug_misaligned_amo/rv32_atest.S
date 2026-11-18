// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.option norvc
.option norelax

.equ OBS_RD,      0
.equ OBS_WORD0,   4
.equ OBS_WORD1,   8
.equ OBS_TRAPPED, 12
.equ OBS_MCAUSE,  16
.equ OBS_MTVAL,   20
.equ OBS_MEPC,    24
.equ OBS_SIZE,    28

// AMO instruction encoder: funct5, rd, rs1, rs2.
.macro AMO_WORD funct5, rd, rs1, rs2
    .word ((\funct5 << 27) | (\rs2 << 20) | (\rs1 << 15) | (2 << 12) | (\rd << 7) | 0x2f)
.endm

.section .bss
.balign 4
current_obs:
    .word 0

.section .data
.balign 8
amo_words:
    .word 0
    .word 0

.section .text
.globl rv32_atest

.macro INIT_CASE
    li t0, 0x11223344
    sw t0, amo_words, t6
    li t0, 0x55667788
    sw t0, amo_words+4, t6
    sw zero, OBS_TRAPPED(a0)
    sw zero, OBS_MCAUSE(a0)
    sw zero, OBS_MTVAL(a0)
    sw zero, OBS_MEPC(a0)
    la t0, current_obs
    sw a0, 0(t0)
    la t0, amo_words
    addi t0, t0, 1
    li t1, 0xaabbccdd
    li t2, 0xdeadbeef
.endm

.macro FINISH_CASE
    sw t2, OBS_RD(a0)
    lw t3, amo_words
    sw t3, OBS_WORD0(a0)
    lw t3, amo_words+4
    sw t3, OBS_WORD1(a0)
    addi a0, a0, OBS_SIZE
.endm

rv32_atest:
    addi sp, sp, -48
    sw ra, 0(sp)
    sw s0, 4(sp)
    sw s1, 8(sp)
    sw s2, 12(sp)
    sw s3, 16(sp)
    sw s4, 20(sp)
    sw s5, 24(sp)

    csrrci s4, mstatus, 8
    csrrw s5, mie, zero
    csrr s1, mtvec
    csrr s2, mepc
    csrr s3, mcause
    la t0, trap_handler
    csrw mtvec, t0

    // Case 0: misaligned AMOSWAP.W. Expected: store/AMO misaligned or access-fault trap.
    INIT_CASE
    AMO_WORD 1, 7, 5, 6       // amoswap.w t2, t1, (t0)
    FINISH_CASE

    // Case 1: misaligned SC.W. Expected: store/AMO misaligned or access-fault trap.
    INIT_CASE
    AMO_WORD 3, 7, 5, 6       // sc.w t2, t1, (t0)
    FINISH_CASE

    csrw mtvec, s1
    csrw mepc, s2
    csrw mcause, s3
    csrw mie, s5
    csrw mstatus, s4
    lw ra, 0(sp)
    lw s0, 4(sp)
    lw s1, 8(sp)
    lw s2, 12(sp)
    lw s3, 16(sp)
    lw s4, 20(sp)
    lw s5, 24(sp)
    addi sp, sp, 48
    ret

trap_handler:
    la t4, current_obs
    lw t4, 0(t4)
    li t3, 1
    sw t3, OBS_TRAPPED(t4)
    csrr t3, mcause
    sw t3, OBS_MCAUSE(t4)
    csrr t3, mtval
    sw t3, OBS_MTVAL(t4)
    csrr t3, mepc
    sw t3, OBS_MEPC(t4)
    addi t3, t3, 4
    csrw mepc, t3
    mret
