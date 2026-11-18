// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.option norvc
.option norelax

.equ OBS_RD,      0
.equ OBS_TRAPPED, 4
.equ OBS_MCAUSE,  8
.equ OBS_MTVAL,   12
.equ OBS_MEPC,    16

.macro AMO_WORD funct5, rd, rs1, rs2
    .word ((\funct5 << 27) | (\rs2 << 20) | (\rs1 << 15) | (2 << 12) | (\rd << 7) | 0x2f)
.endm

.section .bss
.balign 4
current_obs:
    .word 0

.section .text
.globl rv32_atest

rv32_atest:
    addi sp, sp, -48
    sw ra, 0(sp)
    sw s1, 4(sp)
    sw s2, 8(sp)
    sw s3, 12(sp)
    sw s4, 16(sp)
    sw s5, 20(sp)

    sw zero, OBS_TRAPPED(a0)
    sw zero, OBS_MCAUSE(a0)
    sw zero, OBS_MTVAL(a0)
    sw zero, OBS_MEPC(a0)
    la t0, current_obs
    sw a0, 0(t0)

    csrrci s4, mstatus, 8
    csrrw s5, mie, zero
    csrr s1, mtvec
    csrr s2, mepc
    csrr s3, mcause
    la t0, trap_handler
    csrw mtvec, t0

    li t0, 0x90000000       // unmapped in data_mem_model
    li t1, 0xaabbccdd
    li t2, 0xdeadbeef
    AMO_WORD 1, 7, 5, 6     // amoswap.w t2, t1, (t0)
    sw t2, OBS_RD(a0)

    csrw mtvec, s1
    csrw mepc, s2
    csrw mcause, s3
    csrw mie, s5
    csrw mstatus, s4
    lw ra, 0(sp)
    lw s1, 4(sp)
    lw s2, 8(sp)
    lw s3, 12(sp)
    lw s4, 16(sp)
    lw s5, 20(sp)
    addi sp, sp, 48
    ret

.balign 4
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
