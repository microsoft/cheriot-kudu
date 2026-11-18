// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// KUDU-031: misaligned LR/SC/AMO must trap before reaching the data bus.
// The trap handler only touches t3-t6 and never stores, so it does not
// disturb the testbench reservation (cleared by any store).
.option norvc
.option norelax

// rd, w0, w1, trapped, mcause, mtval (8 words per case)
.equ OBS_SIZE, 32

.macro AMO_WORD funct5, rd, rs1, rs2
    .word ((\funct5 << 27) | (\rs2 << 20) | (\rs1 << 15) | (2 << 12) | (\rd << 7) | 0x2f)
.endm

.section .data
.balign 16
.globl sc_words
sc_words: .word 0, 0, 0, 0

.section .text
.globl rv32_atest

// Initialise memory (the stores also clear any reservation) and trap regs.
.macro CASE_INIT
    la t0, sc_words
    li t1, 0x11223344
    sw t1, 0(t0)
    li t1, 0x55667788
    sw t1, 4(t0)
    li t1, 0xaabbccdd
    li t2, 0xdeadbeef
    li t3, 0
    li t4, 0
    li t5, 0
.endm

.macro CASE_SAVE
    sw t2, 0(a0)
    lw t1, 0(t0)
    sw t1, 4(a0)
    lw t1, 4(t0)
    sw t1, 8(a0)
    sw t3, 12(a0)
    sw t4, 16(a0)
    sw t5, 20(a0)
    addi a0, a0, OBS_SIZE
.endm

// aligned lr.w (reservation held), then misaligned sc.w at +off
.macro CASE_LR_SC off
    CASE_INIT
    addi a1, t0, \off
    AMO_WORD 2, 12, 5, 0        // lr.w  a2, (t0)
    AMO_WORD 3, 7, 11, 6        // sc.w  t2, t1, (a1)
    CASE_SAVE
.endm

// misaligned lr.w at +off (must trap and not reserve), then aligned sc.w
.macro CASE_MLR_SC off
    CASE_INIT
    addi a1, t0, \off
    AMO_WORD 2, 12, 11, 0       // lr.w  a2, (a1)   -> traps
    mv a3, t3
    mv a4, t4
    mv a5, t5
    li t2, 0xdeadbeef
    AMO_WORD 3, 7, 5, 6         // sc.w  t2, t1, (t0) -> must fail (rd=1)
    mv t3, a3
    mv t4, a4
    mv t5, a5
    CASE_SAVE
.endm

// misaligned amoswap.w at +off
.macro CASE_AMO off
    CASE_INIT
    addi a1, t0, \off
    AMO_WORD 1, 7, 11, 6        // amoswap.w t2, t1, (a1)
    CASE_SAVE
.endm

// misaligned lr.w at +off: rd unchanged
.macro CASE_LR off
    CASE_INIT
    addi a1, t0, \off
    AMO_WORD 2, 7, 11, 0        // lr.w t2, (a1)
    CASE_SAVE
.endm

// aligned lr.w / sc.w: succeeds
.macro CASE_ALIGNED
    CASE_INIT
    AMO_WORD 2, 12, 5, 0        // lr.w  a2, (t0)
    AMO_WORD 3, 7, 5, 6         // sc.w  t2, t1, (t0)
    CASE_SAVE
.endm

rv32_atest:
    addi sp, sp, -32
    sw ra, 0(sp)
    sw s1, 4(sp)
    sw s2, 8(sp)
    sw s3, 12(sp)
    sw s4, 16(sp)
    sw s5, 20(sp)
    csrrci s4, mstatus, 8
    csrrw s5, mie, zero
    csrr s1, mtvec
    csrr s2, mepc
    csrr s3, mcause
    la t0, trap_handler
    csrw mtvec, t0

    CASE_LR_SC 1        // 0 KUDU-031
    CASE_LR_SC 2        // 1 KUDU-031
    CASE_LR_SC 3        // 2 KUDU-031
    CASE_MLR_SC 2       // 3 KUDU-031
    CASE_AMO 2          // 4 control
    CASE_LR 2           // 5 control
    CASE_ALIGNED        // 6 control

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
    addi sp, sp, 32
    ret

.balign 4
trap_handler:
    li t3, 1
    csrr t4, mcause
    csrr t5, mtval
    csrr t6, mepc
    addi t6, t6, 4
    csrw mepc, t6
    mret
