// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// KUDU-039: an interrupt taken right after a JALR to an odd target must not
// leave mepc[0] = 1 (JALR clears bit 0 of the target; mepc[0] is always 0).
// jo_loop runs 4000 JALRs to (jo_tgt + 1) with the TB external interrupt
// generator enabled (+INTR_RATE). The handler counts interrupts and the
// ones whose mepc is odd, records the first odd mepc, clears bit 0 and
// returns. jo_csrw checks the csrw mepc legalization (control).

.option norvc
.option norelax

.equ TB_BASE, 0x83800000

.section .data
.balign 4
.globl jo_irqs
.globl jo_odd
.globl jo_first_odd
jo_irqs:      .word 0
jo_odd:       .word 0
jo_first_odd: .word 0

.section .text
.globl jo_loop
.globl jo_tgt
.globl jo_csrw

// unsigned jo_loop(void): returns the number of loop iterations executed.
jo_loop:
    addi sp, sp, -32
    sw s0, 0(sp)
    sw s1, 4(sp)
    sw s2, 8(sp)
    sw s8, 12(sp)
    sw s9, 16(sp)
    sw zero, jo_irqs, t0
    sw zero, jo_odd, t0
    sw zero, jo_first_odd, t0
    csrrci s0, mstatus, 8
    csrr s1, mtvec
    csrrw s2, mie, zero
    la t0, trap_handler
    csrw mtvec, t0
    li t0, TB_BASE
    li t1, 0x3fffe
    sw t1, 0x108(t0)         // unmask the TB external interrupt (intr_mask)
    li t0, 0x800
    csrs mie, t0             // MEIE
    csrsi mstatus, 8         // MIE

    li t1, 4000
    li a0, 0
1:  la t0, jo_tgt
    addi t0, t0, 1           // odd target
    jalr x0, 0(t0)
    nop                      // skipped
    nop
jo_tgt:
    addi a0, a0, 1
    addi t1, t1, -1
    bnez t1, 1b

    csrci mstatus, 8
    li t0, TB_BASE
    li t1, 0x3ffff
    sw t1, 0x108(t0)         // mask all TB interrupts
    li t1, 7
    sw t1, 0x104(t0)
    li t0, 0x800
    csrc mie, t0
    li t2, 1000
2:  csrr t0, mip
    srli t0, t0, 11
    andi t0, t0, 1
    beqz t0, 3f
    addi t2, t2, -1
    bnez t2, 2b
3:  csrw mie, s2
    csrw mtvec, s1
    csrw mstatus, s0
    lw s0, 0(sp)
    lw s1, 4(sp)
    lw s2, 8(sp)
    lw s8, 12(sp)
    lw s9, 16(sp)
    addi sp, sp, 32
    ret

// unsigned jo_csrw(unsigned v): csrw mepc, v; returns csrr mepc.
jo_csrw:
    csrr t0, mepc
    csrw mepc, a0
    csrr a0, mepc
    csrw mepc, t0
    ret

.balign 64
trap_handler:
    lw s9, jo_irqs
    addi s9, s9, 1
    sw s9, jo_irqs, s8
    csrr s9, mepc
    andi s8, s9, 1
    beqz s8, 1f
    lw s8, jo_odd
    bnez s8, 2f
    sw s9, jo_first_odd, s8
2:  lw s8, jo_odd
    addi s8, s8, 1
    sw s8, jo_odd, s9
    csrr s9, mepc
    andi s9, s9, -2
    csrw mepc, s9
1:  li s9, TB_BASE
    li s8, 1
    sw s8, 0x104(s9)         // acknowledge
    mret
