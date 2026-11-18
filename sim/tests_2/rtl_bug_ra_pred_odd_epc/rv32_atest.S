// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// KUDU-075 (RV32 program): a return through an odd ra is predicted by the
// RA predictor with the odd ra as its target (ptarget bit 0 = 1). The branch
// unit compares ptarget with the raw ra, so the prediction is "correct" and
// the issuer keeps the odd ptarget as ir0_nxt_pc_q. An interrupt or debug
// request taken before the target reaches IR0 then saves it as mepc/dpc.
//
// void ro_run(unsigned *r, unsigned n): n iterations of `mv ra, <tgt+1>; ret`
// with the TB external interrupt enabled. r[] = {iterations, interrupts,
// interrupts with odd mepc, first odd mepc, synchronous exceptions}. The
// handler clears mepc[0] before mret. Uses s8/s9 in the handler only.

.option norvc
.option norelax

.equ TB_BASE, 0x83800000

.section .data
.balign 4
ro_irqs:      .word 0
ro_odd:       .word 0
ro_first_odd: .word 0
ro_exc:       .word 0

.section .text
.globl ro_run

ro_run:
    addi sp, sp, -32
    sw ra, 0(sp)
    sw s0, 4(sp)
    sw s1, 8(sp)
    sw s2, 12(sp)
    sw s8, 16(sp)
    sw s9, 20(sp)
    sw s3, 24(sp)
    mv s3, a0
    sw zero, ro_irqs, t0
    sw zero, ro_odd, t0
    sw zero, ro_first_odd, t0
    sw zero, ro_exc, t0
    csrrci s0, mstatus, 8
    csrr s1, mtvec
    csrrw s2, mie, zero
    la t0, ro_handler
    csrw mtvec, t0
    li t0, TB_BASE
    li t1, 0x3fffe
    sw t1, 0x108(t0)         // unmask the TB external interrupt (intr_mask)
    li t0, 0x800
    csrs mie, t0             // MEIE
    csrsi mstatus, 8         // MIE

    mv t1, a1
    li a0, 0
    la t2, ro_tgt
    addi t2, t2, 1           // odd return address
1:  mv ra, t2
    nop
    nop
    nop
    nop
    nop
    nop
    ret                      // jalr x0, 0(ra): predicted from cur_ra
    nop
    nop
.balign 8
ro_tgt:
    addi a0, a0, 1
    addi t1, t1, -1
    bnez t1, 1b

    csrci mstatus, 8
    li t0, TB_BASE
    li t1, 0x3ffff
    sw t1, 0x108(t0)         // mask all TB interrupts
    sw t1, 0x104(t0)         // and acknowledge them
    csrw mie, s2
    csrw mtvec, s1
    csrw mstatus, s0

    sw a0, 0(s3)
    lw t0, ro_irqs
    sw t0, 4(s3)
    lw t0, ro_odd
    sw t0, 8(s3)
    lw t0, ro_first_odd
    sw t0, 12(s3)
    lw t0, ro_exc
    sw t0, 16(s3)

    lw ra, 0(sp)
    lw s0, 4(sp)
    lw s1, 8(sp)
    lw s2, 12(sp)
    lw s8, 16(sp)
    lw s9, 20(sp)
    lw s3, 24(sp)
    addi sp, sp, 32
    ret

.balign 64
ro_handler:
    csrr s9, mcause
    bltz s9, 3f
    lw s9, ro_exc            // unexpected exception: count, skip the instruction
    addi s9, s9, 1
    sw s9, ro_exc, s8
    csrr s9, mepc
    addi s9, s9, 4
    csrw mepc, s9
    mret
3:  lw s9, ro_irqs
    addi s9, s9, 1
    sw s9, ro_irqs, s8
    csrr s9, mepc
    andi s8, s9, 1
    beqz s8, 1f
    lw s8, ro_odd
    bnez s8, 2f
    sw s9, ro_first_odd, s8
2:  lw s8, ro_odd
    addi s8, s8, 1
    sw s8, ro_odd, s9
    csrr s9, mepc
    andi s9, s9, -2
    csrw mepc, s9
1:  li s9, TB_BASE
    li s8, 1
    sw s8, 0x104(s9)         // acknowledge
    mret
