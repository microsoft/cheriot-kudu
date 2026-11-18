// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// U-mode privilege checks (KUDU-034, KUDU-038).
// Phase 0 (A): MRET executed in U-mode must raise illegal instruction.
// Phase 1 (B): WFI executed in U-mode with mstatus.TW = 1 must raise illegal
//              instruction. MEIP is pending (MIE = 0) so a WFI that sleeps
//              wakes up at once instead of hanging.
// Phase 2 (C): with mstatus.MIE = 0, MEIE = 1 and MEIP pending, an M-mode
//              interrupt must be taken while the hart runs in U-mode.
// Phase 3 (D): control, WFI in M-mode with TW = 1 does not trap.
// U-mode code returns to M-mode with ECALL; the handler then resumes at
// m_resume. The handler counts traps per phase and records the first
// exception and the first interrupt of each phase. U-mode code uses t0-t2
// only; the handler uses s6-s9 only.

.option norvc
.option norelax

.equ TB_BASE, 0x83800000
.equ MSTATUS_TW, 0x200000

.section .data
.balign 4
.globl up_vars
.globl up_irqs
.globl up_nexc
.globl up_exc_cause
.globl up_exc_epc
.globl up_irq_epc
.globl up_irq_ok
.globl up_ucnt
.globl up_ccnt
.globl up_dwoke
up_vars:
up_phase:     .word 0
m_resume:     .word 0
up_ucnt:      .word 0
up_ccnt:      .word 0
up_dwoke:     .word 0
up_irqs:      .word 0, 0, 0, 0
up_nexc:      .word 0, 0, 0, 0
up_exc_cause: .word 0, 0, 0, 0
up_exc_epc:   .word 0, 0, 0, 0
up_irq_epc:   .word 0, 0, 0, 0
up_irq_ok:    .word 0, 0, 0, 0
up_vars_end:

.section .text
.globl rv32_atest
.globl uA_mret
.globl uB_wfi
.globl uC_start
.globl uC_end

// Enter U-mode at \label with MPIE = 0 (so U-mode runs with MIE = 0).
.macro ENTER_U resume, label
    la t0, \resume
    sw t0, m_resume, t1
    li t0, 0x1880            // MPP = U, MPIE = 0
    csrc mstatus, t0
    la t0, \label
    csrw mepc, t0
    mret
.endm

.macro SET_PHASE n
    csrci mstatus, 8         // MIE = 0
    li t0, \n
    sw t0, up_phase, t1
.endm

rv32_atest:
    addi sp, sp, -48
    sw ra, 0(sp)
    sw s0, 4(sp)
    sw s1, 8(sp)
    sw s2, 12(sp)
    sw s6, 16(sp)
    sw s7, 20(sp)
    sw s8, 24(sp)
    sw s9, 28(sp)
    csrrci s0, mstatus, 8
    csrr s1, mtvec
    csrrw s2, mie, zero
    la t0, trap_handler
    csrw mtvec, t0
    la t0, up_vars
    la t1, up_vars_end
1:  sw zero, 0(t0)
    addi t0, t0, 4
    bltu t0, t1, 1b

    SET_PHASE 0
    ENTER_U mA, uA
mA:
    SET_PHASE 1
    jal ra, irq_on
    beqz a0, mB              // no interrupt source: skip, WFI would hang
    li t0, MSTATUS_TW
    csrs mstatus, t0
    ENTER_U mB, uB
mB:
    li t0, MSTATUS_TW
    csrc mstatus, t0

    SET_PHASE 2
    jal ra, irq_on
    ENTER_U mC, uC_start
mC:
    SET_PHASE 3
    jal ra, irq_on
    beqz a0, 4f
    li t0, MSTATUS_TW
    csrs mstatus, t0
    wfi                      // MEIP pending: no sleep, no trap in M-mode
    li t0, 1
    sw t0, up_dwoke, t1
4:  li t0, MSTATUS_TW
    csrc mstatus, t0

    // Silence the interrupt generator before restoring MIE.
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
    lw ra, 0(sp)
    lw s0, 4(sp)
    lw s1, 8(sp)
    lw s2, 12(sp)
    lw s6, 16(sp)
    lw s7, 20(sp)
    lw s8, 24(sp)
    lw s9, 28(sp)
    addi sp, sp, 48
    ret

// Enable the TB external interrupt generator (needs +INTR_RATE) and MEIE,
// then wait (bounded) until MEIP is pending. On success up_irq_ok[phase] = 1
// and a0 = 1, otherwise a0 = 0.
irq_on:
    li a0, 0
    li t0, TB_BASE
    li t1, 0x3fffe
    sw t1, 0x108(t0)         // unmask the TB external interrupt (intr_mask)
    li t0, 0x800
    csrs mie, t0
    li t2, 20000
1:  csrr t0, mip
    srli t0, t0, 11
    andi t0, t0, 1
    bnez t0, 2f
    addi t2, t2, -1
    bnez t2, 1b
    ret
2:  lw t0, up_phase
    slli t0, t0, 2
    la t1, up_irq_ok
    add t1, t1, t0
    li a0, 1
    sw a0, 0(t1)
    ret

// ---------------- U-mode code ----------------
// A: the first pass executes MRET. If MRET is not illegal it jumps back to
// uA (mepc) in U-mode; the second pass skips it.
uA:
    la t0, up_ucnt
    lw t1, 0(t0)
    addi t1, t1, 1
    sw t1, 0(t0)
    li t2, 2
    bge t1, t2, 1f
uA_mret:
    mret
1:  ecall

uB:
    nop
uB_wfi:
    wfi
    ecall

uC_start:
    li t0, 3000
    la t2, up_ccnt
1:  lw t1, 0(t2)
    addi t1, t1, 1
    sw t1, 0(t2)
    addi t0, t0, -1
    bnez t0, 1b
    ecall
uC_end:

// ---------------- M-mode trap handler ----------------
.balign 64
trap_handler:
    lw s6, up_phase
    slli s6, s6, 2
    csrr s7, mcause
    bltz s7, h_irq
    li s8, 8                 // ECALL from U-mode: back to M-mode
    beq s7, s8, h_ecall
    la s8, up_nexc
    add s8, s8, s6
    lw s9, 0(s8)
    addi s9, s9, 1
    sw s9, 0(s8)
    li s8, 1
    bne s9, s8, 1f
    la s8, up_exc_cause
    add s8, s8, s6
    sw s7, 0(s8)
    la s8, up_exc_epc
    add s8, s8, s6
    csrr s9, mepc
    sw s9, 0(s8)
1:  csrr s9, mepc
    addi s9, s9, 4
    csrw mepc, s9
    mret
h_ecall:
    li s9, 0x1800            // MPP = M
    csrs mstatus, s9
    lw s9, m_resume
    csrw mepc, s9
    mret
h_irq:
    la s8, up_irqs
    add s8, s8, s6
    lw s9, 0(s8)
    addi s9, s9, 1
    sw s9, 0(s8)
    li s8, 1
    bne s9, s8, 1f
    la s8, up_irq_epc
    add s8, s8, s6
    csrr s9, mepc
    sw s9, 0(s8)
1:  li s9, TB_BASE
    li s8, 1
    sw s8, 0x104(s9)         // acknowledge; the generator stays enabled
    mret
