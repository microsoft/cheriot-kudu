// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.option norvc
.option norelax
.section .text
.globl rv32_atest

#include "../isa_test_csr/csr_patterns.inc"

// Check old values as well as readback, restoring each tested register.
.macro RW_BITS csr, bits
    csrr t4, \csr
    csrrw t0, \csr, zero
    bne t0, t4, fail
    csrr t0, \csr
    bnez t0, fail
    li t1, \bits
    csrrs t0, \csr, t1
    bnez t0, fail
    csrr t0, \csr
    bne t0, t1, fail
    csrrc t0, \csr, t1
    bne t0, t1, fail
    csrr t0, \csr
    bnez t0, fail
    csrw \csr, t4
.endm

// These registers are readable but their writes are ignored in M-mode.
.macro IGNORED_WRITES csr
    csrr t4, \csr
    li t1, -1
    csrrw t0, \csr, t1
    bne t0, t4, fail
    csrr t0, \csr
    bne t0, t4, fail
    csrrs t0, \csr, t1
    bne t0, t4, fail
    csrr t0, \csr
    bne t0, t4, fail
    csrrc t0, \csr, t1
    bne t0, t4, fail
    csrr t0, \csr
    bne t0, t4, fail
    csrrsi t0, \csr, 1
    bne t0, t4, fail
    csrrci t0, \csr, 1
    bne t0, t4, fail
.endm

.macro ID_READ csr
    csrr t4, \csr
    csrrs t0, \csr, zero
    bne t0, t4, fail
    csrrc t0, \csr, zero
    bne t0, t4, fail
    csrrsi t0, \csr, 0
    bne t0, t4, fail
    csrrci t0, \csr, 0
    bne t0, t4, fail
.endm

// All faulting instructions are explicitly 32-bit; the handler checks their PC.
.macro EXPECT cause, privilege=0x1800, return_m=0, mpie=0
    la s8, 991f
    li s9, \cause
    li s10, \privilege
    li s11, \return_m
    li a2, \mpie
    addi a5, a5, 1
991:
.endm

.macro RESUMED
    bnez s8, fail
    bne s7, a5, fail
.endm

rv32_atest:
    addi sp, sp, -80
    sw ra, 0(sp)
    sw s0, 4(sp)
    sw s1, 8(sp)
    sw s2, 12(sp)
    sw s3, 16(sp)
    sw s4, 20(sp)
    sw s5, 24(sp)
    sw s6, 28(sp)
    sw s7, 32(sp)
    sw s8, 36(sp)
    sw s9, 40(sp)
    sw s10, 44(sp)
    sw s11, 48(sp)
    csrr s0, mstatus
    csrci mstatus, 8
    csrrw s5, mie, zero
    csrr s1, mtvec
    csrr s2, mepc
    csrr s3, mcause
    csrr s4, mtval
    csrr s6, mcountinhibit
    li s7, 0
    li s8, 0
    li a5, 0
    la t0, trap_handler
    csrw mtvec, t0
    csrr t1, mtvec
    bne t0, t1, fail
    li t0, 0
    csrw mstatus, t0

    ID_READ 0xf11
    ID_READ 0xf12
    ID_READ 0xf13
    ID_READ 0xf14
    IGNORED_WRITES misa
    IGNORED_WRITES mcounteren
    IGNORED_WRITES mip
    IGNORED_WRITES 0x7c1
    // Trigger programming is debug-only, although M-mode access is legal.
    IGNORED_WRITES 0x7a0
    IGNORED_WRITES 0x7a1
    IGNORED_WRITES 0x7a2
    IGNORED_WRITES 0x7a3
    IGNORED_WRITES 0x7a8
    IGNORED_WRITES 0x7aa

    RW_BITS mscratch, 0x5a5aa5a5
    RW_BITS mtval, 0x12345678
    RW_BITS mstatus, 0x88
    RW_BITS mie, 0x888
    // Constant-fetch is supported regardless of pipeline configuration.
    RW_BITS 0x7c0, 0x10

    csrr t4, mscratch
    csrrwi t0, mscratch, 0
    bne t0, t4, fail
    csrrsi t0, mscratch, 21
    bnez t0, fail
    csrrci t0, mscratch, 17
    li t1, 21
    bne t0, t1, fail
    csrr t0, mscratch
    li t1, 4
    bne t0, t1, fail
    csrw mscratch, t4

    // Nonexistent inhibit bits read one; bit 1 is always zero.
    csrr t4, mcountinhibit
    csrrwi t0, mcountinhibit, 0
    bne t0, t4, fail
    csrr t0, mcountinhibit
    andi t0, t0, 7
    bnez t0, fail
    csrsi mcountinhibit, 5
    csrr t0, mcountinhibit
    andi t0, t0, 7
    li t1, 5
    bne t0, t1, fail
    csrci mcountinhibit, 5
    csrr t0, mcountinhibit
    andi t0, t0, 7
    bnez t0, fail
    csrsi mcountinhibit, 5
    RW_BITS mcycle, 0x12345678
    RW_BITS mcycleh, 0x12345678
    RW_BITS minstret, 0x13579bdf
    RW_BITS minstreth, 0x12345678

    // Preserve the real cause: do not manufacture exception coverage by writes.
    csrr t4, mcause
    csrrw t0, mcause, t4
    bne t0, t4, fail
    li t1, 0
    csrrs t0, mcause, t1
    bne t0, t4, fail
    csrrc t0, mcause, t1
    bne t0, t4, fail
    csrr t0, mcause
    bne t0, t4, fail

    // MEPC bit zero is WARL zero. SET from zero also tests an aligned address.
    csrw mepc, zero
    csrrci t0, mepc, 1
    bnez t0, fail
    csrr t0, mepc
    bnez t0, fail
    la t1, machine_traps
    csrrs t0, mepc, t1
    bnez t0, fail
    csrr t0, mepc
    bne t0, t1, fail
    // Idempotent SET keeps the live vector valid even with interrupts disabled.
    la t1, trap_handler
    csrrs t0, mtvec, t1
    bne t0, t1, fail
    csrr t0, mtvec
    bne t0, t1, fail
    // The C pattern suite separately checks non-idempotent SET/CLEAR and
    // restores MTVEC before continuing here with the precise trap matrix.

machine_traps:
    // rs1=x0 suppresses writes, but a non-x0 register containing zero does not.
    .irp csr, 0xf11, 0xf12, 0xf13, 0xf14
      li t1, 0x55555555
      EXPECT 2
      csrrs t0, \csr, t1
      RESUMED
      EXPECT 2
      csrrc t0, \csr, t1
      RESUMED
      EXPECT 2
      csrrsi t0, \csr, 31
      RESUMED
      EXPECT 2
      csrrci t0, \csr, 31
      RESUMED
      li t1, 0
      EXPECT 2
      csrrs t0, \csr, t1
      RESUMED
      EXPECT 2
      csrrc t0, \csr, t1
      RESUMED
    .endr
    .irp csr, 0x7ff, 0x7b0, 0x7b1, 0x7b2, 0x7b3
      li t1, 0xaaaaaaaa
      EXPECT 2
      csrrs t0, \csr, t1
      RESUMED
      EXPECT 2
      csrrc t0, \csr, t1
      RESUMED
      EXPECT 2
      csrrsi t0, \csr, 21
      RESUMED
      EXPECT 2
      csrrci t0, \csr, 21
      RESUMED
    .endr
    EXPECT 2
    csrr t0, 0x7ff
    RESUMED
    EXPECT 2
    csrw 0x7ff, zero
    RESUMED
    EXPECT 2
    csrw 0xf11, zero
    RESUMED
    EXPECT 2
    csrsi 0xf12, 1
    RESUMED
    EXPECT 2
    csrci 0xf13, 1
    RESUMED
    EXPECT 2
    csrw 0xf14, zero
    RESUMED
    .irp csr, 0x7b0, 0x7b1, 0x7b2, 0x7b3
    EXPECT 2
    csrr t0, \csr
    RESUMED
    EXPECT 2
    csrw \csr, zero
    RESUMED
    .endr
    EXPECT 3
    ebreak
    RESUMED
    EXPECT 11
    ecall
    RESUMED
    // Exercise trap stacking of MIE into MPIE as well as the disabled case.
    csrsi mstatus, 8
    EXPECT 11, 0x1800, 0, 0x80
    ecall
    RESUMED
    csrci mstatus, 8

    // MRET with MPP=U, MPIE=0 enters U-mode; ECALL is the only exit.
    csrw mstatus, zero
    la t0, user_tests
    csrw mepc, t0
    mret
user_tests:
    EXPECT 2, 0
    csrr t0, mstatus
    RESUMED
    EXPECT 2, 0
    csrw mscratch, zero
    RESUMED
    EXPECT 2, 0
    csrrsi t0, mie, 1
    RESUMED
    EXPECT 2, 0
    csrrci t0, mie, 1
    RESUMED
    EXPECT 8, 0, 1
    ecall
    RESUMED
    csrr t0, mstatus
    andi t0, t0, 8
    bnez t0, fail
    li t0, 66
    bne s7, t0, fail

    csrw mepc, s2
    csrw mcause, s3
    csrw mtval, s4
    csrw mcountinhibit, s6
    csrw mtvec, s1
    csrw mie, s5
    csrw mstatus, s0
    lw ra, 0(sp)
    lw s0, 4(sp)
    lw s1, 8(sp)
    lw s2, 12(sp)
    lw s3, 16(sp)
    lw s4, 20(sp)
    lw s5, 24(sp)
    lw s6, 28(sp)
    lw s7, 32(sp)
    lw s8, 36(sp)
    lw s9, 40(sp)
    lw s10, 44(sp)
    lw s11, 48(sp)
    addi sp, sp, 80
    li a0, 0
    ret

.balign 4
trap_handler:
    addi sp, sp, -16
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    beqz s8, fail
    csrr t0, mepc
    bne t0, s8, fail
    csrr t1, mcause
    bne t1, s9, fail
    csrr t1, mstatus
    li t2, 0x1808
    and t2, t1, t2
    bne t2, s10, fail
    andi t2, t1, 0x80
    bne t2, a2, fail
    addi s7, s7, 1
    bne s7, a5, fail
    addi t0, t0, 4
    csrw mepc, t0
    li s8, 0
    beqz s11, 1f
    li t0, 0x1800
    csrs mstatus, t0
1:
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    addi sp, sp, 16
    mret

// Do not MRET on unexpected traps: print a bounded verdict and stop simulation.
fail:
    li t0, 0x83800200
    la t1, fail_message
1:
    lbu t2, 0(t1)
    beqz t2, 2f
    sw t2, 0(t0)
    addi t1, t1, 1
    j 1b
2:
    li t2, 255
    sw t2, 0(t0)
3:
    j 3b

.section .rodata
fail_message:
    .asciz "rv32_test_csr: CSR test failed (CSR/trap check)\n"
