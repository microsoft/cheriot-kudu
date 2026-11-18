// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.section .text
.option norvc
.globl cheri_atest

#include "csr_patterns.inc"

.macro ADDRESS reg, symbol
    lui \reg, %hi(\symbol)
    addi \reg, \reg, %lo(\symbol)
.endm

// The expanded trap matrix exceeds the CHERIoT conditional-branch range.
.macro CHECK_EQ lhs, rhs
    beq \lhs, \rhs, .Lcheck_ok\@
    j test_fail
.Lcheck_ok\@:
.endm

// Check returned old values and readback for all four CSR operations.
// mask=0 still uses a nonzero rs1 register: SET/CLEAR must not become READ.
.macro MATRIX csr, value, mask
    li a0, \csr
    csrr t0, \csr
    li a2, \value
    csrrw a1, \csr, a2
    bne a1, t0, .Lmatrix_fail\@
    csrr a1, \csr
    bne a1, a2, .Lmatrix_fail\@
    li t1, \mask
    csrrs a1, \csr, t1
    bne a1, a2, .Lmatrix_fail\@
    or a2, a2, t1
    csrr a1, \csr
    bne a1, a2, .Lmatrix_fail\@
    csrrc a1, \csr, t1
    bne a1, a2, .Lmatrix_fail\@
    not t1, t1
    and a2, a2, t1
    csrr a1, \csr
    bne a1, a2, .Lmatrix_fail\@
    csrw \csr, t0
    j .Lmatrix_done\@
.Lmatrix_fail\@:
    csrw \csr, t0
    j test_fail
.Lmatrix_done\@:
.endm

// WARL/ignored writes and controls whose active settings must be preserved.
.macro UNCHANGED csr
    li a0, \csr
    csrr t0, \csr
    csrrw a1, \csr, t0
    CHECK_EQ a1, t0
    li t1, 0
    csrrs a1, \csr, t1
    CHECK_EQ a1, t0
    csrrc a1, \csr, t1
    CHECK_EQ a1, t0
    csrr a1, \csr
    CHECK_EQ a1, t0
.endm

.macro IGNORED csr
    li a0, \csr
    csrr t0, \csr
    li t1, -1
    csrrw a1, \csr, t1
    CHECK_EQ a1, t0
    csrrs a1, \csr, t1
    CHECK_EQ a1, t0
    csrrc a1, \csr, t1
    CHECK_EQ a1, t0
    csrr a1, \csr
    CHECK_EQ a1, t0
.endm

.macro READ_ID csr
    li a0, \csr
    csrr a1, \csr
    csrrc a2, \csr, zero
    CHECK_EQ a1, a2
    csrrs a2, \csr, zero
    CHECK_EQ a1, a2
    csrrsi a2, \csr, 0
    CHECK_EQ a1, a2
    csrrci a2, \csr, 0
    CHECK_EQ a1, a2
.endm

// No generic "skip fault": only this exact PC/cause/privilege may resume.
// The handler consumes the expectation; the following check proves it ran.
.macro TRAP cause, count, user, instruction:vararg
    li a0, 0x1000 + \count
    ADDRESS s0, .Lfault\@
    li s1, \cause
    li t2, 0x1800
    .if \user
      li t2, 0
      auipcc ca1, 0
      csetaddr ca1, ca1, s0
      cspecialw mepcc, ca1
      li t0, 0x1880
      csrc mstatus, t0
      mret
    .endif
.Lfault\@:
    \instruction
    li a1, \count
    CHECK_EQ a5, a1
    CHECK_EQ s0, zero
.endm

cheri_atest:
    cincoffset csp, csp, -96
    csc cra, 0(csp)
    csc c4, 8(csp)
    csc c8, 16(csp)
    csc c9, 24(csp)
    cspecialr ca1, mtcc
    csc ca1, 32(csp)
    cspecialr ca1, mepcc
    csc ca1, 40(csp)
    cspecialr ca1, mscratchc
    csc ca1, 48(csp)
    cspecialr c4, mtdc
    csc c4, 56(csp)
    csrr t0, mstatus
    csw t0, 64(csp)
    csrci mstatus, 8
    csrr t0, mie
    csw t0, 68(csp)
    csrw mie, zero
    csrr t0, mcause
    csw t0, 72(csp)
    csrr t0, mtval
    csw t0, 76(csp)
    csrr t0, mcountinhibit
    csw t0, 80(csp)
    csrsi mcountinhibit, 5

    li s0, 0
    li a5, 0
    auipcc ca1, 0
    ADDRESS t0, trap_handler
    csetaddr ca1, ca1, t0
    cspecialw mtcc, ca1

    READ_ID 0xf11
    READ_ID 0xf12
    READ_ID 0xf13
    READ_ID 0xf14
    // MISA.X/E are set and I is clear in CHERIoT mode.
    li a0, 0x301
    csrr a1, misa
    li t0, 0x800110
    and a1, a1, t0
    li t0, 0x800010
    CHECK_EQ a1, t0
    IGNORED 0x301
    IGNORED 0x306
    IGNORED 0x344
    IGNORED 0x7c1
    // Trigger CSRs are accessible in M-mode, but changes require debug mode.
    IGNORED 0x7a0
    IGNORED 0x7a1
    IGNORED 0x7a2
    IGNORED 0x7a3
    IGNORED 0x7a8
    IGNORED 0x7aa
    MATRIX 0x340, 0x13572468, 0x80
    MATRIX 0x343, 0x24681357, 0x8000
    MATRIX 0x304, 0, 0x888
    UNCHANGED 0x300
    // Do not fabricate exception causes to improve cp_cause.
    UNCHANGED 0x342
    UNCHANGED 0x320
    UNCHANGED 0x7c0
    MATRIX 0xb00, 0x12345678, 0x100
    MATRIX 0xb80, 0x1234, 0x10000
    MATRIX 0xb02, 0x12345678, 0x100
    MATRIX 0xb82, 0x1234, 0x10000
    // No stores occur while testing the watermark registers.
    MATRIX 0xbc1, 0x80010000, 0x100
    MATRIX 0xbc2, 0x80000000, 0x100
    MATRIX 0xbc4, 0, 1

    // MTDC and MSCRATCHC preserve their complete capability values.
    li a0, 0x2000
    cspecialw mtdc, c4
    cspecialr ca1, mtdc
    cseqx a1, ca1, c4
    li t0, 1
    CHECK_EQ a1, t0
    cspecialw mscratchc, c4
    cspecialr ca1, mscratchc
    cseqx a1, ca1, c4
    li t0, 1
    CHECK_EQ a1, t0

    TRAP 2, 1, 0, csrr a1, 0x777
    TRAP 2, 2, 0, csrw 0x777, a1
    TRAP 2, 3, 0, csrw mvendorid, zero
    TRAP 2, 4, 0, csrrsi a1, marchid, 1
    TRAP 2, 5, 0, csrrci a1, mimpid, 1
    TRAP 2, 6, 0, csrw mhartid, zero
    TRAP 2, 7, 0, csrr a1, 0x7b0
    TRAP 2, 8, 0, csrw 0x7b0, zero
    TRAP 2, 9, 0, csrr a1, 0x7b1
    TRAP 2, 10, 0, csrw 0x7b1, zero
    TRAP 2, 11, 0, csrr a1, 0x7b2
    TRAP 2, 12, 0, csrw 0x7b2, zero
    TRAP 2, 13, 0, csrr a1, 0x7b3
    TRAP 2, 14, 0, csrw 0x7b3, zero
    TRAP 2, 15, 0, csrr a1, mtvec
    TRAP 2, 16, 0, csrw mtvec, zero
    TRAP 2, 17, 0, csrr a1, mepc
    TRAP 2, 18, 0, csrw mepc, zero
    TRAP 2, 19, 0, cspecialr ca1, 24
    TRAP 2, 20, 0, cspecialw 24, c4
    TRAP 11, 21, 0, ecall
    TRAP 3, 22, 0, ebreak
    TRAP 2, 23, 1, csrr a1, mscratch
    TRAP 2, 24, 1, csrw mscratch, zero
    TRAP 8, 25, 1, ecall
    .set trap_count, 25
    .irp csr, 0xf11, 0xf12, 0xf13, 0xf14
      li a3, 0x55555555
      .set trap_count, trap_count+1
      TRAP 2, trap_count, 0, csrrs a1, \csr, a3
      .set trap_count, trap_count+1
      TRAP 2, trap_count, 0, csrrc a1, \csr, a3
      .set trap_count, trap_count+1
      TRAP 2, trap_count, 0, csrrsi a1, \csr, 31
      .set trap_count, trap_count+1
      TRAP 2, trap_count, 0, csrrci a1, \csr, 31
      li a3, 0
      .set trap_count, trap_count+1
      TRAP 2, trap_count, 0, csrrs a1, \csr, a3
      .set trap_count, trap_count+1
      TRAP 2, trap_count, 0, csrrc a1, \csr, a3
    .endr
    .irp csr, 0x777, 0x7b0, 0x7b1, 0x7b2, 0x7b3, 0x305, 0x341
      li a3, 0xaaaaaaaa
      .set trap_count, trap_count+1
      TRAP 2, trap_count, 0, csrrs a1, \csr, a3
      .set trap_count, trap_count+1
      TRAP 2, trap_count, 0, csrrc a1, \csr, a3
      .set trap_count, trap_count+1
      TRAP 2, trap_count, 0, csrrsi a1, \csr, 21
      .set trap_count, trap_count+1
      TRAP 2, trap_count, 0, csrrci a1, \csr, 21
    .endr
    li a0, 0
    j test_exit

.balign 16
trap_handler:
    csrr t0, mcause
    bne t0, s1, unexpected_trap
    cspecialr ca1, mepcc
    cgetaddr t0, ca1
    beq s0, zero, unexpected_trap
    bne t0, s0, unexpected_trap
    csrr t0, mstatus
    andi t1, t0, 8
    bne t1, zero, unexpected_trap
    li t1, 0x1800
    and t0, t0, t1
    bne t0, t2, unexpected_trap
    // All deliberate faulting instructions are 32 bits, including EBREAK.
    cincoffset ca1, ca1, 4
    cspecialw mepcc, ca1
    li s0, 0
    addi a5, a5, 1
    csrs mstatus, t1
    mret

unexpected_trap:
    li a0, 0xeeee
    auipcc ca1, 0
    ADDRESS t0, test_fail
    csetaddr ca1, ca1, t0
    cspecialw mepcc, ca1
    li t0, 0x1800
    csrs mstatus, t0
    mret

test_fail:
    // Every failure keeps a nonzero phase code, including unexpected traps.
    bne a0, zero, test_exit
    li a0, -1
test_exit:
    clc ca1, 48(csp)
    cspecialw mscratchc, ca1
    clc ca1, 56(csp)
    cspecialw mtdc, ca1
    clc ca1, 40(csp)
    cspecialw mepcc, ca1
    clc ca1, 32(csp)
    cspecialw mtcc, ca1
    clw t0, 72(csp)
    csrw mcause, t0
    clw t0, 76(csp)
    csrw mtval, t0
    clw t0, 80(csp)
    csrw mcountinhibit, t0
    clw t0, 68(csp)
    csrw mie, t0
    clw t0, 64(csp)
    csrw mstatus, t0
    clc cra, 0(csp)
    clc c4, 8(csp)
    clc c8, 16(csp)
    clc c9, 24(csp)
    cincoffset csp, csp, 96
    cret
