// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// KUDU-076: the LSU sets bus_err_q when the first half of a misaligned access
// takes a bus error, and only clears it when the next load/store starts.
// CSR instructions also complete through the LSU (csr_go), and
// lsu_err_mcause checks data_or_pmp_err (which includes bus_err_q) before
// csr_err, so a failing CSR access that follows the faulting split access
// (with no load/store in between) reports a load/store access fault with
// mtval = addr_last_q instead of an illegal-instruction exception.
//
// void sb_run(unsigned *r): five cases of 5 words each,
//   {first mcause, first mtval, last mcause, last mtval, failing CSR insn}.
// The trap handler makes no memory access (one would clear bus_err_q): it
// moves the previous mcause/mtval from s2/s3 to s4/s5, reads the new ones
// into s2/s3 and skips the trapping instruction.
//   C0 control  illegal csrr 0x5c0 alone
//   C1          misaligned lw (first half unmapped), then illegal csrr 0x5c0
//   C2          misaligned sw (first half unmapped), then illegal csrr 0x5c0
//   C3          misaligned lw, then csrw mvendorid (read-only CSR)
//   C4 control  misaligned lw, an aligned lw, then illegal csrr 0x5c0

.option norvc
.option norelax

.equ BAD_ADDR, 0x7ffffffd    // word 0x7ffffffc unmapped, 0x80000000 mapped

.section .text
.globl sb_run

.macro CASE_BEGIN
    li s2, 0
    li s3, 0
    li s4, 0
    li s5, 0
    li t1, BAD_ADDR
.endm

.macro CASE_END k, insn_label
    sw s4, (\k*20+0)(s6)
    sw s5, (\k*20+4)(s6)
    sw s2, (\k*20+8)(s6)
    sw s3, (\k*20+12)(s6)
    lw t0, \insn_label
    sw t0, (\k*20+16)(s6)
.endm

sb_run:
    addi sp, sp, -32
    sw s2, 0(sp)
    sw s3, 4(sp)
    sw s4, 8(sp)
    sw s5, 12(sp)
    sw s6, 16(sp)
    sw s7, 20(sp)
    mv s6, a0
    csrr s7, mtvec
    la t0, sb_handler
    csrw mtvec, t0

    CASE_BEGIN
    lw t2, 0(s6)             // a good load: bus_err_q = 0
c0_csr:
    csrr t0, 0x5c0
    CASE_END 0, c0_csr

    CASE_BEGIN
    lw t2, 0(t1)             // load access fault, bus_err_q = 1
c1_csr:
    csrr t0, 0x5c0
    CASE_END 1, c1_csr

    CASE_BEGIN
    sw zero, 0(t1)           // store access fault, bus_err_q = 1
c2_csr:
    csrr t0, 0x5c0
    CASE_END 2, c2_csr

    CASE_BEGIN
    lw t2, 0(t1)
c3_csr:
    csrw mvendorid, zero
    CASE_END 3, c3_csr

    CASE_BEGIN
    lw t2, 0(t1)
    lw t2, 0(s6)             // a good load clears bus_err_q
c4_csr:
    csrr t0, 0x5c0
    CASE_END 4, c4_csr

    csrw mtvec, s7
    lw s2, 0(sp)
    lw s3, 4(sp)
    lw s4, 8(sp)
    lw s5, 12(sp)
    lw s6, 16(sp)
    lw s7, 20(sp)
    addi sp, sp, 32
    ret

.balign 64
sb_handler:
    mv s4, s2
    mv s5, s3
    csrr s2, mcause
    csrr s3, mtval
    csrr t0, mepc
    addi t0, t0, 4
    csrw mepc, t0
    mret
