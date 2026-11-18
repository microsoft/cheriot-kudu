// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// RV32 / PMODE=0 flavour. Each case writes 4 words at a5:
//   [0] mcause (0xffff = no trap)  [1] mtval  [2] t1 after the case
//   [3] address of the instruction under test
// The trap handler records mcause/mtval and skips the 32-bit instruction.
.option norelax
.option norvc
.section .text
.globl csr_atest
.balign 64
handler:
    csrr t6, mcause
    sw t6, 0(a5)
    csrr t6, mtval
    sw t6, 4(a5)
    csrr t6, mepc
    addi t6, t6, 4
    csrw mepc, t6
    mret

.macro BEGIN_CASE site
    li t0, 0xffff
    sw t0, 0(a5)
    sw zero, 4(a5)
    la t0, \site
    sw t0, 12(a5)
    li t1, 0x5555aaaa
    li t0, -1
.endm

.macro END_CASE
    sw t1, 8(a5)
    addi a5, a5, 16
.endm

csr_atest:
    // a0 = results (4 words per case)
    mv a5, a0
    csrr t2, mtvec
    la t0, handler
    csrw mtvec, t0

    // case 0: unimplemented CSR read
    BEGIN_CASE c0_site
c0_site:
    csrr t1, 0x3ff
    END_CASE

    // case 1: write to read-only mvendorid
    BEGIN_CASE c1_site
c1_site:
    csrw mvendorid, t0
    END_CASE

    // case 2: unimplemented CSR, immediate form
    BEGIN_CASE c2_site
c2_site:
    csrrwi t1, 0x3ff, 5
    END_CASE

    // case 3 (control): custom-0 opcode reports the instruction bits
    BEGIN_CASE c3_site
c3_site:
    .word 0x0000000b
    END_CASE

    // case 4 (control): legal CSR access does not trap
    BEGIN_CASE c4_site
    li t1, 0x1234
    csrw mscratch, t1
c4_site:
    csrr t1, mscratch
    END_CASE

    // case 5: read mstatush
    BEGIN_CASE c5_site
c5_site:
    csrr t1, 0x310
    END_CASE

    // case 6: write mstatush (t0 = all ones)
    BEGIN_CASE c6_site
    li t1, 0
c6_site:
    csrw 0x310, t0
    END_CASE

    // case 7: read mstatush after the write
    BEGIN_CASE c7_site
c7_site:
    csrr t1, 0x310
    END_CASE

    csrw mtvec, t2
    ret
