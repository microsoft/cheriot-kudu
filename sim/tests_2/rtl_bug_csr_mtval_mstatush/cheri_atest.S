// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// CHERIoT PMODE=1 flavour. Each case writes 4 words at c13:
//   [0] mcause (0xffff = no trap)  [1] mtval  [2] t1 after the case  [3] 0
// The trap handler records mcause/mtval and skips the 32-bit instruction.
.option norelax
.option norvc
.section .text
.globl csr_atest
.balign 16
handler:
    csrr t2, mcause
    csw t2, 0(c13)
    csrr t2, mtval
    csw t2, 4(c13)
    cspecialr c14, mepcc
    cincoffset c14, c14, 4
    cspecialw mepcc, c14
    mret

.macro BEGIN_CASE
    li t0, 0xffff
    csw t0, 0(c13)
    csw zero, 4(c13)
    csw zero, 12(c13)
    li t1, 0x5555aaaa
    li t0, -1
.endm

.macro END_CASE
    csw t1, 8(c13)
    cincoffset c13, c13, 16
.endm

csr_atest:
    // a0 = results capability (4 words per case)
    cincoffset csp, csp, -16
    csc cra, 0(csp)
    cspecialr c15, mtcc
    csc c15, 8(csp)
    cmove c13, ca0
    auipcc c15, 0
    lui t0, %hi(handler)
    addi t0, t0, %lo(handler)
    csetaddr c15, c15, t0
    cspecialw mtcc, c15

    // case 0 (control): unimplemented CSR read, mtval = 0 at PMODE=1
    BEGIN_CASE
    csrr t1, 0x3ff
    END_CASE

    // case 1 (control): write to read-only mvendorid, mtval = 0 at PMODE=1
    BEGIN_CASE
    csrw mvendorid, t0
    END_CASE

    // case 2: read mstatush
    BEGIN_CASE
    csrr t1, 0x310
    END_CASE

    // case 3: write mstatush (t0 = all ones)
    BEGIN_CASE
    li t1, 0
    csrw 0x310, t0
    END_CASE

    // case 4: read mstatush after the write
    BEGIN_CASE
    csrr t1, 0x310
    END_CASE

    // case 5 (control): CDBG_CTRL.0 is writable and reads back
    BEGIN_CASE
    li t1, 1
    csrw 0xbc4, t1
    csrr t1, 0xbc4
    END_CASE

    // case 6: CDBG_CTRL.0 = 1 escalates a tag-clearing CSetBoundsImm to a
    // CHERI fault (cheriot-ibex cheri_ex.sv:438). t1 = tag of c12 afterwards.
    BEGIN_CASE
    cmove c12, c13
    csetboundsimm c12, c13, 2047
    cgettag t1, c12
    END_CASE
    csrw 0xbc4, zero

    // case 7 (control): same with CDBG_CTRL.0 = 0 clears the tag, no trap
    BEGIN_CASE
    cmove c12, c13
    csetboundsimm c12, c13, 2047
    cgettag t1, c12
    END_CASE

    clc c15, 8(csp)
    cspecialw mtcc, c15
    clc cra, 0(csp)
    cincoffset csp, csp, 16
    cret
