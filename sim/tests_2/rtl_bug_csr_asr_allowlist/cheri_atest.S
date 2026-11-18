// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Runs CSR accesses from a PCC without the access-system-registers (ASR)
// permission. The trap handler records mcause/mtval for each case and skips
// the faulting instruction; 0xffff in mcause means no trap was taken.
.option norelax
.option norvc
.section .text
.globl cheri_atest
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

cheri_atest:
    // a0 = results capability (2 words per case)
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
    // jump to noasr with a PCC whose permissions lack ASR
    auipcc c12, 0
    lui t0, %hi(noasr)
    addi t0, t0, %lo(noasr)
    csetaddr c12, c12, t0
    li t0, 0x16b
    candperm c12, c12, t0
    cjalr cra, c12
    clc c15, 8(csp)
    cspecialw mtcc, c15
    clc cra, 0(csp)
    cincoffset csp, csp, 16
    cret

.balign 4
noasr:
    // The handler writes results at the current c13 offset, so advance
    // c13 per case instead of using fixed offsets.
    // case 0
    li t0, 0xffff
    csw t0, 0(c13)
    csw zero, 4(c13)
    csrw 0xb00, x0
    cincoffset c13, c13, 8
    // case 1
    li t0, 0xffff
    csw t0, 0(c13)
    csw zero, 4(c13)
    csrw 0xb02, x0
    cincoffset c13, c13, 8
    // case 2
    li t0, 0xffff
    csw t0, 0(c13)
    csw zero, 4(c13)
    csrw 0xb80, x0
    cincoffset c13, c13, 8
    // case 3
    li t0, 0xffff
    csw t0, 0(c13)
    csw zero, 4(c13)
    csrw 0xb82, x0
    cincoffset c13, c13, 8
    // case 4
    li t0, 0xffff
    csw t0, 0(c13)
    csw zero, 4(c13)
    csrr t1, 0x323
    cincoffset c13, c13, 8
    // case 5
    li t0, 0xffff
    csw t0, 0(c13)
    csw zero, 4(c13)
    csrw 0x323, x0
    cincoffset c13, c13, 8
    // case 6
    li t0, 0xffff
    csw t0, 0(c13)
    csw zero, 4(c13)
    csrr t1, 0xb00
    cincoffset c13, c13, 8
    // case 7
    li t0, 0xffff
    csw t0, 0(c13)
    csw zero, 4(c13)
    csrr t1, 0x300
    cincoffset c13, c13, 8
    cret
