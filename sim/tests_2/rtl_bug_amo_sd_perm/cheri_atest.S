// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.option norelax
.option norvc
.section .text
.globl cheri_atest

.balign 16
trap_handler:
    csrr x14, mcause
    csw x14, 0(c10)
    csrr x14, mtval
    csw x14, 4(c10)
    cspecialr c15, mepcc
    cincoffset c15, c15, 4
    cspecialw mepcc, c15
    mret

cheri_atest:
    cincoffset csp, csp, -64
    csc cra, 0(csp)
    csc c8, 8(csp)
    csc c9, 16(csp)
    cspecialr c8, mtcc
    csc c8, 24(csp)
    csc c3, 32(csp)
    csc c4, 40(csp)
    cspecialr c6, mtdc
    li x11, 0x80030000
    csetaddr c10, c6, x11
    cspecialr c3, mscratchc
    auipcc c4, 0
    auipcc c8, 0
    lui x11, %hi(trap_handler)
    addi x11, x11, %lo(trap_handler)
    csetaddr c8, c8, x11
    cspecialw mtcc, c8
    li x11, 0x80020000
    csetaddr c9, c6, x11
    li x12, 0x80030000
zfill:
    csc c0, 0(c9)
    cincoffset c9, c9, 8
    addi x11, x11, 8
    bltu x11, x12, zfill
    csrw 0xbc2, zero
    csrw 0xbc1, zero
// ---- case 0: amoadd noSD in-bounds aligned
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x12, 0x101
    .word 0x00c2a42f
    cgetaddr x11, c8
    csw x11, 8(c10)
    .word 0xff7405db
    csw x11, 12(c10)
    cgettag x11, c8
    csw x11, 16(c10)
    cgetperm x11, c8
    csw x11, 20(c10)
    cgettype x11, c8
    csw x11, 24(c10)
    cgetbase x11, c8
    csw x11, 28(c10)
    .word 0xff8405db
    csw x11, 32(c10)
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x11, 0(c9)
    csw x11, 36(c10)
    clw x11, 4(c9)
    csw x11, 40(c10)
    clc c9, 0(c9)
    .word 0xff7485db
    csw x11, 44(c10)
    cgettag x11, c9
    csw x11, 48(c10)
    csrr x11, 0xbc1
    csw x11, 52(c10)
    csw x13, 56(c10)
    li x11, 0
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 1: amoadd noSD out-of-bounds (at top)
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x12, 0x101
    .word 0x00c2a42f
    cgetaddr x11, c8
    csw x11, 8(c10)
    .word 0xff7405db
    csw x11, 12(c10)
    cgettag x11, c8
    csw x11, 16(c10)
    cgetperm x11, c8
    csw x11, 20(c10)
    cgettype x11, c8
    csw x11, 24(c10)
    cgetbase x11, c8
    csw x11, 28(c10)
    .word 0xff8405db
    csw x11, 32(c10)
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x11, 0(c9)
    csw x11, 36(c10)
    clw x11, 4(c9)
    csw x11, 40(c10)
    clc c9, 0(c9)
    .word 0xff7485db
    csw x11, 44(c10)
    cgettag x11, c9
    csw x11, 48(c10)
    csrr x11, 0xbc1
    csw x11, 52(c10)
    csw x13, 56(c10)
    li x11, 1
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 2: amoswap noSD misaligned in-bounds
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x12, 0x101
    .word 0x08c2a42f
    cgetaddr x11, c8
    csw x11, 8(c10)
    .word 0xff7405db
    csw x11, 12(c10)
    cgettag x11, c8
    csw x11, 16(c10)
    cgetperm x11, c8
    csw x11, 20(c10)
    cgettype x11, c8
    csw x11, 24(c10)
    cgetbase x11, c8
    csw x11, 28(c10)
    .word 0xff8405db
    csw x11, 32(c10)
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x11, 0(c9)
    csw x11, 36(c10)
    clw x11, 4(c9)
    csw x11, 40(c10)
    clc c9, 0(c9)
    .word 0xff7485db
    csw x11, 44(c10)
    cgettag x11, c9
    csw x11, 48(c10)
    csrr x11, 0xbc1
    csw x11, 52(c10)
    csw x13, 56(c10)
    li x11, 2
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 3: amoadd noSD zero-length cap
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x12, 0x101
    .word 0x00c2a42f
    cgetaddr x11, c8
    csw x11, 8(c10)
    .word 0xff7405db
    csw x11, 12(c10)
    cgettag x11, c8
    csw x11, 16(c10)
    cgetperm x11, c8
    csw x11, 20(c10)
    cgettype x11, c8
    csw x11, 24(c10)
    cgetbase x11, c8
    csw x11, 28(c10)
    .word 0xff8405db
    csw x11, 32(c10)
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x11, 0(c9)
    csw x11, 36(c10)
    clw x11, 4(c9)
    csw x11, 40(c10)
    clc c9, 0(c9)
    .word 0xff7485db
    csw x11, 44(c10)
    cgettag x11, c9
    csw x11, 48(c10)
    csrr x11, 0xbc1
    csw x11, 52(c10)
    csw x13, 56(c10)
    li x11, 3
    csw x11, 60(c10)
    cincoffset c10, c10, 64
    clc c8, 24(csp)
    cspecialw mtcc, c8
    clc cra, 0(csp)
    clc c8, 8(csp)
    clc c9, 16(csp)
    clc c3, 32(csp)
    clc c4, 40(csp)
    cincoffset csp, csp, 64
    li a0, 4
    cret

.globl rec_base
rec_base:
    cspecialr ca0, mtdc
    li a1, 0x80030000
    csetaddr ca0, ca0, a1
    cret
