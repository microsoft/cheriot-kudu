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
// ---- case 0: lr LDonly inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
// ---- case 1: sc LDonly inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
// ---- case 2: sc_resv LDonly inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
// ---- case 3: amoswap LDonly inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 3
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 4: amoadd LDonly inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 4
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 5: lr LDonly inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 5
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 6: sc LDonly inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 6
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 7: sc_resv LDonly inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 7
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 8: amoswap LDonly inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 8
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 9: amoadd LDonly inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 9
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 10: lr LDonly top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 10
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 11: sc LDonly top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 11
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 12: sc_resv LDonly top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 12
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 13: amoswap LDonly top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 13
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 14: amoadd LDonly top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 14
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 15: lr LDonly at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023010
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
    li x11, 15
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 16: sc LDonly at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023010
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
    li x11, 16
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 17: sc_resv LDonly at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023010
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
    li x11, 17
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 18: amoswap LDonly at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023010
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
    li x11, 18
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 19: amoadd LDonly at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023010
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
    li x11, 19
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 20: lr LDonly straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 20
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 21: sc LDonly straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 21
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 22: sc_resv LDonly straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 22
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 23: amoswap LDonly straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 23
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 24: amoadd LDonly straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 24
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 25: lr LDonly mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 25
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 26: sc LDonly mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 26
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 27: sc_resv LDonly mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 27
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 28: amoswap LDonly mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 28
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 29: amoadd LDonly mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 29
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 30: lr LDonly mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 30
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 31: sc LDonly mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 31
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 32: sc_resv LDonly mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 32
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 33: amoswap LDonly mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 33
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 34: amoadd LDonly mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 34
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 35: lr LDonly mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 35
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 36: sc LDonly mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 36
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 37: sc_resv LDonly mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 37
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 38: amoswap LDonly mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 38
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 39: amoadd LDonly mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 39
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 40: lr LDonly zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 40
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 41: sc LDonly zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 41
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 42: sc_resv LDonly zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 42
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 43: amoswap LDonly zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 43
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 44: amoadd LDonly zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 44
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 45: lr LDonly len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 45
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 46: sc LDonly len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 46
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 47: sc_resv LDonly len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 47
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 48: amoswap LDonly len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 48
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 49: amoadd LDonly len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x21
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 49
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 50: lr SDonly inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 50
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 51: sc SDonly inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 51
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 52: sc_resv SDonly inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 52
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 53: amoswap SDonly inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 53
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 54: amoadd SDonly inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 54
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 55: lr SDonly inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 55
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 56: sc SDonly inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 56
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 57: sc_resv SDonly inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 57
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 58: amoswap SDonly inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 58
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 59: amoadd SDonly inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 59
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 60: lr SDonly top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 60
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 61: sc SDonly top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 61
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 62: sc_resv SDonly top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 62
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 63: amoswap SDonly top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 63
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 64: amoadd SDonly top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 64
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 65: lr SDonly at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023010
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
    li x11, 65
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 66: sc SDonly at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023010
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
    li x11, 66
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 67: sc_resv SDonly at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023010
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
    li x11, 67
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 68: amoswap SDonly at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023010
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
    li x11, 68
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 69: amoadd SDonly at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023010
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
    li x11, 69
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 70: lr SDonly straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 70
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 71: sc SDonly straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 71
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 72: sc_resv SDonly straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 72
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 73: amoswap SDonly straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 73
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 74: amoadd SDonly straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 74
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 75: lr SDonly mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 75
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 76: sc SDonly mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 76
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 77: sc_resv SDonly mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 77
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 78: amoswap SDonly mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 78
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 79: amoadd SDonly mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 79
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 80: lr SDonly mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 80
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 81: sc SDonly mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 81
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 82: sc_resv SDonly mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 82
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 83: amoswap SDonly mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 83
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 84: amoadd SDonly mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 84
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 85: lr SDonly mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 85
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 86: sc SDonly mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 86
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 87: sc_resv SDonly mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 87
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 88: amoswap SDonly mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 88
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 89: amoadd SDonly mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 89
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 90: lr SDonly zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 90
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 91: sc SDonly zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 91
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 92: sc_resv SDonly zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 92
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 93: amoswap SDonly zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 93
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 94: amoadd SDonly zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 94
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 95: lr SDonly len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 95
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 96: sc SDonly len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 96
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 97: sc_resv SDonly len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 97
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 98: amoswap SDonly len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 98
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 99: amoadd SDonly len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x5
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 99
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 100: lr dataRW inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 100
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 101: sc dataRW inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 101
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 102: sc_resv dataRW inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 102
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 103: amoswap dataRW inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 103
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 104: amoadd dataRW inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 104
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 105: lr dataRW inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 105
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 106: sc dataRW inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 106
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 107: sc_resv dataRW inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 107
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 108: amoswap dataRW inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 108
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 109: amoadd dataRW inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 109
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 110: lr dataRW top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 110
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 111: sc dataRW top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 111
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 112: sc_resv dataRW top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 112
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 113: amoswap dataRW top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 113
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 114: amoadd dataRW top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 114
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 115: lr dataRW at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023010
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
    li x11, 115
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 116: sc dataRW at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023010
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
    li x11, 116
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 117: sc_resv dataRW at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023010
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
    li x11, 117
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 118: amoswap dataRW at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023010
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
    li x11, 118
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 119: amoadd dataRW at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023010
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
    li x11, 119
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 120: lr dataRW straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 120
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 121: sc dataRW straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 121
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 122: sc_resv dataRW straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 122
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 123: amoswap dataRW straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 123
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 124: amoadd dataRW straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 124
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 125: lr dataRW mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 125
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 126: sc dataRW mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 126
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 127: sc_resv dataRW mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 127
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 128: amoswap dataRW mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 128
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 129: amoadd dataRW mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 129
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 130: lr dataRW mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 130
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 131: sc dataRW mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 131
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 132: sc_resv dataRW mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 132
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 133: amoswap dataRW mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 133
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 134: amoadd dataRW mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 134
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 135: lr dataRW mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 135
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 136: sc dataRW mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 136
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 137: sc_resv dataRW mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 137
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 138: amoswap dataRW mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 138
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 139: amoadd dataRW mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 139
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 140: lr dataRW zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 140
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 141: sc dataRW zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 141
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 142: sc_resv dataRW zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 142
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 143: amoswap dataRW zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 143
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 144: amoadd dataRW zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 144
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 145: lr dataRW len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 145
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 146: sc dataRW len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 146
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 147: sc_resv dataRW len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 147
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 148: amoswap dataRW len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 148
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 149: amoadd dataRW len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x25
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 149
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 150: lr untag+noSD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 150
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 151: sc untag+noSD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 151
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 152: sc_resv untag+noSD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 152
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 153: amoswap untag+noSD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 153
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 154: amoadd untag+noSD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 154
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 155: lr untag+noSD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 155
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 156: sc untag+noSD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 156
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 157: sc_resv untag+noSD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 157
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 158: amoswap untag+noSD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 158
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 159: amoadd untag+noSD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 159
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 160: lr untag+noSD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 160
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 161: sc untag+noSD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 161
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 162: sc_resv untag+noSD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 162
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 163: amoswap untag+noSD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 163
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 164: amoadd untag+noSD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 164
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 165: lr untag+noSD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023010
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
    li x11, 165
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 166: sc untag+noSD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023010
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
    li x11, 166
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 167: sc_resv untag+noSD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023010
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
    li x11, 167
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 168: amoswap untag+noSD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023010
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
    li x11, 168
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 169: amoadd untag+noSD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023010
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
    li x11, 169
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 170: lr untag+noSD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 170
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 171: sc untag+noSD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 171
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 172: sc_resv untag+noSD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 172
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 173: amoswap untag+noSD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 173
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 174: amoadd untag+noSD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 174
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 175: lr untag+noSD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 175
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 176: sc untag+noSD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 176
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 177: sc_resv untag+noSD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 177
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 178: amoswap untag+noSD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 178
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 179: amoadd untag+noSD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 179
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 180: lr untag+noSD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 180
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 181: sc untag+noSD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 181
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 182: sc_resv untag+noSD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 182
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 183: amoswap untag+noSD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 183
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 184: amoadd untag+noSD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 184
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 185: lr untag+noSD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 185
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 186: sc untag+noSD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 186
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 187: sc_resv untag+noSD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 187
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 188: amoswap untag+noSD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 188
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 189: amoadd untag+noSD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 189
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 190: lr untag+noSD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 190
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 191: sc untag+noSD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 191
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 192: sc_resv untag+noSD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 192
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 193: amoswap untag+noSD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 193
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 194: amoadd untag+noSD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 194
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 195: lr untag+noSD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 195
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 196: sc untag+noSD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 196
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 197: sc_resv untag+noSD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 197
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 198: amoswap untag+noSD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 198
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 199: amoadd untag+noSD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x7b
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    ccleartag c5, c5
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 199
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 200: lr sealed+noLD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 200
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 201: sc sealed+noLD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 201
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 202: sc_resv sealed+noLD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 202
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 203: amoswap sealed+noLD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 203
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 204: amoadd sealed+noLD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 204
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 205: lr sealed+noLD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 205
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 206: sc sealed+noLD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 206
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 207: sc_resv sealed+noLD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 207
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 208: amoswap sealed+noLD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 208
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 209: amoadd sealed+noLD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 209
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 210: lr sealed+noLD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 210
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 211: sc sealed+noLD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 211
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 212: sc_resv sealed+noLD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 212
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 213: amoswap sealed+noLD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 213
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 214: amoadd sealed+noLD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 214
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 215: lr sealed+noLD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023010
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
    li x11, 215
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 216: sc sealed+noLD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023010
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
    li x11, 216
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 217: sc_resv sealed+noLD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023010
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
    li x11, 217
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 218: amoswap sealed+noLD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023010
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
    li x11, 218
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 219: amoadd sealed+noLD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023010
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023010
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
    li x11, 219
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 220: lr sealed+noLD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 220
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 221: sc sealed+noLD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 221
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 222: sc_resv sealed+noLD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 222
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 223: amoswap sealed+noLD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 223
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 224: amoadd sealed+noLD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 224
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 225: lr sealed+noLD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 225
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 226: sc sealed+noLD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 226
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 227: sc_resv sealed+noLD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 227
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 228: amoswap sealed+noLD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 228
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 229: amoadd sealed+noLD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 229
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 230: lr sealed+noLD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 230
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 231: sc sealed+noLD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 231
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 232: sc_resv sealed+noLD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 232
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 233: amoswap sealed+noLD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 233
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 234: amoadd sealed+noLD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 234
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 235: lr sealed+noLD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 235
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 236: sc sealed+noLD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 236
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 237: sc_resv sealed+noLD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 237
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 238: amoswap sealed+noLD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 238
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 239: amoadd sealed+noLD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 239
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 240: lr sealed+noLD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 0x80023008
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
    li x11, 240
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 241: sc sealed+noLD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 241
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 242: sc_resv sealed+noLD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 0x80023008
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
    li x11, 242
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 243: amoswap sealed+noLD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 243
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 244: amoadd sealed+noLD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c5, c6, x11
    li x12, 0x0
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 0x80023008
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
    li x11, 244
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 245: lr sealed+noLD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x1002a42f
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
    li x11, 245
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 246: sc sealed+noLD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 246
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 247: sc_resv sealed+noLD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    .word 0x1004a02f
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 247
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 248: amoswap sealed+noLD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 248
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 249: amoadd sealed+noLD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023008
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x3
    csetbounds c5, c5, x12
    li x12, 0x5f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 9
    csetaddr c13, c3, x11
    cseal c5, c5, c13
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 249
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 250: sc fail on cap granule off=0
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 250
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 251: sc fail on cap granule off=4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x12, 0x00000101
    .word 0x18c2a42f
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
    li x11, 251
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 252: amoswap on cap granule off=0
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x12, 0x80000101
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
    li x11, 252
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 253: amoswap on cap granule off=4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x12, 0x80000101
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
    li x11, 253
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 254: amoadd on cap granule off=0
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x12, 0x80000101
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
    li x11, 254
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 255: amoadd on cap granule off=4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x12, 0x80000101
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
    li x11, 255
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 256: amoxor on cap granule off=0
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x12, 0x80000101
    .word 0x20c2a42f
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
    li x11, 256
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 257: amoxor on cap granule off=4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x12, 0x80000101
    .word 0x20c2a42f
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
    li x11, 257
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 258: amoor on cap granule off=0
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x12, 0x80000101
    .word 0x40c2a42f
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
    li x11, 258
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 259: amoor on cap granule off=4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x12, 0x80000101
    .word 0x40c2a42f
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
    li x11, 259
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 260: amoand on cap granule off=0
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x12, 0x80000101
    .word 0x60c2a42f
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
    li x11, 260
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 261: amoand on cap granule off=4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x12, 0x80000101
    .word 0x60c2a42f
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
    li x11, 261
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 262: amomin on cap granule off=0
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x12, 0x80000101
    .word 0x80c2a42f
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
    li x11, 262
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 263: amomin on cap granule off=4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x12, 0x80000101
    .word 0x80c2a42f
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
    li x11, 263
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 264: amomax on cap granule off=0
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x12, 0x80000101
    .word 0xa0c2a42f
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
    li x11, 264
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 265: amomax on cap granule off=4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x12, 0x80000101
    .word 0xa0c2a42f
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
    li x11, 265
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 266: amominu on cap granule off=0
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x12, 0x80000101
    .word 0xc0c2a42f
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
    li x11, 266
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 267: amominu on cap granule off=4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x12, 0x80000101
    .word 0xc0c2a42f
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
    li x11, 267
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 268: amomaxu on cap granule off=0
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x12, 0x80000101
    .word 0xe0c2a42f
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
    li x11, 268
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 269: amomaxu on cap granule off=4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
    li x11, 0x80020040
    csetaddr c7, c6, x11
    li x12, 0x40
    csetbounds c7, c7, x12
    li x12, 0x7f
    candperm c7, c7, x12
    li x11, 0x80023000
    csetaddr c9, c6, x11
    csc c7, 0(c9)
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x11, 0x80023000
    csetaddr c5, c6, x11
    li x12, 0x10
    csetbounds c5, c5, x12
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x12, 0x80000101
    .word 0xe0c2a42f
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
    li x11, 269
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
    li a0, 270
    cret

.globl rec_base
rec_base:
    cspecialr ca0, mtdc
    li a1, 0x80030000
    csetaddr ca0, ca0, a1
    cret
