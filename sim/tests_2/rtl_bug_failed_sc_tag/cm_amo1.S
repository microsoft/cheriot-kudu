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
// ---- case 0: lr full inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
// ---- case 1: sc full inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
// ---- case 2: sc_resv full inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
// ---- case 3: amoswap full inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
// ---- case 4: amoadd full inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
// ---- case 5: amoor full inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 5
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 6: lr full inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 6
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 7: sc full inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 7
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 8: sc_resv full inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 8
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 9: amoswap full inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 9
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 10: amoadd full inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 10
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 11: amoor full inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023004
    csetaddr c5, c5, x11
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 11
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 12: lr full top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 12
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 13: sc full top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 13
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 14: sc_resv full top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 14
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 15: amoswap full top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 15
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 16: amoadd full top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 16
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 17: amoor full top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x8002300c
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 17
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 18: lr full at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 18
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 19: sc full at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 19
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 20: sc_resv full at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 20
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 21: amoswap full at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 21
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 22: amoadd full at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 22
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 23: amoor full at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023010
    csetaddr c5, c5, x11
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 23
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 24: lr full straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 24
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 25: sc full straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 25
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 26: sc_resv full straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 26
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 27: amoswap full straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 27
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 28: amoadd full straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 28
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 29: amoor full straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x8002300e
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 29
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 30: lr full mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 30
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 31: sc full mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 31
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 32: sc_resv full mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 32
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 33: amoswap full mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 33
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 34: amoadd full mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 34
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 35: amoor full mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023002
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 35
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 36: lr full mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 36
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 37: sc full mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 37
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 38: sc_resv full mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 38
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 39: amoswap full mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 39
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 40: amoadd full mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 40
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 41: amoor full mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023001
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 41
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 42: lr full mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 42
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 43: sc full mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 43
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 44: sc_resv full mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 44
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 45: amoswap full mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 45
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 46: amoadd full mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 46
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 47: amoor full mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x8002300d
    csetaddr c5, c5, x11
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 47
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 48: lr full zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 48
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 49: sc full zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 49
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 50: sc_resv full zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 50
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 51: amoswap full zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 51
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 52: amoadd full zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 52
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 53: amoor full zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023008
    csetaddr c5, c5, x11
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 53
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 54: lr full len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 54
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 55: sc full len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 55
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 56: sc_resv full len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 56
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 57: amoswap full len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 57
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 58: amoadd full len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 58
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 59: amoor full len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
    candperm c5, c5, x12
    li x11, 0x80023000
    csetaddr c5, c5, x11
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 59
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 60: lr untagged inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 60
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 61: sc untagged inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 61
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 62: sc_resv untagged inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 62
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 63: amoswap untagged inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 63
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 64: amoadd untagged inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 64
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 65: lr untagged inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 65
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 66: sc untagged inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 66
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 67: sc_resv untagged inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 67
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 68: amoswap untagged inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 68
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 69: amoadd untagged inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 69
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 70: lr untagged top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 70
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 71: sc untagged top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 71
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 72: sc_resv untagged top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 72
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 73: amoswap untagged top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 73
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 74: amoadd untagged top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 74
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 75: lr untagged at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 75
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 76: sc untagged at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 76
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 77: sc_resv untagged at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 77
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 78: amoswap untagged at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 78
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 79: amoadd untagged at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 79
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 80: lr untagged straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 80
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 81: sc untagged straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 81
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 82: sc_resv untagged straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 82
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 83: amoswap untagged straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 83
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 84: amoadd untagged straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 84
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 85: lr untagged mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 85
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 86: sc untagged mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 86
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 87: sc_resv untagged mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 87
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 88: amoswap untagged mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 88
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 89: amoadd untagged mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 89
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 90: lr untagged mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 90
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 91: sc untagged mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 91
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 92: sc_resv untagged mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 92
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 93: amoswap untagged mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 93
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 94: amoadd untagged mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 94
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 95: lr untagged mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 95
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 96: sc untagged mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 96
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 97: sc_resv untagged mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 97
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 98: amoswap untagged mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 98
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 99: amoadd untagged mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 99
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 100: lr untagged zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 100
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 101: sc untagged zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 101
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 102: sc_resv untagged zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 102
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 103: amoswap untagged zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 103
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 104: amoadd untagged zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 104
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 105: lr untagged len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 105
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 106: sc untagged len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 106
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 107: sc_resv untagged len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 107
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 108: amoswap untagged len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 108
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 109: amoadd untagged len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 109
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 110: lr sealed inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 110
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 111: sc sealed inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 111
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 112: sc_resv sealed inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 112
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 113: amoswap sealed inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 113
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 114: amoadd sealed inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 114
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 115: lr sealed inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 115
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 116: sc sealed inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 116
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 117: sc_resv sealed inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 117
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 118: amoswap sealed inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 118
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 119: amoadd sealed inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 119
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 120: lr sealed top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 120
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 121: sc sealed top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 121
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 122: sc_resv sealed top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 122
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 123: amoswap sealed top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 123
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 124: amoadd sealed top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 124
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 125: lr sealed at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 125
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 126: sc sealed at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 126
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 127: sc_resv sealed at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 127
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 128: amoswap sealed at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 128
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 129: amoadd sealed at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 129
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 130: lr sealed straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 130
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 131: sc sealed straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 131
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 132: sc_resv sealed straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 132
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 133: amoswap sealed straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 133
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 134: amoadd sealed straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 134
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 135: lr sealed mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 135
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 136: sc sealed mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 136
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 137: sc_resv sealed mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 137
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 138: amoswap sealed mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 138
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 139: amoadd sealed mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 139
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 140: lr sealed mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 140
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 141: sc sealed mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 141
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 142: sc_resv sealed mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 142
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 143: amoswap sealed mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 143
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 144: amoadd sealed mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 144
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 145: lr sealed mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 145
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 146: sc sealed mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 146
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 147: sc_resv sealed mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 147
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 148: amoswap sealed mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 148
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 149: amoadd sealed mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 149
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 150: lr sealed zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 150
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 151: sc sealed zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 151
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 152: sc_resv sealed zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 152
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 153: amoswap sealed zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 153
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 154: amoadd sealed zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 154
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 155: lr sealed len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 155
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 156: sc sealed len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 156
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 157: sc_resv sealed len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 157
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 158: amoswap sealed len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 158
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 159: amoadd sealed len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x7f
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
    li x11, 159
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 160: lr noLD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 160
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 161: sc noLD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 161
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 162: sc_resv noLD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 162
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 163: amoswap noLD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 163
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 164: amoadd noLD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 164
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 165: amoor noLD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 165
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 166: lr noLD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 166
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 167: sc noLD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 167
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 168: sc_resv noLD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 168
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 169: amoswap noLD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 169
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 170: amoadd noLD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 170
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 171: amoor noLD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 171
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 172: lr noLD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 172
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 173: sc noLD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 173
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 174: sc_resv noLD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 174
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 175: amoswap noLD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 175
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 176: amoadd noLD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 176
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 177: amoor noLD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 177
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 178: lr noLD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 178
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 179: sc noLD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 179
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 180: sc_resv noLD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 180
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 181: amoswap noLD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 181
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 182: amoadd noLD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 182
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 183: amoor noLD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 183
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 184: lr noLD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 184
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 185: sc noLD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 185
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 186: sc_resv noLD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 186
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 187: amoswap noLD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 187
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 188: amoadd noLD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 188
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 189: amoor noLD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
// ---- case 190: lr noLD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 190
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 191: sc noLD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 191
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 192: sc_resv noLD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 192
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 193: amoswap noLD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 193
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 194: amoadd noLD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 194
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 195: amoor noLD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 195
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 196: lr noLD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 196
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 197: sc noLD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 197
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 198: sc_resv noLD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 198
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 199: amoswap noLD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 199
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 200: amoadd noLD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 200
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 201: amoor noLD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 201
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 202: lr noLD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 202
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 203: sc noLD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 203
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 204: sc_resv noLD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 204
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 205: amoswap noLD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 205
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 206: amoadd noLD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 206
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 207: amoor noLD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 207
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 208: lr noLD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 208
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 209: sc noLD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 209
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 210: sc_resv noLD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 210
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 211: amoswap noLD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 211
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 212: amoadd noLD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 212
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 213: amoor noLD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
// ---- case 214: lr noLD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 214
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 215: sc noLD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 215
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 216: sc_resv noLD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 216
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 217: amoswap noLD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 217
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 218: amoadd noLD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 218
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 219: amoor noLD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 219
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 220: lr noSD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 220
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 221: sc noSD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 221
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 222: sc_resv noSD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 222
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 223: amoswap noSD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 223
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 224: amoadd noSD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 224
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 225: amoor noSD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 225
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 226: lr noSD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 226
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 227: sc noSD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 227
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 228: sc_resv noSD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 228
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 229: amoswap noSD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 229
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 230: amoadd noSD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 230
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 231: amoor noSD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x80023004
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 231
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 232: lr noSD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 232
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 233: sc noSD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 233
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 234: sc_resv noSD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 234
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 235: amoswap noSD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 235
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 236: amoadd noSD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 236
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 237: amoor noSD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
// ---- case 238: lr noSD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 238
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 239: sc noSD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 239
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 240: sc_resv noSD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 240
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 241: amoswap noSD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 241
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 242: amoadd noSD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 242
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 243: amoor noSD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x80023010
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 243
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 244: lr noSD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 244
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 245: sc noSD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 245
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 246: sc_resv noSD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 246
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 247: amoswap noSD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 247
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 248: amoadd noSD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 248
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 249: amoor noSD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 249
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 250: lr noSD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 250
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 251: sc noSD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 251
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 252: sc_resv noSD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 252
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 253: amoswap noSD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 253
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 254: amoadd noSD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 254
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 255: amoor noSD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 255
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 256: lr noSD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 256
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 257: sc noSD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 257
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 258: sc_resv noSD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 258
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 259: amoswap noSD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 259
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 260: amoadd noSD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 260
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 261: amoor noSD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 261
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 262: lr noSD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 262
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 263: sc noSD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 263
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 264: sc_resv noSD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 264
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 265: amoswap noSD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 265
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 266: amoadd noSD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 266
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 267: amoor noSD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x8002300c
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 267
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 268: lr noSD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 268
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 269: sc noSD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 269
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 270: sc_resv noSD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 270
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 271: amoswap noSD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 271
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 272: amoadd noSD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 272
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 273: amoor noSD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x80023008
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 273
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 274: lr noSD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 274
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 275: sc noSD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 275
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 276: sc_resv noSD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 276
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 277: amoswap noSD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 277
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 278: amoadd noSD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 278
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 279: amoor noSD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x11, 0x80023000
    csetaddr c9, c6, x11
    clw x13, 0(c9)
    li x12, 0x00000101
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
    li x11, 279
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 280: lr noLDnoSD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 280
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 281: sc noLDnoSD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 281
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 282: sc_resv noLDnoSD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 282
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 283: amoswap noLDnoSD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 283
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 284: amoadd noLDnoSD inb
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 284
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 285: lr noLDnoSD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 285
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 286: sc noLDnoSD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 286
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 287: sc_resv noLDnoSD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 287
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 288: amoswap noLDnoSD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 288
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 289: amoadd noLDnoSD inb hi
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 289
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 290: lr noLDnoSD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 290
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 291: sc noLDnoSD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 291
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 292: sc_resv noLDnoSD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 292
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 293: amoswap noLDnoSD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 293
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 294: amoadd noLDnoSD top-4
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 294
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 295: lr noLDnoSD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 295
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 296: sc noLDnoSD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 296
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 297: sc_resv noLDnoSD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 297
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 298: amoswap noLDnoSD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 298
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 299: amoadd noLDnoSD at top
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 299
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 300: lr noLDnoSD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 300
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 301: sc noLDnoSD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 301
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 302: sc_resv noLDnoSD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 302
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 303: amoswap noLDnoSD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 303
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 304: amoadd noLDnoSD straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 304
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 305: lr noLDnoSD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 305
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 306: sc noLDnoSD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 306
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 307: sc_resv noLDnoSD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 307
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 308: amoswap noLDnoSD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 308
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 309: amoadd noLDnoSD mis+2
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 309
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 310: lr noLDnoSD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 310
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 311: sc noLDnoSD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 311
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 312: sc_resv noLDnoSD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 312
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 313: amoswap noLDnoSD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 313
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 314: amoadd noLDnoSD mis+1
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 314
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 315: lr noLDnoSD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 315
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 316: sc noLDnoSD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 316
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 317: sc_resv noLDnoSD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 317
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 318: amoswap noLDnoSD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 318
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 319: amoadd noLDnoSD mis straddle
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 319
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 320: lr noLDnoSD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 320
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 321: sc noLDnoSD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 321
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 322: sc_resv noLDnoSD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 322
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 323: amoswap noLDnoSD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 323
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 324: amoadd noLDnoSD zero-len
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 324
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 325: lr noLDnoSD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 325
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 326: sc noLDnoSD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 326
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 327: sc_resv noLDnoSD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 327
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 328: amoswap noLDnoSD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 328
    csw x11, 60(c10)
    cincoffset c10, c10, 64
// ---- case 329: amoadd noLDnoSD len3
    csw zero, 0(c10)
    csw zero, 4(c10)
    li x13, 0
    li x8, 0x5a5a5a5a
    li x11, 0x80022ff0
    csetaddr c9, c6, x11
    .word 0x1804a02f
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
    li x12, 0x41
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
    li x11, 329
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
    li a0, 330
    cret

.globl rec_base
rec_base:
    cspecialr ca0, mtdc
    li a1, 0x80030000
    csetaddr ca0, ca0, a1
    cret
