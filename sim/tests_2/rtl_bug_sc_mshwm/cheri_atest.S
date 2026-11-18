// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// KUDU-037: every store-type write into [MSHWMB, MSHWM) must lower MSHWM,
// including a successful sc.w.
// c10 = observation pointer, c11 = 16-byte aligned 16-byte block.
.option norelax
.option norvc
.section .text
.globl cheri_atest

// obs: 0 mshwm after the access, 4 block base, 8 rd, 12 memory word at +4
// op: 0 = lr.w + sc.w, 1 = csw, 2 = amoswap.w, 3 = sc.w without reservation
.macro CASE op
    cgetaddr t0, c11
    li t1, 0x11223344
    csw t1, 4(c11)              // initialise data (before MSHWM is armed)
    csw t0, 4(c10)
    li t1, 4
    cincoffset c14, c11, t1     // c14 -> block + 4
    csrw 0xbc2, t0              // mshwmb = block
    addi t1, t0, 16
    csrw 0xbc1, t1              // mshwm  = block + 16
    nop                         // keep clear of the KUDU-016 CSR/store window
    nop
    nop
    nop
    li t1, 0x5a5a5a5a
    li t2, 0xdeadbeef
.if \op == 0
    .word ((2 << 27) | (0 << 20) | (14 << 15) | (2 << 12) | (13 << 7) | 0x2f)  // lr.w a3, (c14)
    .word ((3 << 27) | (6 << 20) | (14 << 15) | (2 << 12) | (7 << 7) | 0x2f)   // sc.w t2, t1, (c14)
.elseif \op == 1
    csw t1, 0(c14)
.elseif \op == 2
    .word ((1 << 27) | (6 << 20) | (14 << 15) | (2 << 12) | (7 << 7) | 0x2f)   // amoswap.w t2, t1, (c14)
.else
    csw zero, 0(c10)            // outside the range: clears the reservation
    .word ((3 << 27) | (6 << 20) | (14 << 15) | (2 << 12) | (7 << 7) | 0x2f)   // sc.w t2, t1, (c14)
.endif
    csrr t1, 0xbc1
    li t0, -1
    csrw 0xbc2, t0              // disarm before recording results
    csrw 0xbc1, t0
    csw t1, 0(c10)
    csw t2, 8(c10)
    clw t1, 4(c11)
    csw t1, 12(c10)
    cincoffset c10, c10, 16
.endm

cheri_atest:
    cincoffset csp, csp, -16
    csrr t0, 0xbc1
    csw t0, 0(csp)
    csrr t0, 0xbc2
    csw t0, 4(csp)

    CASE 0
    CASE 1
    CASE 2
    CASE 3

    clw t0, 4(csp)
    csrw 0xbc2, t0
    clw t0, 0(csp)
    csrw 0xbc1, t0
    cincoffset csp, csp, 16
    cret
