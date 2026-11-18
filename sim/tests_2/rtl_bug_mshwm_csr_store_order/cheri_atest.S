// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Each case: program MSHWMB/MSHWM and let them settle, then execute
//   older store -> csrw MSHWM/MSHWMB -> store into the stack area
// With an older store in flight, the younger store issues in the same cycle
// the CSR write commits, so Kudu checks it against the stale MSHWM/MSHWMB.
// results[i] = MSHWM read back after the sequence has fully retired.
.option norelax
.option norvc
.section .text
.globl cheri_atest

.macro SETTLE
    addi x0, x0, 0
    addi x0, x0, 0
    addi x0, x0, 0
    addi x0, x0, 0
    addi x0, x0, 0
    addi x0, x0, 0
.endm

.macro PROLOGUE b, w
    csrw 0xbc2, \b
    csrw 0xbc1, \w
    SETTLE
.endm

.macro OLDER_STORE
    mul t0, t1, t1
    csw t0, 60(c10)
.endm

.macro RECORD off
    SETTLE
    csrr t0, 0xbc1
    csw t0, \off(c10)
.endm

cheri_atest:
    // a0 = results capability, a1 = 256-byte, 16-byte aligned area capability
    cmove c10, ca0
    cgetaddr t1, ca1          // base
    addi t2, t1, 64           // base+64
    addi a2, t1, 128          // base+128
    addi a3, t1, 256          // base+256 (top)

    // case 0: MSHWM = base+64, raise MSHWM to base+256, store at base+100.
    // MSHWM must become base+96.
    PROLOGUE t1, t2
    OLDER_STORE
    csrw 0xbc1, a3
    csw zero, 100(ca1)
    RECORD 0

    // case 1: MSHWM = base+256, raise MSHWMB to base+128, store at base+100.
    // 100 < MSHWMB, so MSHWM must stay base+256.
    PROLOGUE t1, a3
    OLDER_STORE
    csrw 0xbc2, a2
    csw zero, 100(ca1)
    RECORD 4

    // case 2: case 0 with MSHWMB and MSHWM written back to back.
    PROLOGUE t1, t2
    OLDER_STORE
    csrw 0xbc2, t1
    csrw 0xbc1, a3
    csw zero, 100(ca1)
    RECORD 8

    // case 3: case 0 with a capability store at base+96.
    PROLOGUE t1, t2
    OLDER_STORE
    csrw 0xbc1, a3
    csc cnull, 96(ca1)
    RECORD 12

    // case 4 (control): case 0 without the older store.
    PROLOGUE t1, t2
    csrw 0xbc1, a3
    csw zero, 100(ca1)
    RECORD 16

    // case 5 (control): case 0 with a gap before the younger store.
    PROLOGUE t1, t2
    OLDER_STORE
    csrw 0xbc1, a3
    SETTLE
    csw zero, 100(ca1)
    RECORD 20

    cret
