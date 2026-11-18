// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.option push
.option rvc

// a0=seed, a1=operand, a2=operation, a3=result pointer, a4=writable mask.
// No loads/stores/calls occur until the original CSR is restored. This matters
// for the live trap vector and for the store-sensitive watermark registers.
.macro PATTERN_ACCESS name, csr
.globl csr_pattern_\name
.type csr_pattern_\name, @function
csr_pattern_\name:
    csrr t0, \csr
    not t1, a4
    and t1, t0, t1
    and a0, a0, a4
    or a0, a0, t1
    csrw \csr, a0
    csrr a4, \csr
    beqz a2, .Lset\@
    li t1, 1
    beq a2, t1, .Lclear\@
    li t1, 2
    beq a2, t1, .Lseti0\@
    li t1, 3
    beq a2, t1, .Lcleari0\@
    li t1, 4
    beq a2, t1, .Lseti1\@
    li t1, 5
    beq a2, t1, .Lcleari1\@
    li t1, 6
    beq a2, t1, .Lseti8\@
    li t1, 7
    beq a2, t1, .Lcleari8\@
    li t1, 8
    beq a2, t1, .Lseti16\@
    li t1, 9
    beq a2, t1, .Lcleari16\@
    li t1, 10
    beq a2, t1, .Lseti21\@
    li t1, 11
    beq a2, t1, .Lcleari21\@
    li t1, 12
    beq a2, t1, .Lseti31\@
    li t1, 13
    beq a2, t1, .Lcleari31\@
    li t1, 14
    beq a2, t1, .Lreadset\@
    csrrc t1, \csr, zero
    j .Ldone\@
.Lreadset\@:
    csrrs t1, \csr, zero
    j .Ldone\@
.Lset\@:
    csrrs t1, \csr, a1
    j .Ldone\@
.Lclear\@:
    csrrc t1, \csr, a1
    j .Ldone\@
.Lseti0\@:
    csrrsi t1, \csr, 0
    j .Ldone\@
.Lcleari0\@:
    csrrci t1, \csr, 0
    j .Ldone\@
.Lseti1\@:
    csrrsi t1, \csr, 1
    j .Ldone\@
.Lcleari1\@:
    csrrci t1, \csr, 1
    j .Ldone\@
.Lseti8\@:
    csrrsi t1, \csr, 8
    j .Ldone\@
.Lcleari8\@:
    csrrci t1, \csr, 8
    j .Ldone\@
.Lseti16\@:
    csrrsi t1, \csr, 16
    j .Ldone\@
.Lcleari16\@:
    csrrci t1, \csr, 16
    j .Ldone\@
.Lseti21\@:
    csrrsi t1, \csr, 21
    j .Ldone\@
.Lcleari21\@:
    csrrci t1, \csr, 21
    j .Ldone\@
.Lseti31\@:
    csrrsi t1, \csr, 31
    j .Ldone\@
.Lcleari31\@:
    csrrci t1, \csr, 31
    j .Ldone\@
.Ldone\@:
    csrr t2, \csr
    csrw \csr, t0
    csrr a0, \csr
#ifdef CHERIOT
    csw t0, 0(ca3)
    csw a4, 4(ca3)
    csw t1, 8(ca3)
    csw t2, 12(ca3)
    csw a0, 16(ca3)
    cret
#else
    sw t0, 0(a3)
    sw a4, 4(a3)
    sw t1, 8(a3)
    sw t2, 12(a3)
    sw a0, 16(a3)
    ret
#endif
.size csr_pattern_\name, .-csr_pattern_\name
.endm

PATTERN_ACCESS status, 0x300
PATTERN_ACCESS isa, 0x301
PATTERN_ACCESS ie, 0x304
PATTERN_ACCESS counteren, 0x306
PATTERN_ACCESS inhibit, 0x320
PATTERN_ACCESS scratch, 0x340
PATTERN_ACCESS cause, 0x342
PATTERN_ACCESS tval, 0x343
PATTERN_ACCESS ip, 0x344
PATTERN_ACCESS tselect, 0x7a0
PATTERN_ACCESS tdata1, 0x7a1
PATTERN_ACCESS tdata2, 0x7a2
PATTERN_ACCESS tdata3, 0x7a3
PATTERN_ACCESS mcontext, 0x7a8
PATTERN_ACCESS scontext, 0x7aa
PATTERN_ACCESS control, 0x7c0
PATTERN_ACCESS seed, 0x7c1
PATTERN_ACCESS cycle, 0xb00
PATTERN_ACCESS cycleh, 0xb80
PATTERN_ACCESS instret, 0xb02
PATTERN_ACCESS instreth, 0xb82
#ifdef CHERIOT
PATTERN_ACCESS watermark, 0xbc1
PATTERN_ACCESS watermarkbase, 0xbc2
PATTERN_ACCESS watermarkcontrol, 0xbc4
#else
PATTERN_ACCESS vector, 0x305
PATTERN_ACCESS epc, 0x341
#endif
.balign 4
.option pop
