// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.section .text
.globl _start

_start:
    cspecialw 25, c5
    cspecialw 26, c6

    li x6, 0x83800000
    csetaddr c5, c5, x6
    li x6, 0xd00d
    csw x6, 4(c5)        // mark that mtvec must not be reached now

    li x6, 0x800
    csrs mie, x6
    li x6, 0x8
    csrs mstatus, x6

    li x6, 0x3fffe
    csw x6, 264(c5)      // unmask the testbench external interrupt

    li x7, 1000
1:
    addi x7, x7, -1
    bnez x7, 1b

    li x6, 0x3ffff
    csw x6, 264(c5)      // mask all testbench interrupts
    li x6, 7
    csw x6, 260(c5)      // acknowledge a pending interrupt before returning
    csw x0, 4(c5)        // clear in-debug-ROM marker
    csw x0, 320(c5)      // deassert debug_req

    cspecialr c5, 25
    cspecialr c6, 26
    dret
