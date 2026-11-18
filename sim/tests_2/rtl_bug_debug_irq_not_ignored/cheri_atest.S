// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.section .text
.globl cheri_atest

.macro UART_CHAR value
    li x11, \value
    csw x11, 512(c5)
.endm

.macro PRINT_FAIL
    UART_CHAR 'D'
    UART_CHAR 'E'
    UART_CHAR 'B'
    UART_CHAR 'U'
    UART_CHAR 'G'
    UART_CHAR ' '
    UART_CHAR 'I'
    UART_CHAR 'R'
    UART_CHAR 'Q'
    UART_CHAR ' '
    UART_CHAR 'F'
    UART_CHAR 'A'
    UART_CHAR 'I'
    UART_CHAR 'L'
    UART_CHAR ' '
    UART_CHAR 'c'
    UART_CHAR 'a'
    UART_CHAR 's'
    UART_CHAR 'e'
    UART_CHAR 's'
    UART_CHAR '='
    UART_CHAR '0'
    UART_CHAR 'x'
    UART_CHAR '0'
    UART_CHAR '0'
    UART_CHAR '0'
    UART_CHAR '0'
    UART_CHAR '0'
    UART_CHAR '0'
    UART_CHAR '0'
    UART_CHAR '1'
    UART_CHAR 10
.endm

cheri_atest:
    cincoffset csp, csp, -48
    csc c1, 0(csp)
    csc c3, 8(csp)
    csc c5, 16(csp)
    csc c8, 24(csp)
    csc c11, 32(csp)
    csc c12, 40(csp)

    cspecialr c3, mtdc
    li x11, 0x83800000
    csetaddr c5, c3, x11
    csetboundsimm c5, c5, 0x800
    li x11, 0x24
    candperm c5, c5, x11

1:  auipcc c8, %cheri_compartment_pccrel_hi(debug_irq_mtvec)
    cincoffset c8, c8, %cheri_compartment_pccrel_lo(1b)
    cspecialw mtcc, c8

    csw x0, 4(c5)        // scratch1: in-debug-ROM marker
    li x11, 0x3ffff
    csw x11, 264(c5)     // TB interrupts masked until debug mode
    li x11, 7
    csw x11, 260(c5)     // acknowledge any stale interrupt

    li x11, 0x800        // MEIE
    csrs mie, x11
    li x11, 0x8          // mstatus.MIE
    csrs mstatus, x11

    li x11, 1
    csw x11, 320(c5)     // request debug entry; debug ROM does the check

    li x12, 4000
wait_debug_return:
    addi x12, x12, -1
    bnez x12, wait_debug_return

    li a0, 0
    clc c1, 0(csp)
    clc c3, 8(csp)
    clc c5, 16(csp)
    clc c8, 24(csp)
    clc c11, 32(csp)
    clc c12, 40(csp)
    cincoffset csp, csp, 48
    cret

.align 4
debug_irq_mtvec:
    li x11, 0x83800000
    csetaddr c5, c5, x11
    clw x10, 4(c5)
    li x11, 0xd00d
    bne x10, x11, normal_irq

    PRINT_FAIL
    li x11, 0xff
    csw x11, 512(c5)
fail_halt:
    j fail_halt

normal_irq:
    li x11, 7
    csw x11, 260(c5)
    mret
