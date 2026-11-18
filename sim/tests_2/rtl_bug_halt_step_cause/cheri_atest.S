// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Every case writes the mailbox address to TB scratch_reg1 (0x8380_0004) and
// raises debug_req (0x8380_0140). The debug ROM preserves all registers.

.option norvc

.section .text
.globl install_handler
.type install_handler, @function
.globl halt_only
.type halt_only, @function
.globl step_nop
.type step_nop, @function
.globl step_haltreq
.type step_haltreq, @function

// Common prologue: c13 = TB register block, scratch_reg1 = mailbox (c10).
.macro TB_SETUP
    cspecialr c13, mtdc
    li x14, 0x83800000
    csetaddr c13, c13, x14
    cgetaddr x14, c10
    csw x14, 4(c13)
.endm

// mb[16] = address of \label (the instruction the ROM resumes at with step=1)
.macro SET_TARGET label
91: auipcc c11, %cheri_compartment_pccrel_hi(\label)
    cincoffset c11, c11, %cheri_compartment_pccrel_lo(91b)
    cgetaddr x11, c11
    csw x11, 64(c10)
.endm

.macro RAISE_DEBUG_REQ
    li x14, 1
    csw x14, 320(c13)
.endm

install_handler:
1:  auipcc c10, %cheri_compartment_pccrel_hi(trap_handler)
    cincoffset c10, c10, %cheri_compartment_pccrel_lo(1b)
    cspecialw mtcc, c10
    cret

// H3 (control): a plain halt request reports cause HALTREQ.
halt_only:
    TB_SETUP
    RAISE_DEBUG_REQ
    li x14, 300
1:  addi x14, x14, -1
    bnez x14, 1b
    li x10, 0
    cret

// H2 (control): step a nop; cause STEP, dpc = target + 4.
step_nop:
    TB_SETUP
    SET_TARGET 2f
    RAISE_DEBUG_REQ
1:  j 1b
2:  addi x15, x15, 1
    li x10, 0
    cret

// H1: the stepped instruction is the store that raises debug_req again
// (x14 = 1). When the step completes a halt request is also pending, so the
// re-entry must report cause HALTREQ (3), which has priority over STEP (4).
step_haltreq:
    TB_SETUP
    SET_TARGET 2f
    RAISE_DEBUG_REQ
1:  j 1b
2:  csw x14, 320(c13)        // stepped: debug_req = 1
    li x10, 0
    cret

// No trap is expected. Count it in mb[12] and end the simulation.
.p2align 2
trap_handler:
    cspecialr c6, mtdc
    li x7, 0x83800200
    csetaddr c6, c6, x7
    li x7, 'T'
    csw x7, 0(c6)
    li x7, 'R'
    csw x7, 0(c6)
    li x7, 'A'
    csw x7, 0(c6)
    li x7, 'P'
    csw x7, 0(c6)
    li x7, ' '
    csw x7, 0(c6)
    li x7, 'F'
    csw x7, 0(c6)
    li x7, 'A'
    csw x7, 0(c6)
    li x7, 'I'
    csw x7, 0(c6)
    li x7, 'L'
    csw x7, 0(c6)
    li x7, 10
    csw x7, 0(c6)
    li x7, 0xff
    csw x7, 0(c6)
1:  j 1b
