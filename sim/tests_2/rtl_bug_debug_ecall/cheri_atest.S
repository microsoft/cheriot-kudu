// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.section .text
.globl install_mtcc
.globl dbg_case

// MTCC = dbg_mtvec.
install_mtcc:
1:  auipcc c10, %cheri_compartment_pccrel_hi(dbg_mtvec)
    cincoffset c10, c10, %cheri_compartment_pccrel_lo(1b)
    cspecialw mtcc, c10
    cret

// void dbg_case(int case, volatile int *mb)
// Raises debug_req and waits for the debug ROM to return. The ROM and the
// mtvec handler may clobber t0-t2 and a0-a5.
dbg_case:
    csw x10, 0(c11)          // mb[0] = case
    li x14, 5
    csrw mcause, x14         // known mcause (load access fault)
    auipcc c14, 0
    cspecialw mepcc, c14     // known MEPCC
    cspecialr c13, mtdc
    li x14, 0x83800000
    csetaddr c13, c13, x14
    cgetaddr x14, c11
    csw x14, 4(c13)          // scratch_reg1 = mailbox address
    li x14, 1
    csw x14, 320(c13)        // debug_req = 1

    li x15, 3000
2:  addi x15, x15, -1
    bnez x15, 2b
    cret

// Trap handler. A trap taken while the debug ROM runs (in-ROM flag set) is
// recorded and returned from with dret. Any other trap ends the simulation.
.p2align 2
dbg_mtvec:
    cspecialr c6, mtdc
    li x7, 0x83800000
    csetaddr c6, c6, x7
    clw x7, 4(c6)
    csetaddr c6, c6, x7      // c6 = mailbox
    clw x7, 12(c6)
    addi x7, x7, 1
    csw x7, 12(c6)           // mtvec hits++
    csrr x7, mcause
    csw x7, 52(c6)           // mb[13]
    cspecialr c7, mepcc
    cgetaddr x7, c7
    csw x7, 56(c6)           // mb[14]
    clw x7, 8(c6)
    beqz x7, unexpected_trap
    csw x0, 8(c6)            // leave the "ROM" context
    .word 0x7b200073         // dret

unexpected_trap:
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
    li x7, 10
    csw x7, 0(c6)
    li x7, 0xff
    csw x7, 0(c6)
1:  j 1b
