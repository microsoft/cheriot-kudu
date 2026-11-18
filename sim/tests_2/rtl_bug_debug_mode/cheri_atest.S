// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.section .text
.globl install_mtcc
.globl dbg_case
.globl clc_probe
.globl pcc_probe

// MTCC = dbg_mtvec, bounded to 256 bytes so that a PCC derived from it is
// easy to recognise.
install_mtcc:
1:  auipcc c10, %cheri_compartment_pccrel_hi(dbg_mtvec)
    cincoffset c10, c10, %cheri_compartment_pccrel_lo(1b)
    li x11, 256
    csetbounds c10, c10, x11
    cspecialw mtcc, c10
    cret

// void dbg_case(int case, volatile int *mb, void **buf)
// Raises debug_req and waits for the debug ROM to return. The ROM and the
// mtvec handler may clobber t0-t2 and a0-a5; c8/c9 carry the CLC
// authorities into debug mode (no-MC and no-LM views of buf).
dbg_case:
    cincoffset csp, csp, -16
    csc c8, 0(csp)
    csc c9, 8(csp)

    csw x10, 0(c11)          // mb[0] = case
    li x13, 0xfbf
    candperm c8, c12, x13    // clear MC
    li x13, 0xff7
    candperm c9, c12, x13    // clear LM

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

    clc c8, 0(csp)
    clc c9, 8(csp)
    cincoffset csp, csp, 16
    cret

// void clc_probe(void **buf, volatile int *out)
// Normal-mode baseline for the debug-mode CLC case.
clc_probe:
    li x13, 0xfbf
    candperm c12, c10, x13
    clc c13, 0(c12)
    cgettag x14, c13
    csw x14, 0(c11)          // tag via no-MC authority
    li x13, 0xff7
    candperm c12, c10, x13
    clc c13, 0(c12)
    cgetperm x14, c13
    csw x14, 4(c11)          // perms via no-LM authority
    cgettag x14, c13
    csw x14, 8(c11)          // tag via no-LM authority
    cret

// void pcc_probe(volatile int *out)
pcc_probe:
    auipcc c11, 0
    cgetbase x12, c11
    csw x12, 0(c10)
    cgetlen x12, c11
    csw x12, 4(c10)
    cgetperm x12, c11
    csw x12, 8(c10)
    cgettag x12, c11
    csw x12, 12(c10)
    cspecialr c11, mtcc
    cgetbase x12, c11
    csw x12, 16(c10)
    cgetlen x12, c11
    csw x12, 20(c10)
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
