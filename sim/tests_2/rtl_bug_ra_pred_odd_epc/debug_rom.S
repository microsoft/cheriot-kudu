// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Debug ROM for rtl_bug_ra_pred_odd_epc. Build with -DCHERIOT for PMODE=1
// (DEPCC = SCR 24, DSCRATCHC0/1 = SCR 25/26), without for PMODE=0 / RV32
// (dpc/dscratch0/1). Register-transparent: uses x14/x15 only.
//
// The test writes the address of its mailbox to TB scratch_reg1
// (0x8380_0004). Mailbox (32-bit words): 0 entries, 1 entries with an odd
// dpc, 2 first odd dpc. An odd dpc is cleared to even before dret. Requests
// that arrive before the mailbox is set (scratch_reg1 == 0) are only acked.

.option norvc
.option norelax
.section .text
.globl _start

#ifdef CHERIOT
#define LDW(rd, off, rb)  clw x##rd, off(c##rb)
#define STW(rs, off, rb)  csw x##rs, off(c##rb)
#define SAVE              cspecialw 25, c14; cspecialw 26, c15
#define RESTORE           cspecialr c14, 25; cspecialr c15, 26
#define DPCRD15           cspecialr c15, 24; cgetaddr x15, c15
#define DPCWR15           cspecialr c14, 24; csetaddr c14, c14, x15; cspecialw 24, c14
#else
#define LDW(rd, off, rb)  lw x##rd, off(x##rb)
#define STW(rs, off, rb)  sw x##rs, off(x##rb)
#define SAVE              csrw 0x7b2, x14; csrw 0x7b3, x15
#define RESTORE           csrr x14, 0x7b2; csrr x15, 0x7b3
#define DPCRD15           csrr x15, 0x7b1
#define DPCWR15           csrw 0x7b1, x15
#endif

_start:
    j entry
    nop
dexc:
    j dexc                   // exception inside the ROM: hang (test times out)

entry:
    SAVE
#ifdef CHERIOT
    cspecialr c14, 29        // MTDC (root) for the MMIO and mailbox accesses
    li x15, 0x83800000
    csetaddr c14, c14, x15
    csw x0, 0x140(c14)       // debug_ack, deassert debug_req
    clw x15, 4(c14)          // mailbox
    beqz x15, done           // request before the test set up its mailbox
    csetaddr c14, c14, x15
#else
    li x14, 0x83800000
    STW(0, 0x140, 14)        // debug_ack, deassert debug_req
    LDW(14, 4, 14)           // mailbox
    beqz x14, done           // request before the test set up its mailbox
#endif
    LDW(15, 0, 14)
    addi x15, x15, 1
    STW(15, 0, 14)           // entries++
    DPCRD15
    andi x15, x15, 1
    beqz x15, done
    LDW(15, 4, 14)
    bnez x15, 1f
    DPCRD15
    STW(15, 8, 14)           // first odd dpc
1:  LDW(15, 4, 14)
    addi x15, x15, 1
    STW(15, 4, 14)           // odd entries++
    DPCRD15
    andi x15, x15, -2
    DPCWR15
done:
    RESTORE
    dret
