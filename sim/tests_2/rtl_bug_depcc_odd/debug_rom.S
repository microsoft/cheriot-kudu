// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Debug ROM for rtl_bug_depcc_odd. Build with -DCHERIOT for PMODE=1
// (DEPCC = SCR 24, DSCRATCHC0/1 = SCR 25/26), without for PMODE=0 / RV32
// (dpc/dscratch0/1). Register-transparent: x14/x15 are saved in the debug
// scratch registers, x13 in the mailbox.
//
// The test writes the address of its mailbox to TB scratch_reg1
// (0x8380_0004). Mailbox (32-bit words, 16-byte aligned): 0 entries,
// 1 dpc read back after the odd write, 2 tag of the read-back DEPCC
// (CHERIoT only), 3 odd address written, 4-5 saved DEPCC/dpc, 6-7 saved x13.
// Only the first entry after the mailbox is set runs the check; it restores
// the original DEPCC/dpc before dret. Requests that arrive before the mailbox
// is set (scratch_reg1 == 0) are only acked.

.option norvc
.option norelax
.section .text
.globl _start

#ifdef CHERIOT
#define LDW(rd, off, rb)  clw x##rd, off(c##rb)
#define STW(rs, off, rb)  csw x##rs, off(c##rb)
#define SAVE              cspecialw 25, c14; cspecialw 26, c15
#define RESTORE           cspecialr c14, 25; cspecialr c15, 26
#else
#define LDW(rd, off, rb)  lw x##rd, off(x##rb)
#define STW(rs, off, rb)  sw x##rs, off(x##rb)
#define SAVE              csrw 0x7b2, x14; csrw 0x7b3, x15
#define RESTORE           csrr x14, 0x7b2; csrr x15, 0x7b3
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
    addi x15, x15, -1
    bnez x15, done           // check only on the first entry

#ifdef CHERIOT
    csc c13, 24(c14)
    cspecialr c15, 24        // original DEPCC
    csc c15, 16(c14)
    cgetaddr x13, c15
    ori x13, x13, 1
    csw x13, 12(c14)         // odd address written
    csetaddr c13, c15, x13
    cspecialw 24, c13        // DEPCC <- odd address
    cspecialr c13, 24
    cgetaddr x15, c13
    csw x15, 4(c14)          // DEPCC address read back
    cgettag x15, c13
    csw x15, 8(c14)          // DEPCC tag read back
    clc c15, 16(c14)
    cspecialw 24, c15        // restore the original DEPCC
    clc c13, 24(c14)
#else
    sw x13, 24(x14)
    csrr x15, 0x7b1          // original dpc
    sw x15, 16(x14)
    ori x13, x15, 1
    sw x13, 12(x14)          // odd address written
    csrw 0x7b1, x13          // dpc <- odd address
    csrr x15, 0x7b1
    sw x15, 4(x14)           // dpc read back
    lw x15, 16(x14)
    csrw 0x7b1, x15          // restore the original dpc
    lw x13, 24(x14)
#endif
done:
    RESTORE
    dret
