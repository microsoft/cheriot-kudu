// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Programmable, register-transparent debug ROM for the debug review tests.
// Build with -DCHERIOT for PMODE=1 (SCR 24/25/26), without for PMODE=0
// (dpc/dscratch0/1). Uses x13/x14/x15 only (x13 saved in the mailbox).
// +0 DmHaltAddr, +8 DmExcAddr. Mailbox layout in dbg_mb.h.

#include "dbg_mb.h"

.option norvc
.option norelax
.section .text
.globl _start

#ifdef CHERIOT
#define LDW(rd, off, rb)  clw x##rd, off(c##rb)
#define STW(rs, off, rb)  csw x##rs, off(c##rb)
#define LHU(rd, off, rb)  clhu x##rd, off(c##rb)
#define SAVE13            csc c13, MB_SAVE_S1(c14)
#define REST13            clc c13, MB_SAVE_S1(c14)
#define SAVE1415          cspecialw 25, c14; cspecialw 26, c15
#define REST14            cspecialr c14, 25
#define REST15            cspecialr c15, 26
#define DPCRD(r)          cspecialr c##r, 24; cgetaddr x##r, c##r
// x13 is the temporary
#define DPCWR15           cspecialr c13, 24; csetaddr c13, c13, x15; cspecialw 24, c13
#define MEPCRD(r)         cspecialr c##r, mepcc; cgetaddr x##r, c##r
#define OTHER_MODE_OP     csrr x15, 0x7b1
#define ADDR15(l)         98: auipcc c15, %cheri_compartment_pccrel_hi(l); cincoffset c15, c15, %cheri_compartment_pccrel_lo(98b); cgetaddr x15, c15
#else
#define LDW(rd, off, rb)  lw x##rd, off(x##rb)
#define STW(rs, off, rb)  sw x##rs, off(x##rb)
#define LHU(rd, off, rb)  lhu x##rd, off(x##rb)
#define SAVE13            sw x13, MB_SAVE13(x14)
#define REST13            lw x13, MB_SAVE13(x14)
#define SAVE1415          csrw 0x7b2, x14; csrw 0x7b3, x15
#define REST14            csrr x14, 0x7b2
#define REST15            csrr x15, 0x7b3
#define DPCRD(r)          csrr x##r, 0x7b1
#define DPCWR15           csrw 0x7b1, x15
#define MEPCRD(r)         csrr x##r, mepc
// cspecialr c15, 24
#define OTHER_MODE_OP     .word 0x038007db
#define ADDR15(l)         lla x15, l
#endif

_start:
    j entry
    nop
    j dexc_handler

entry:
    SAVE1415
#ifdef CHERIOT
    // tagged mailbox capability derived from MTDC (root), so that csc/clc
    // of the saved c13 keep the tag
    cspecialr c14, 29
    li x15, 0x83800000
    csetaddr c14, c14, x15
    csw x0, 0x140(c14)              // debug_ack, deassert MMIO debug_req
    clw x15, 4(c14)                 // mailbox
    csetaddr c14, c14, x15
#else
    li x14, 0x83800000
    STW(0, 0x140, 14)               // debug_ack, deassert MMIO debug_req
    LDW(14, 4, 14)                  // mailbox
#endif
    SAVE13
    // re-entry from an ebreak executed inside the ROM (DEXC_OP 4)
    LDW(15, MB_DEXC_OP, 14)
    li x13, 0x44
    bne x15, x13, 1f
    csrr x15, 0x7b0
    STW(15, MB_EBRK_DCSR, 14)
    DPCRD(15)
    STW(15, MB_EBRK_DPC, 14)
    LDW(15, MB_EBRK_CNT, 14)
    addi x15, x15, 1
    STW(15, MB_EBRK_CNT, 14)
    STW(0, MB_DEXC_OP, 14)
    j rom_exit
1:
    LDW(15, MB_CNT, 14)
    addi x15, x15, 1
    STW(15, MB_CNT, 14)
    addi x15, x15, -1
    andi x15, x15, 31
    slli x15, x15, 4
    add x13, x14, x15
    addi x13, x13, MB_LOG
    csrr x15, 0x7b0
    STW(15, 0, 13)
    DPCRD(15)
    STW(15, 4, 13)
    csrr x15, mcause
    STW(15, 8, 13)
    STW(15, MB_PRE_MCAUSE, 14)
    MEPCRD(15)
    STW(15, 12, 13)
    STW(15, MB_PRE_MEPC, 14)
    csrr x15, mstatus
    STW(15, MB_PRE_MSTATUS, 14)
    csrr x15, mtval
    STW(15, MB_PRE_MTVAL, 14)
    csrr x15, mip
    STW(15, MB_MIP_DBG, 14)
#ifdef CHERIOT
    cspecialr c15, 24
    cgettag x13, c15
    STW(13, MB_DEPCC_TAG, 14)
    cgetbase x13, c15
    STW(13, MB_DEPCC_BASE, 14)
    cgetlen x13, c15
    STW(13, MB_DEPCC_LEN, 14)
    cgetperm x13, c15
    STW(13, MB_DEPCC_PERM, 14)
#endif
    LDW(15, MB_MSTATUS_SET, 14)
    csrs mstatus, x15
    // trigger hit: disable the trigger(s) matching dpc when ONESHOT
    csrr x15, 0x7b0
    srli x15, x15, 6
    andi x15, x15, 7
    addi x15, x15, -2
    bnez x15, 2f
    LDW(15, MB_TRIG_ONESHOT, 14)
    beqz x15, 2f
    csrwi 0x7a0, 0
    csrr x15, 0x7a2
    DPCRD(13)
    bne x15, x13, 21f
    csrwi 0x7a1, 0
21: csrwi 0x7a0, 1
    csrr x15, 0x7a2
    DPCRD(13)
    bne x15, x13, 22f
    csrwi 0x7a1, 0
22: csrwi 0x7a0, 0
2:
    // dcsr modifications
    LDW(15, MB_OR, 14)
    csrs 0x7b0, x15
    LDW(15, MB_ANDN, 14)
    csrc 0x7b0, x15
    // ebreak entry: skip the ebreak
    csrr x15, 0x7b0
    srli x15, x15, 6
    andi x15, x15, 7
    addi x15, x15, -1
    bnez x15, 3f
    DPCRD(15)
    LHU(13, 0, 15)
    andi x13, x13, 3
    addi x13, x13, -3
    addi x15, x15, 2
    bnez x13, 31f
    addi x15, x15, 2
31: DPCWR15
3:
    // skip one instruction (4 bytes) at SKIP_AT
    LDW(15, MB_SKIP_AT, 14)
    beqz x15, 4f
    DPCRD(13)
    bne x13, x15, 4f
    addi x15, x15, 4
    DPCWR15
    LDW(15, MB_SKIP_HIT, 14)
    addi x15, x15, 1
    STW(15, MB_SKIP_HIT, 14)
4:
    // stop stepping at STEP_STOP
    LDW(15, MB_STEP_STOP, 14)
    beqz x15, 5f
    DPCRD(13)
    bne x13, x15, 5f
    csrci 0x7b0, 4
    LDW(13, MB_OR, 14)
    andi x13, x13, -5
    STW(13, MB_OR, 14)
    STW(0, MB_STEP_STOP, 14)
5:
    // new dpc
    LDW(15, MB_NEWDPC, 14)
    beqz x15, 6f
    DPCWR15
    STW(0, MB_NEWDPC, 14)
6:
#ifdef CHERIOT
    LDW(15, MB_DEPCC_CLRTAG, 14)
    beqz x15, 61f
    STW(0, MB_DEPCC_CLRTAG, 14)
    cspecialr c15, 24
    ccleartag c15, c15
    cspecialw 24, c15
61:
#endif
    // triggers
    LDW(15, MB_TRIG_APPLY, 14)
    beqz x15, 7f
    STW(0, MB_TRIG_APPLY, 14)
    csrwi 0x7a0, 0
    LDW(15, MB_T0_D1, 14)
    csrw 0x7a1, x15
    LDW(15, MB_T0_D2, 14)
    csrw 0x7a2, x15
    csrr x15, 0x7a1
    STW(15, MB_TRIG_RB0, 14)
    csrwi 0x7a0, 1
    LDW(15, MB_T1_D1, 14)
    csrw 0x7a1, x15
    LDW(15, MB_T1_D2, 14)
    csrw 0x7a2, x15
    csrwi 0x7a0, 5
    csrr x15, 0x7a0
    STW(15, MB_TRIG_RB1, 14)
    csrwi 0x7a0, 0
7:
    // spin inside debug mode (lets a pending interrupt sit), then sample mip
    LDW(15, MB_SPIN, 14)
    beqz x15, 8f
71: addi x15, x15, -1
    bnez x15, 71b
    csrr x15, mip
    STW(15, MB_MIP_DBG, 14)
    STW(0, MB_SPIN, 14)
8:
    // exception inside debug mode
    LDW(13, MB_DEXC_OP, 14)
    beqz x13, dexc_resume
    li x15, 1
    beq x13, x15, op_ill
    li x15, 2
    beq x13, x15, op_ecall
    li x15, 3
    beq x13, x15, op_ldfault
    li x15, 4
    beq x13, x15, op_ebreak
    li x15, 5
    beq x13, x15, op_other
    li x15, 6
    beq x13, x15, op_trig
    j dexc_resume
op_ill:
    .word 0
    j dexc_resume
op_ecall:
    ecall
    j dexc_resume
op_ldfault:
    li x15, 0x90000000
    LDW(15, 0, 15)
    j dexc_resume
op_other:
    OTHER_MODE_OP
    j dexc_resume
op_trig:
    // trigger 0 on rom_tnop; must not fire in debug mode
    csrwi 0x7a0, 0
    li x15, TDATA1_EXEC
    csrw 0x7a1, x15
    ADDR15(rom_tnop)
    csrw 0x7a2, x15
    nop
rom_tnop:
    addi x15, x15, 1
    csrwi 0x7a1, 0
    LDW(13, MB_W3, 14)
    addi x13, x13, 1
    STW(13, MB_W3, 14)
    j dexc_resume
op_ebreak:
    // restore the user's registers, then ebreak: re-enters at +0 (see above)
    li x15, 0x44
    STW(15, MB_DEXC_OP, 14)
    REST13
    REST14
    REST15
    ebreak
    // not expected: ebreak in debug mode must re-enter the ROM
    li x14, 0x83800000
    LDW(14, 4, 14)
    li x15, 0x77
    STW(15, MB_EBRK_CNT, 14)
    j rom_exit

dexc_handler:
    LDW(15, MB_DEXC_CNT, 14)
    addi x15, x15, 1
    STW(15, MB_DEXC_CNT, 14)
    csrr x15, 0x7b0
    STW(15, MB_DEXC_DCSR, 14)
    DPCRD(15)
    STW(15, MB_DEXC_DPC, 14)
    csrr x15, mcause
    STW(15, MB_DEXC_MCAUSE, 14)
    MEPCRD(15)
    STW(15, MB_DEXC_MEPC, 14)
    csrr x15, mstatus
    STW(15, MB_DEXC_MSTATUS, 14)
    csrr x15, mtval
    STW(15, MB_DEXC_MTVAL, 14)
dexc_resume:
    STW(0, MB_DEXC_OP, 14)

rom_exit:
    LDW(15, MB_HALT_ON_EXIT, 14)
    beqz x15, 91f
    addi x15, x15, -1
    STW(15, MB_HALT_ON_EXIT, 14)
    li x15, 1
    li x13, 0x83800000
    STW(15, 0x140, 13)
91:
    LDW(15, MB_EXIT_MODE, 14)
    STW(0, MB_EXIT_MODE, 14)
    li x13, 1
    beq x15, x13, exit_dpc
    li x13, 2
    beq x15, x13, exit_dcsr
    REST13
    REST14
    REST15
    dret

// csrw dpc / cspecialw depcc immediately before dret (x14 is clobbered)
exit_dpc:
    LDW(15, MB_EXIT_VAL, 14)
    REST13
#ifdef CHERIOT
    cspecialr c14, 24
    csetaddr c14, c14, x15
    REST15
    cspecialw 24, c14
#else
    mv x14, x15
    REST15
    csrw 0x7b1, x14
#endif
    dret

// csrw dcsr immediately before dret (x14 is clobbered)
exit_dcsr:
    csrr x15, 0x7b0
    LDW(13, MB_EXIT_ANDN, 14)
    not x13, x13
    and x15, x15, x13
    LDW(13, MB_EXIT_VAL, 14)
    or x15, x15, x13
    REST13
    mv x14, x15
    REST15
    csrw 0x7b0, x14
    dret
