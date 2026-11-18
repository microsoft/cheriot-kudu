// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Common part of the directed debug tests. ISA-specific macros come from
// the wrapper (rv32_atest.S / cheri_atest.S). Registers: x8 = MMIO/root
// pointer (0x8380_0000), x9 = mailbox pointer, x10/x11/x12 = checker.

#include "dbg_mb.h"

.option norelax
.option norvc
.section .text
.globl run_case

#define AMO(f5, rd, rs2, rs1) .word (((f5) << 27) | ((rs2) << 20) | ((rs1) << 15) | (2 << 12) | ((rd) << 7) | 0x2f)
#define DRET .word 0x7b200073

.macro CHK id
    beq x10, x11, .Lok\@
    LDW(12, MB_NFAIL, 9)
    bnez x12, .Lnf\@
    li x12, \id
    STW(12, MB_FID, 9)
    STW(10, MB_FGOT, 9)
    STW(11, MB_FEXP, 9)
    LDW(12, MB_NFAIL, 9)
.Lnf\@:
    addi x12, x12, 1
    STW(12, MB_NFAIL, 9)
.Lok\@:
.endm

// mailbox word == imm
.macro CHKM id, off, imm
    LDW(10, \off, 9)
    li x11, \imm
    CHK \id
.endm

// mailbox word == address of label + add
.macro CHKML id, off, lbl, add=0
    LDW(10, \off, 9)
    LAI(11, \lbl)
    addi x11, x11, \add
    CHK \id
.endm

// mailbox word a == mailbox word b
.macro CHKMM id, offa, offb
    LDW(10, \offa, 9)
    LDW(11, \offb, 9)
    CHK \id
.endm

.macro CHKREG id, reg, imm
    mv x10, x\reg
    li x11, \imm
    CHK \id
.endm

// log entry k: dcsr.cause
.macro CHKCAUSE id, k, cause
    LDW(10, LOGOFF(\k, 0), 9)
    srli x10, x10, 6
    andi x10, x10, 7
    li x11, \cause
    CHK \id
.endm

// log entry k: dcsr.prv
.macro CHKPRV id, k, prv
    LDW(10, LOGOFF(\k, 0), 9)
    andi x10, x10, 3
    li x11, \prv
    CHK \id
.endm

// log entry k: dpc == label + add
.macro CHKDPC id, k, lbl, add=0
    LDW(10, LOGOFF(\k, 1), 9)
    LAI(11, \lbl)
    addi x11, x11, \add
    CHK \id
.endm

// log entry k: dpc == label and cause == STEP
.macro STEPCHK id, k, lbl
    CHKDPC \id, \k, \lbl
    CHKCAUSE \id+500, \k, 4
.endm

// lo <= mailbox word < hi
.macro CHKRANGE id, off, lo, hi
    LDW(10, \off, 9)
    LAI(11, \lo)
    bltu x10, x11, .Lf\@
    LAI(11, \hi)
    bltu x10, x11, .Lp\@
.Lf\@:
    li x11, -1
    CHK \id
.Lp\@:
.endm

.macro SETMB off, imm
    li x5, \imm
    STW(5, \off, 9)
.endm

.macro SETMBL off, lbl, add=0
    LAI(5, \lbl)
    addi x5, x5, \add
    STW(5, \off, 9)
.endm

// raise a halt request, wait (with timeout) until the ROM count reaches n
.macro HALT_WAIT id, n
    li x5, 1
    STW(5, 0x140, 8)
    li x7, 20000
.Lw\@:
    LDW(5, MB_CNT, 9)
    li x6, \n
    bgeu x5, x6, .Ld\@
    addi x7, x7, -1
    bnez x7, .Lw\@
    li x10, 0xdead
    li x11, 0
    CHK \id
.Ld\@:
.endm

// wait (with timeout) until the ROM count reaches n
.macro WAIT_CNT id, n
    li x7, 20000
.Lw\@:
    LDW(5, MB_CNT, 9)
    li x6, \n
    bgeu x5, x6, .Ld\@
    addi x7, x7, -1
    bnez x7, .Lw\@
    li x10, 0xdead
    li x11, 0
    CHK \id
.Ld\@:
.endm

// enter debug once to set dcsr bits (ebreakm etc.), then reset the count
.macro DBG_SETUP orv
    SETMB MB_OR, \orv
    CALL(dbg_halt)
    STW(0, MB_CNT, 9)
    SETMB MB_OR, ((\orv) & ~3)
.endm

// enter single-step via an ebreak (ebreakm), stepping until dpc == stop
.macro STEP_BEGIN stop, andn=0
    DBG_SETUP (DCSR_EBREAKM | 3)
    SETMB MB_OR, (DCSR_EBREAKM | DCSR_STEP)
    SETMB MB_ANDN, \andn
    SETMBL MB_STEP_STOP, \stop
    ebreak
.endm

.macro TO_U lbl
    LAI(5, \lbl)
    SETMEPC(5)
    li x5, 0x1800
    csrc mstatus, x5
    mret
.endm

.macro SET_TRIG t0, t1
    SETMB MB_TRIG_APPLY, 1
    SETMB MB_TRIG_ONESHOT, 1
.ifnc \t0, none
    SETMB MB_T0_D1, TDATA1_EXEC
    SETMBL MB_T0_D2, \t0
.endif
.ifnc \t1, none
    SETMB MB_T1_D1, TDATA1_EXEC
    SETMBL MB_T1_D2, \t1
.endif
.endm

.macro IRQ_SW_PENDING id
    csrci mstatus, 8
    li x5, 8
    csrw mie, x5
    li x5, 0x3fffd
    STW(5, 0x108, 8)
    li x7, 200000
.Lp\@:
    csrr x5, mip
    andi x5, x5, 8
    bnez x5, .Lg\@
    addi x7, x7, -1
    bnez x7, .Lp\@
    li x10, 0xdead
    li x11, 0
    CHK \id
.Lg\@:
.endm

.macro IRQ_OFF
    csrci mstatus, 8
    csrw mie, x0
    li x5, 0x3ffff
    STW(5, 0x108, 8)
    STW(5, 0x104, 8)
.endm

.macro DISPATCH n
    li x5, \n
    bne x10, x5, .Ln\@
    j case_\n
.Ln\@:
.endm

// int run_case(int n, mmio, mb)
run_case:
    FN_ENTER
    MOVP(8, 11)
    MOVP(9, 12)
    SETMTVEC(trap_handler)
    DISPATCH 0
    CASE_LIST
    li x10, -1
    j rc_out
case_end:
    LDW(10, MB_NFAIL, 9)
rc_out:
    FN_EXIT

// halt request, wait for the ROM (dpc lands in dh_loop)
dbg_halt:
    LDW(6, MB_CNT, 9)
    li x5, 1
    STW(5, 0x140, 8)
    li x7, 20000
dh_loop:
    LDW(5, MB_CNT, 9)
    bne x5, x6, dh_done
    addi x7, x7, -1
    bnez x7, dh_loop
    li x10, 0xdead
    li x11, 0
    CHK 999
dh_done:
    RET
dh_end:
    nop

// Trap handler. Interrupts: ack + mask all lines, return. ecall: resume at
// MB_RESUME in M. Other exceptions: skip 4 bytes (same mode) when RESUME is 0
// or SKIPMODE is set, else resume at RESUME in M.
.balign 64
trap_handler:
    MSCR_SAVE13
    HSAVE12
    LDW(13, MB_TCNT, 9)
    addi x13, x13, 1
    STW(13, MB_TCNT, 9)
    csrr x13, mcause
    STW(13, MB_TCAUSE, 9)
    GETMEPC(13)
    STW(13, MB_TEPC, 9)
    csrr x13, mtval
    STW(13, MB_TVAL, 9)
    csrr x13, mstatus
    STW(13, MB_TMSTATUS, 9)
    csrr x13, mcause
    bltz x13, th_irq
    addi x12, x13, -8
    beqz x12, th_resume
    addi x12, x13, -11
    beqz x12, th_resume
    LDW(12, MB_W2, 9)
    bnez x12, th_skip
    LDW(12, MB_RESUME, 9)
    bnez x12, th_resume
th_skip:
    MEPC_ADD4
    j th_out
th_resume:
    LDW(12, MB_RESUME, 9)
    SETMEPC(12)
    li x13, 0x1800
    csrs mstatus, x13
    j th_out
th_irq:
    li x13, 0x3ffff
    STW(13, 0x108, 8)
    STW(13, 0x104, 8)
th_out:
    HREST12
    MSCR_REST13
    mret
trap_handler_end:
    nop

// div/mul workload, result in x10 (x5,x6,x7,x13,x14,x15)
mc_work:
    li x5, 0x13579bdf
    li x6, 0
    li x7, 30
mw_loop:
    li x13, 1103515245
    mul x5, x5, x13
    li x13, 12345
    add x5, x5, x13
    mulh x13, x5, x6
    add x6, x6, x13
    ori x14, x7, 1
    divu x13, x5, x14
    add x6, x6, x13
    remu x13, x5, x14
    xor x6, x6, x13
    div x13, x6, x14
    add x6, x6, x13
    rem x13, x6, x14
    add x6, x6, x13
    mulhu x13, x6, x5
    xor x6, x6, x13
    addi x7, x7, -1
    bnez x7, mw_loop
    mv x10, x6
    RET

// AMO / LR / SC workload on MB_W1, result in x10
amo_work:
    PTRADD(13, 9, MB_W1)
    li x5, 0x100
    STW(5, 0, 13)
    li x15, 0
    li x7, 20
aw_loop:
    li x6, 3
    AMO(0, 5, 6, 13)
    add x15, x15, x5
    AMO(4, 5, 7, 13)
    add x15, x15, x5
aw_lr:
    AMO(2, 5, 0, 13)
    addi x5, x5, 7
    AMO(3, 6, 5, 13)
    bnez x6, aw_lr
    add x15, x15, x5
    addi x7, x7, -1
    bnez x7, aw_loop
    LDW(5, 0, 13)
    add x10, x15, x5
    RET

// reset: clear dcsr step/ebreak bits, prv = M, disable both triggers
case_0:
    IRQ_OFF
    SETMB MB_OR, 3
    SETMB MB_ANDN, (DCSR_EBREAKM | DCSR_EBREAKU | DCSR_STEP)
    SETMB MB_TRIG_APPLY, 1
    CALL(dbg_halt)
    j case_end
