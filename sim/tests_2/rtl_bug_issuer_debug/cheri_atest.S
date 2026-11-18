// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Every case writes the mailbox address to TB scratch_reg1 (0x8380_0004) and
// raises debug_req (0x8380_0140). The debug ROM preserves all registers; the
// trap handler clobbers t0-t2. RVC is off so that instruction offsets from the
// I1 base label are 4 bytes each.

.option norvc

.section .text
.globl install_handler
.type install_handler, @function
.globl step_illegal
.type step_illegal, @function
.globl step_irq
.type step_irq, @function
.globl step_ebreak
.type step_ebreak, @function
.globl step_wfi
.type step_wfi, @function
.globl mepc_halt
.type mepc_halt, @function

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

// unsigned install_handler(void): MTCC = trap_handler, returns its address.
install_handler:
1:  auipcc c10, %cheri_compartment_pccrel_hi(trap_handler)
    cincoffset c10, c10, %cheri_compartment_pccrel_lo(1b)
    cspecialw mtcc, c10
    cgetaddr x10, c10
    cret

// ---------------------------------------------------------------------------
// I1: halt request while the IR is empty. dpc_<kind><n>(int *mb) asserts
// debug_req, runs n counted instructions and then redirects (cjalr or a taken
// branch), so the request lands at a different point of the redirect for each
// n. Returns x15. Layout from the base label (mb[15]), 4 bytes per instruction:
//   +4i   addi x15, 1        (i < n)
//   +4n   addi x15, 0x40
//   +4n+4 cjalr c14, c12 / bnez x14
//   +4n+8, +4n+12   addi x15, 0x400   (wrong path, must not execute)
//   +4n+16  addi x15, 0x10   (target)
//   +4n+20  addi x15, 0x20
//   +4n+24  addi x15, 0x80
//   +4n+28  delay loop
// ---------------------------------------------------------------------------
.macro DPC_BLOCK kind, n
.globl dpc_\kind\()\n
.type dpc_\kind\()\n, @function
dpc_\kind\()\n:
    TB_SETUP
92: auipcc c12, %cheri_compartment_pccrel_hi(93f)
    cincoffset c12, c12, %cheri_compartment_pccrel_lo(92b)
94: auipcc c11, %cheri_compartment_pccrel_hi(95f)
    cincoffset c11, c11, %cheri_compartment_pccrel_lo(94b)
    cgetaddr x11, c11
    csw x11, 60(c10)         // mb[15] = base
    li x15, 0
    RAISE_DEBUG_REQ          // x14 = 1
95:
    .rept \n
    addi x15, x15, 1
    .endr
    addi x15, x15, 0x40
.ifc \kind, j
    cjalr c14, c12
.else
    bnez x14, 93f
.endif
    addi x15, x15, 0x400
    addi x15, x15, 0x400
93: addi x15, x15, 0x10
    addi x15, x15, 0x20
    addi x15, x15, 0x80
    li x14, 300
96: addi x14, x14, -1
    bnez x14, 96b
    mv x10, x15
    cret
.size dpc_\kind\()\n, . - dpc_\kind\()\n
.endm

.irp n, 0,1,2,3,4,5,6,7,8,9,10,11
DPC_BLOCK j, \n
DPC_BLOCK b, \n
.endr

// ---------------------------------------------------------------------------
// I6: a halt request must not change MEPCC. Writes MEPCC = 2f (also mb[16]),
// halts, and returns the address of MEPCC after the resume.
// ---------------------------------------------------------------------------
mepc_halt:
    TB_SETUP
91: auipcc c11, %cheri_compartment_pccrel_hi(2f)
    cincoffset c11, c11, %cheri_compartment_pccrel_lo(91b)
    cspecialw mepcc, c11
    cgetaddr x11, c11
    csw x11, 64(c10)
    RAISE_DEBUG_REQ
    li x14, 300
1:  addi x14, x14, -1
    bnez x14, 1b
    cspecialr c11, mepcc
    cgetaddr x10, c11
    cret
2:  nop                      // never executed

// ---------------------------------------------------------------------------
// I2: single-step an illegal instruction. The ROM redirects to 2f with
// dcsr.step = 1. Expected: halt at the handler entry before it executes.
// ---------------------------------------------------------------------------
step_illegal:
    TB_SETUP
    SET_TARGET 2f
    RAISE_DEBUG_REQ
1:  j 1b
2:  .word 0xffffffff         // illegal; the handler resumes at 2f + 4
    li x10, 0
    cret

// ---------------------------------------------------------------------------
// I3: single-step with an enabled interrupt pending (dcsr.stepie = 0).
// MEIP is made pending with MIE = 0; the ROM sets MIE and steps 2f.
// Expected: the interrupt is not taken while stepping; halt at 2f + 4.
// ---------------------------------------------------------------------------
step_irq:
    TB_SETUP
    SET_TARGET 2f
    li x15, 0
    csrci mstatus, 8         // MIE = 0 (startup leaves it set)
    li x14, 0x3fffe
    csw x14, 264(c13)        // unmask the TB external interrupt (+INTR_RATE != 0)
    li x14, 0x800
    csrs mie, x14            // MEIE
3:  csrr x14, mip
    srli x14, x14, 11
    andi x14, x14, 1
    beqz x14, 3b             // wait for MEIP
    RAISE_DEBUG_REQ
1:  j 1b
2:  addi x15, x15, 1
    addi x15, x15, 2
    li x14, 0x3ffff
    csw x14, 264(c13)        // mask all TB interrupts
    li x14, 7
    csw x14, 260(c13)        // acknowledge
    li x14, 0x800
    csrc mie, x14
    mv x10, x15
    cret

// ---------------------------------------------------------------------------
// I4: single-step an ebreak with dcsr.ebreakm = 1. Expected dcsr.cause =
// EBREAK (1), which has priority over STEP (4).
// ---------------------------------------------------------------------------
step_ebreak:
    TB_SETUP
    SET_TARGET 2f
    RAISE_DEBUG_REQ
1:  j 1b
2:  ebreak                   // the ROM resumes at 2f + 4
    li x10, 0
    cret

// ---------------------------------------------------------------------------
// I5: single-step a wfi with no interrupt enabled. Expected: wfi completes
// (no-op) and the hart halts at 2f + 4. A hang here ends in +TIMEOUT.
// ---------------------------------------------------------------------------
step_wfi:
    TB_SETUP
    SET_TARGET 2f
    csrw mie, x0
    RAISE_DEBUG_REQ
1:  j 1b
2:  wfi
    li x10, 0
    cret

// ---------------------------------------------------------------------------
// Trap handler. Counts traps (mb[12]) and records mcause (mb[13]) and mepc
// (mb[14]). It does not trust MEPCC (a debug halt inside the handler may
// clobber it): exceptions resume at mb[16] + 4, interrupts at mb[16], the step
// target of the running case. Interrupts also silence the TB generator, clear
// MEIE and are counted in mb[18].
// ---------------------------------------------------------------------------
.p2align 2
trap_handler:
    cspecialr c6, mtdc
    li x7, 0x83800000
    csetaddr c6, c6, x7
    clw x7, 4(c6)
    csetaddr c5, c6, x7      // c5 = mailbox
    clw x7, 48(c5)
    addi x7, x7, 1
    csw x7, 48(c5)
    csrr x7, mcause
    csw x7, 52(c5)
    cspecialr c7, mepcc
    cgetaddr x7, c7
    csw x7, 56(c5)
    csrr x7, mcause
    bltz x7, 1f
    clw x7, 64(c5)
    addi x7, x7, 4
    j 2f
1:  li x7, 0x3ffff
    csw x7, 264(c6)          // mask all TB interrupts
    li x7, 7
    csw x7, 260(c6)          // acknowledge
    li x7, 0x800
    csrc mie, x7
    clw x7, 72(c5)
    addi x7, x7, 1
    csw x7, 72(c5)           // mb[18] = interrupts taken
    clw x7, 64(c5)
2:  cspecialr c6, mepcc
    csetaddr c6, c6, x7
    cspecialw mepcc, c6
    mret
