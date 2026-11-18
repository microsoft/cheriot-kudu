// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// RA review: predicted cret to an odd-address backward sentry; count interrupts with odd mepcc
// Ported to tests_2 (rtl_bug_ra_pred_conf2): unmasks external interrupt line 0 in the TB
// intr_mask (0x8380_0108) so +INTR_RATE reaches the core, and masks/acks all lines at the end.
.option norelax
.option norvc
.section .text
.globl cheri_atest
.macro ADDR reg, sym
  lui \reg, %hi(\sym)
  addi \reg, \reg, %lo(\sym)
.endm
.balign 16
handler:
  csrr t0, mcause
  bltz t0, h_irq
  clw t2, 8(c10)          // unexpected exception: count, skip
  addi t2, t2, 1
  csw t2, 8(c10)
  cspecialr ct1, mepcc
  cincoffset ct1, ct1, 4
  cspecialw mepcc, ct1
  mret
h_irq:
  cspecialr ct1, mepcc
  cgetaddr t1, ct1
  andi t1, t1, 1
  clw t2, 0(c10)
  add t2, t2, t1
  csw t2, 0(c10)
  clw t2, 4(c10)
  addi t2, t2, 1
  csw t2, 4(c10)
  li t0, 7
  csw t0, 0(c11)
  mret

cheri_atest:            // ca0 = results {nodd, nirq, nexc, niter}
  cincoffset csp, csp, -32
  csc cra, 0(csp)
  csc cs0, 8(csp)
  cspecialr ct0, mtcc
  csc ct0, 16(csp)
  cmove c10, ca0
  csw zero, 0(c10)
  csw zero, 4(c10)
  csw zero, 8(c10)
  cspecialr c9, mscratchc
  auipcc c12, 0
  ADDR t0, handler
  csetaddr ct0, c12, t0
  cspecialw mtcc, ct0
  ADDR t0, L_tgt
  addi t0, t0, 1
  csetaddr c14, c12, t0
  li t1, 5
  csetaddr c15, c9, t1
  cseal c14, c14, c15
  cspecialr c11, mtdc
  li t0, 0x83800100
  csetaddr c11, c11, t0
  li t0, 4
  csw t0, 0(c11)
  li t0, 0x83800108
  csetaddr c11, c11, t0
  li t0, 0x3fffe
  csw t0, 0(c11)
  li t0, 0x83800104
  csetaddr c11, c11, t0
  li t0, 0x800
  csrs mie, t0
  csrsi mstatus, 8
  li s0, 6000
loop:
  cmove cra, c14
  nop
  nop
  nop
  nop
  nop
  nop
  cret
  nop
.balign 8
L_tgt:
  addi s0, s0, -1
  bnez s0, loop
  csrci mstatus, 8
  li t0, 0x800
  csrc mie, t0
  cspecialr c11, mtdc
  li t0, 0x83800100
  csetaddr c11, c11, t0
  csw zero, 0(c11)
  li t0, 0x83800108
  csetaddr c11, c11, t0
  li t1, 0x3ffff
  csw t1, 0(c11)
  li t0, 0x83800104
  csetaddr c11, c11, t0
  csw t1, 0(c11)
  clc ct0, 16(csp)
  cspecialw mtcc, ct0
  csrsi mstatus, 8
  clc cra, 0(csp)
  clc cs0, 8(csp)
  cincoffset csp, csp, 32
  cret
