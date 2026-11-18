// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// KUDU-075 (CHERIoT program, from the RA review's ra_odd): cret to a backward
// sentry whose address is odd. The RA predictor predicts the return with the
// odd cra address as its target, the branch unit accepts it (it compares with
// the raw cra), and an interrupt or debug request taken before the target
// reaches IR0 saves the odd address as mepcc/depcc.
//
// void ro_run(unsigned *r, unsigned n): r[] = {iterations, interrupts,
// interrupts with odd mepcc, first odd mepcc address, synchronous
// exceptions}. The handler clears mepcc[0] before mret.

.option norelax
.option norvc
.section .text
.globl ro_run
.macro ADDR reg, sym
  lui \reg, %hi(\sym)
  addi \reg, \reg, %lo(\sym)
.endm

.balign 16
handler:
  csrr t0, mcause
  bltz t0, h_irq
  clw t2, 16(c10)         // unexpected exception: count, skip
  addi t2, t2, 1
  csw t2, 16(c10)
  cspecialr ct1, mepcc
  cincoffset ct1, ct1, 4
  cspecialw mepcc, ct1
  mret
h_irq:
  clw t2, 4(c10)
  addi t2, t2, 1
  csw t2, 4(c10)
  cspecialr ct1, mepcc
  cgetaddr t1, ct1
  andi t2, t1, 1
  beqz t2, 1f
  clw t2, 8(c10)
  bnez t2, 2f
  csw t1, 12(c10)         // first odd mepcc address
2:clw t2, 8(c10)
  addi t2, t2, 1
  csw t2, 8(c10)
  andi t1, t1, -2
  cspecialr ct2, mepcc    // cgetaddr above overwrote ct1 with an integer
  csetaddr ct2, ct2, t1
  cspecialw mepcc, ct2
1:li t0, 1
  csw t0, 0(c11)          // acknowledge
  mret

ro_run:                   // ca0 = results, a1 = iterations
  cincoffset csp, csp, -32
  csc cra, 0(csp)
  csc cs0, 8(csp)
  csc cs1, 16(csp)
  cspecialr ct0, mtcc
  csc ct0, 24(csp)
  cmove c10, ca0
  csw zero, 0(c10)
  csw zero, 4(c10)
  csw zero, 8(c10)
  csw zero, 12(c10)
  csw zero, 16(c10)
  mv s0, a1
  li s1, 0
  cspecialr c9, mscratchc
  auipcc c12, 0
  ADDR t0, handler
  csetaddr ct0, c12, t0
  cspecialw mtcc, ct0
  ADDR t0, L_tgt
  addi t0, t0, 1          // odd return address
  csetaddr c14, c12, t0
  li t1, 5
  csetaddr c15, c9, t1
  cseal c14, c14, c15     // backward sentry (otype 5)
  cspecialr c11, mtdc
  li t0, 0x83800108
  csetaddr c11, c11, t0
  li t0, 0x3fffe
  csw t0, 0(c11)          // unmask the TB external interrupt (intr_mask)
  li t0, 0x83800104
  csetaddr c11, c11, t0   // c11 = interrupt acknowledge register
  li t0, 0x800
  csrs mie, t0
  csrsi mstatus, 8
loop:
  cmove cra, c14
  nop
  nop
  nop
  nop
  nop
  nop
  cret                    // predicted from cur_ra
  nop
.balign 8
L_tgt:
  addi s1, s1, 1
  addi s0, s0, -1
  bnez s0, loop
  csrci mstatus, 8
  li t0, 0x800
  csrc mie, t0
  cspecialr c11, mtdc
  li t0, 0x83800108
  csetaddr c11, c11, t0
  li t1, 0x3ffff
  csw t1, 0(c11)          // mask all TB interrupts
  li t0, 0x83800104
  csetaddr c11, c11, t0
  csw t1, 0(c11)          // and acknowledge them
  csw s1, 0(c10)
  clc ct0, 24(csp)
  cspecialw mtcc, ct0
  csrsi mstatus, 8
  clc cra, 0(csp)
  clc cs0, 8(csp)
  clc cs1, 16(csp)
  cincoffset csp, csp, 32
  cret
