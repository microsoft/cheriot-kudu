// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
.option norelax
.option norvc
.section .text
.globl dcs_main
.balign 64
dcs_main:
  cincoffset csp, csp, -16
  csc cs0, 0(csp)
  csc cs1, 8(csp)
  cmove cs1, ca0
  li s0, 0
  li tp, 0
  li t1, 0x22222222
  csw t1, 260(cs1)
  clw t2, 260(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa4a4a4a4
  csw a5, 256(cs1)
  csc cs1, 256(cs1)
  clw a3, 260(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 260(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 128(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x33333333
  csw t1, 276(cs1)
  clw t2, 276(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa7a7a7a7
  csw a5, 272(cs1)
  csc cs1, 272(cs1)
  clw a3, 276(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 276(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 132(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x44444444
  csw t1, 292(cs1)
  clw t2, 292(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa6a6a6a6
  csw a5, 288(cs1)
  csc cs1, 288(cs1)
  clw a3, 292(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 292(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 136(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x55555555
  csw t1, 308(cs1)
  clw t2, 308(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa1a1a1a1
  csw a5, 304(cs1)
  csc cs1, 304(cs1)
  nop
  clw a3, 308(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 308(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 140(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x66666666
  csw t1, 324(cs1)
  clw t2, 324(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa0a0a0a0
  csw a5, 320(cs1)
  csc cs1, 320(cs1)
  nop
  clw a3, 324(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 324(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 144(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x77777777
  csw t1, 340(cs1)
  clw t2, 340(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa3a3a3a3
  csw a5, 336(cs1)
  csc cs1, 336(cs1)
  nop
  clw a3, 340(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 340(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 148(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x88888888
  csw t1, 356(cs1)
  clw t2, 356(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa2a2a2a2
  csw a5, 352(cs1)
  csc cs1, 352(cs1)
  nop
  nop
  clw a3, 356(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 356(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 152(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x99999999
  csw t1, 372(cs1)
  clw t2, 372(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xadadadad
  csw a5, 368(cs1)
  csc cs1, 368(cs1)
  nop
  nop
  clw a3, 372(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 372(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 156(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xaaaaaaaa
  csw t1, 260(cs1)
  clw t2, 260(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xacacacac
  csw a5, 256(cs1)
  csc cs1, 256(cs1)
  nop
  nop
  clw a3, 260(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 260(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 160(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xbbbbbbbb
  csw t1, 276(cs1)
  clw t2, 276(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xafafafaf
  csw a5, 272(cs1)
  csc cs1, 272(cs1)
  nop
  nop
  nop
  clw a3, 276(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 276(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 164(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xcccccccc
  csw t1, 292(cs1)
  clw t2, 292(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xaeaeaeae
  csw a5, 288(cs1)
  csc cs1, 288(cs1)
  nop
  nop
  nop
  clw a3, 292(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 292(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 168(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xdddddddd
  csw t1, 308(cs1)
  clw t2, 308(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa9a9a9a9
  csw a5, 304(cs1)
  csc cs1, 304(cs1)
  nop
  nop
  nop
  clw a3, 308(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 308(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 172(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xeeeeeeee
  csw t1, 324(cs1)
  clw t2, 324(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa8a8a8a8
  csw a5, 322(cs1)
  clw a3, 324(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 324(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 176(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xffffffff
  csw t1, 340(cs1)
  clw t2, 340(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xabababab
  csw a5, 338(cs1)
  clw a3, 340(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 340(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 180(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x11111111
  csw t1, 356(cs1)
  clw t2, 356(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xaaaaaaaa
  csw a5, 354(cs1)
  clw a3, 356(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 356(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 184(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x22222222
  csw t1, 372(cs1)
  clw t2, 372(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb5b5b5b5
  csw a5, 370(cs1)
  nop
  clw a3, 372(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 372(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 188(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x33333333
  csw t1, 260(cs1)
  clw t2, 260(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb4b4b4b4
  csw a5, 258(cs1)
  nop
  clw a3, 260(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 260(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 192(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x44444444
  csw t1, 276(cs1)
  clw t2, 276(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb7b7b7b7
  csw a5, 274(cs1)
  nop
  clw a3, 276(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 276(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 196(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x55555555
  csw t1, 292(cs1)
  clw t2, 292(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb6b6b6b6
  csw a5, 290(cs1)
  nop
  nop
  clw a3, 292(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 292(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 200(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x66666666
  csw t1, 308(cs1)
  clw t2, 308(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb1b1b1b1
  csw a5, 306(cs1)
  nop
  nop
  clw a3, 308(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 308(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 204(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x77777777
  csw t1, 324(cs1)
  clw t2, 324(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb0b0b0b0
  csw a5, 322(cs1)
  nop
  nop
  clw a3, 324(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 324(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 208(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x88888888
  csw t1, 340(cs1)
  clw t2, 340(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb3b3b3b3
  csw a5, 338(cs1)
  nop
  nop
  nop
  clw a3, 340(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 340(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 212(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x99999999
  csw t1, 356(cs1)
  clw t2, 356(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb2b2b2b2
  csw a5, 354(cs1)
  nop
  nop
  nop
  clw a3, 356(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 356(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 216(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xaaaaaaaa
  csw t1, 372(cs1)
  clw t2, 372(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xbdbdbdbd
  csw a5, 370(cs1)
  nop
  nop
  nop
  clw a3, 372(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 372(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 220(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xbbbbbbbb
  csw t1, 260(cs1)
  clw t2, 260(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xbcbcbcbc
  csh a5, 259(cs1)
  clw a3, 260(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 260(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 224(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xcccccccc
  csw t1, 276(cs1)
  clw t2, 276(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xbfbfbfbf
  csh a5, 275(cs1)
  clw a3, 276(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 276(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 228(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xdddddddd
  csw t1, 292(cs1)
  clw t2, 292(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xbebebebe
  csh a5, 291(cs1)
  clw a3, 292(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 292(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 232(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xeeeeeeee
  csw t1, 308(cs1)
  clw t2, 308(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb9b9b9b9
  csh a5, 307(cs1)
  nop
  clw a3, 308(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 308(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 236(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xffffffff
  csw t1, 324(cs1)
  clw t2, 324(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb8b8b8b8
  csh a5, 323(cs1)
  nop
  clw a3, 324(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 324(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 240(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x11111111
  csw t1, 340(cs1)
  clw t2, 340(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xbbbbbbbb
  csh a5, 339(cs1)
  nop
  clw a3, 340(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 340(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 244(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x22222222
  csw t1, 356(cs1)
  clw t2, 356(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xbabababa
  csh a5, 355(cs1)
  nop
  nop
  clw a3, 356(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 356(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 248(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x33333333
  csw t1, 372(cs1)
  clw t2, 372(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x85858585
  csh a5, 371(cs1)
  nop
  nop
  clw a3, 372(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 372(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 252(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x44444444
  csw t1, 260(cs1)
  clw t2, 260(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x84848484
  csh a5, 259(cs1)
  nop
  nop
  clw a3, 260(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 260(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 256(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x55555555
  csw t1, 276(cs1)
  clw t2, 276(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x87878787
  csh a5, 275(cs1)
  nop
  nop
  nop
  clw a3, 276(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 276(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 260(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x66666666
  csw t1, 292(cs1)
  clw t2, 292(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x86868686
  csh a5, 291(cs1)
  nop
  nop
  nop
  clw a3, 292(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 292(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 264(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x77777777
  csw t1, 308(cs1)
  clw t2, 308(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x81818181
  csh a5, 307(cs1)
  nop
  nop
  nop
  clw a3, 308(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 308(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 268(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x88888888
  csw t1, 324(cs1)
  clw t2, 324(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x80808080
  csw a5, 323(cs1)
  clw a3, 324(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 324(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 272(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x99999999
  csw t1, 340(cs1)
  clw t2, 340(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x83838383
  csw a5, 339(cs1)
  clw a3, 340(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 340(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 276(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xaaaaaaaa
  csw t1, 356(cs1)
  clw t2, 356(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x82828282
  csw a5, 355(cs1)
  clw a3, 356(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 356(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 280(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xbbbbbbbb
  csw t1, 372(cs1)
  clw t2, 372(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x8d8d8d8d
  csw a5, 371(cs1)
  nop
  clw a3, 372(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 372(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 284(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xcccccccc
  csw t1, 260(cs1)
  clw t2, 260(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x8c8c8c8c
  csw a5, 259(cs1)
  nop
  clw a3, 260(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 260(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 288(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xdddddddd
  csw t1, 276(cs1)
  clw t2, 276(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x8f8f8f8f
  csw a5, 275(cs1)
  nop
  clw a3, 276(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 276(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 292(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xeeeeeeee
  csw t1, 292(cs1)
  clw t2, 292(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x8e8e8e8e
  csw a5, 291(cs1)
  nop
  nop
  clw a3, 292(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 292(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 296(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xffffffff
  csw t1, 308(cs1)
  clw t2, 308(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x89898989
  csw a5, 307(cs1)
  nop
  nop
  clw a3, 308(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 308(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 300(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x11111111
  csw t1, 324(cs1)
  clw t2, 324(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x88888888
  csw a5, 323(cs1)
  nop
  nop
  clw a3, 324(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 324(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 304(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x22222222
  csw t1, 340(cs1)
  clw t2, 340(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x8b8b8b8b
  csw a5, 339(cs1)
  nop
  nop
  nop
  clw a3, 340(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 340(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 308(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x33333333
  csw t1, 356(cs1)
  clw t2, 356(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x8a8a8a8a
  csw a5, 355(cs1)
  nop
  nop
  nop
  clw a3, 356(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 356(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 312(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x44444444
  csw t1, 372(cs1)
  clw t2, 372(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x95959595
  csw a5, 371(cs1)
  nop
  nop
  nop
  clw a3, 372(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 372(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 316(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x55555555
  csw t1, 260(cs1)
  clw t2, 260(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x94949494
  csw a5, 257(cs1)
  clw a3, 260(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 260(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 320(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x66666666
  csw t1, 276(cs1)
  clw t2, 276(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x97979797
  csw a5, 273(cs1)
  clw a3, 276(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 276(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 324(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x77777777
  csw t1, 292(cs1)
  clw t2, 292(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x96969696
  csw a5, 289(cs1)
  clw a3, 292(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 292(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 328(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x88888888
  csw t1, 308(cs1)
  clw t2, 308(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x91919191
  csw a5, 305(cs1)
  nop
  clw a3, 308(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 308(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 332(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x99999999
  csw t1, 324(cs1)
  clw t2, 324(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x90909090
  csw a5, 321(cs1)
  nop
  clw a3, 324(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 324(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 336(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xaaaaaaaa
  csw t1, 340(cs1)
  clw t2, 340(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x93939393
  csw a5, 337(cs1)
  nop
  clw a3, 340(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 340(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 340(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xbbbbbbbb
  csw t1, 356(cs1)
  clw t2, 356(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x92929292
  csw a5, 353(cs1)
  nop
  nop
  clw a3, 356(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 356(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 344(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xcccccccc
  csw t1, 372(cs1)
  clw t2, 372(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x9d9d9d9d
  csw a5, 369(cs1)
  nop
  nop
  clw a3, 372(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 372(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 348(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xdddddddd
  csw t1, 260(cs1)
  clw t2, 260(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x9c9c9c9c
  csw a5, 257(cs1)
  nop
  nop
  clw a3, 260(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 260(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 352(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xeeeeeeee
  csw t1, 276(cs1)
  clw t2, 276(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x9f9f9f9f
  csw a5, 273(cs1)
  nop
  nop
  nop
  clw a3, 276(cs1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 276(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 356(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0xffffffff
  csw t1, 292(cs1)
  clw t2, 292(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x9e9e9e9e
  csw a5, 289(cs1)
  nop
  nop
  nop
  clw a3, 292(cs1)
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 292(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 360(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  li t1, 0x11111111
  csw t1, 308(cs1)
  clw t2, 308(cs1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x99999999
  csw a5, 305(cs1)
  nop
  nop
  nop
  clw a3, 308(cs1)
  nop
  nop
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  clw t2, 308(cs1)
  addi tp, tp, 1
  bne a4, t2, 1f
  beq a3, t2, 2f
1:
  addi s0, s0, 1
  xor t1, a4, t2
  snez t1, t1
  xor a2, a3, t2
  snez a2, a2
  slli a2, a2, 1
  or t1, t1, a2
  csw t1, 364(cs1)
  csw a4, 8(cs1)
  csw t2, 12(cs1)
  csw tp, 16(cs1)
2:
  csw s0, 0(cs1)
  csw tp, 4(cs1)
  clc cs0, 0(csp)
  clc cs1, 8(csp)
  cincoffset csp, csp, 16
  cret
