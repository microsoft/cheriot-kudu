// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
.option norelax
.option norvc
.section .text
.globl dcs_main
.balign 64
dcs_main:
  addi sp, sp, -16
  sw s0, 0(sp)
  sw s1, 4(sp)
  mv s1, a0
  li s0, 0
  li tp, 0
  li t1, 0x22222222
  sw t1, 260(s1)
  lw t2, 260(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa4a4a4a4
  sw a5, 258(s1)
  lw a3, 260(s1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  lw t2, 260(s1)
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
  sw t1, 128(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x33333333
  sw t1, 276(s1)
  lw t2, 276(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa7a7a7a7
  sw a5, 274(s1)
  lw a3, 276(s1)
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
  lw t2, 276(s1)
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
  sw t1, 132(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x44444444
  sw t1, 292(s1)
  lw t2, 292(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa6a6a6a6
  sw a5, 290(s1)
  lw a3, 292(s1)
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
  lw t2, 292(s1)
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
  sw t1, 136(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x55555555
  sw t1, 308(s1)
  lw t2, 308(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa1a1a1a1
  sw a5, 306(s1)
  nop
  lw a3, 308(s1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  lw t2, 308(s1)
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
  sw t1, 140(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x66666666
  sw t1, 324(s1)
  lw t2, 324(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa0a0a0a0
  sw a5, 322(s1)
  nop
  lw a3, 324(s1)
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
  lw t2, 324(s1)
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
  sw t1, 144(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x77777777
  sw t1, 340(s1)
  lw t2, 340(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa3a3a3a3
  sw a5, 338(s1)
  nop
  lw a3, 340(s1)
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
  lw t2, 340(s1)
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
  sw t1, 148(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x88888888
  sw t1, 356(s1)
  lw t2, 356(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa2a2a2a2
  sw a5, 354(s1)
  nop
  nop
  lw a3, 356(s1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  lw t2, 356(s1)
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
  sw t1, 152(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x99999999
  sw t1, 372(s1)
  lw t2, 372(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xadadadad
  sw a5, 370(s1)
  nop
  nop
  lw a3, 372(s1)
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
  lw t2, 372(s1)
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
  sw t1, 156(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xaaaaaaaa
  sw t1, 260(s1)
  lw t2, 260(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xacacacac
  sw a5, 258(s1)
  nop
  nop
  lw a3, 260(s1)
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
  lw t2, 260(s1)
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
  sw t1, 160(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xbbbbbbbb
  sw t1, 276(s1)
  lw t2, 276(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xafafafaf
  sw a5, 274(s1)
  nop
  nop
  nop
  lw a3, 276(s1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  lw t2, 276(s1)
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
  sw t1, 164(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xcccccccc
  sw t1, 292(s1)
  lw t2, 292(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xaeaeaeae
  sw a5, 290(s1)
  nop
  nop
  nop
  lw a3, 292(s1)
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
  lw t2, 292(s1)
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
  sw t1, 168(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xdddddddd
  sw t1, 308(s1)
  lw t2, 308(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa9a9a9a9
  sw a5, 306(s1)
  nop
  nop
  nop
  lw a3, 308(s1)
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
  lw t2, 308(s1)
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
  sw t1, 172(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xeeeeeeee
  sw t1, 324(s1)
  lw t2, 324(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xa8a8a8a8
  sh a5, 323(s1)
  lw a3, 324(s1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  lw t2, 324(s1)
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
  sw t1, 176(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xffffffff
  sw t1, 340(s1)
  lw t2, 340(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xabababab
  sh a5, 339(s1)
  lw a3, 340(s1)
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
  lw t2, 340(s1)
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
  sw t1, 180(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x11111111
  sw t1, 356(s1)
  lw t2, 356(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xaaaaaaaa
  sh a5, 355(s1)
  lw a3, 356(s1)
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
  lw t2, 356(s1)
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
  sw t1, 184(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x22222222
  sw t1, 372(s1)
  lw t2, 372(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb5b5b5b5
  sh a5, 371(s1)
  nop
  lw a3, 372(s1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  lw t2, 372(s1)
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
  sw t1, 188(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x33333333
  sw t1, 260(s1)
  lw t2, 260(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb4b4b4b4
  sh a5, 259(s1)
  nop
  lw a3, 260(s1)
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
  lw t2, 260(s1)
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
  sw t1, 192(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x44444444
  sw t1, 276(s1)
  lw t2, 276(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb7b7b7b7
  sh a5, 275(s1)
  nop
  lw a3, 276(s1)
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
  lw t2, 276(s1)
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
  sw t1, 196(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x55555555
  sw t1, 292(s1)
  lw t2, 292(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb6b6b6b6
  sh a5, 291(s1)
  nop
  nop
  lw a3, 292(s1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  lw t2, 292(s1)
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
  sw t1, 200(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x66666666
  sw t1, 308(s1)
  lw t2, 308(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb1b1b1b1
  sh a5, 307(s1)
  nop
  nop
  lw a3, 308(s1)
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
  lw t2, 308(s1)
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
  sw t1, 204(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x77777777
  sw t1, 324(s1)
  lw t2, 324(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb0b0b0b0
  sh a5, 323(s1)
  nop
  nop
  lw a3, 324(s1)
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
  lw t2, 324(s1)
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
  sw t1, 208(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x88888888
  sw t1, 340(s1)
  lw t2, 340(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb3b3b3b3
  sh a5, 339(s1)
  nop
  nop
  nop
  lw a3, 340(s1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  lw t2, 340(s1)
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
  sw t1, 212(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x99999999
  sw t1, 356(s1)
  lw t2, 356(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb2b2b2b2
  sh a5, 355(s1)
  nop
  nop
  nop
  lw a3, 356(s1)
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
  lw t2, 356(s1)
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
  sw t1, 216(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xaaaaaaaa
  sw t1, 372(s1)
  lw t2, 372(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xbdbdbdbd
  sh a5, 371(s1)
  nop
  nop
  nop
  lw a3, 372(s1)
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
  lw t2, 372(s1)
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
  sw t1, 220(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xbbbbbbbb
  sw t1, 260(s1)
  lw t2, 260(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xbcbcbcbc
  sw a5, 259(s1)
  lw a3, 260(s1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  lw t2, 260(s1)
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
  sw t1, 224(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xcccccccc
  sw t1, 276(s1)
  lw t2, 276(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xbfbfbfbf
  sw a5, 275(s1)
  lw a3, 276(s1)
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
  lw t2, 276(s1)
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
  sw t1, 228(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xdddddddd
  sw t1, 292(s1)
  lw t2, 292(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xbebebebe
  sw a5, 291(s1)
  lw a3, 292(s1)
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
  lw t2, 292(s1)
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
  sw t1, 232(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xeeeeeeee
  sw t1, 308(s1)
  lw t2, 308(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb9b9b9b9
  sw a5, 307(s1)
  nop
  lw a3, 308(s1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  lw t2, 308(s1)
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
  sw t1, 236(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xffffffff
  sw t1, 324(s1)
  lw t2, 324(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xb8b8b8b8
  sw a5, 323(s1)
  nop
  lw a3, 324(s1)
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
  lw t2, 324(s1)
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
  sw t1, 240(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x11111111
  sw t1, 340(s1)
  lw t2, 340(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xbbbbbbbb
  sw a5, 339(s1)
  nop
  lw a3, 340(s1)
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
  lw t2, 340(s1)
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
  sw t1, 244(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x22222222
  sw t1, 356(s1)
  lw t2, 356(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0xbabababa
  sw a5, 355(s1)
  nop
  nop
  lw a3, 356(s1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  lw t2, 356(s1)
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
  sw t1, 248(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x33333333
  sw t1, 372(s1)
  lw t2, 372(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x85858585
  sw a5, 371(s1)
  nop
  nop
  lw a3, 372(s1)
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
  lw t2, 372(s1)
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
  sw t1, 252(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x44444444
  sw t1, 260(s1)
  lw t2, 260(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x84848484
  sw a5, 259(s1)
  nop
  nop
  lw a3, 260(s1)
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
  lw t2, 260(s1)
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
  sw t1, 256(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x55555555
  sw t1, 276(s1)
  lw t2, 276(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x87878787
  sw a5, 275(s1)
  nop
  nop
  nop
  lw a3, 276(s1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  lw t2, 276(s1)
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
  sw t1, 260(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x66666666
  sw t1, 292(s1)
  lw t2, 292(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x86868686
  sw a5, 291(s1)
  nop
  nop
  nop
  lw a3, 292(s1)
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
  lw t2, 292(s1)
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
  sw t1, 264(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x77777777
  sw t1, 308(s1)
  lw t2, 308(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x81818181
  sw a5, 307(s1)
  nop
  nop
  nop
  lw a3, 308(s1)
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
  lw t2, 308(s1)
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
  sw t1, 268(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x88888888
  sw t1, 324(s1)
  lw t2, 324(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x80808080
  sw a5, 321(s1)
  lw a3, 324(s1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  lw t2, 324(s1)
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
  sw t1, 272(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x99999999
  sw t1, 340(s1)
  lw t2, 340(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x83838383
  sw a5, 337(s1)
  lw a3, 340(s1)
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
  lw t2, 340(s1)
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
  sw t1, 276(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xaaaaaaaa
  sw t1, 356(s1)
  lw t2, 356(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x82828282
  sw a5, 353(s1)
  lw a3, 356(s1)
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
  lw t2, 356(s1)
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
  sw t1, 280(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xbbbbbbbb
  sw t1, 372(s1)
  lw t2, 372(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x8d8d8d8d
  sw a5, 369(s1)
  nop
  lw a3, 372(s1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  lw t2, 372(s1)
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
  sw t1, 284(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xcccccccc
  sw t1, 260(s1)
  lw t2, 260(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x8c8c8c8c
  sw a5, 257(s1)
  nop
  lw a3, 260(s1)
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
  lw t2, 260(s1)
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
  sw t1, 288(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xdddddddd
  sw t1, 276(s1)
  lw t2, 276(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x8f8f8f8f
  sw a5, 273(s1)
  nop
  lw a3, 276(s1)
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
  lw t2, 276(s1)
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
  sw t1, 292(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xeeeeeeee
  sw t1, 292(s1)
  lw t2, 292(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x8e8e8e8e
  sw a5, 289(s1)
  nop
  nop
  lw a3, 292(s1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  lw t2, 292(s1)
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
  sw t1, 296(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0xffffffff
  sw t1, 308(s1)
  lw t2, 308(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x89898989
  sw a5, 305(s1)
  nop
  nop
  lw a3, 308(s1)
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
  lw t2, 308(s1)
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
  sw t1, 300(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x11111111
  sw t1, 324(s1)
  lw t2, 324(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x88888888
  sw a5, 321(s1)
  nop
  nop
  lw a3, 324(s1)
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
  lw t2, 324(s1)
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
  sw t1, 304(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x22222222
  sw t1, 340(s1)
  lw t2, 340(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x8b8b8b8b
  sw a5, 337(s1)
  nop
  nop
  nop
  lw a3, 340(s1)
  xor a4, a3, zero
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  lw t2, 340(s1)
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
  sw t1, 308(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x33333333
  sw t1, 356(s1)
  lw t2, 356(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x8a8a8a8a
  sw a5, 353(s1)
  nop
  nop
  nop
  lw a3, 356(s1)
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
  lw t2, 356(s1)
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
  sw t1, 312(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  li t1, 0x44444444
  sw t1, 372(s1)
  lw t2, 372(s1)
  nop
  nop
  nop
  nop
  nop
  nop
  li a5, 0x95959595
  sw a5, 369(s1)
  nop
  nop
  nop
  lw a3, 372(s1)
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
  lw t2, 372(s1)
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
  sw t1, 316(s1)
  sw a4, 8(s1)
  sw t2, 12(s1)
  sw tp, 16(s1)
2:
  sw s0, 0(s1)
  sw tp, 4(s1)
  lw s0, 0(sp)
  lw s1, 4(sp)
  addi sp, sp, 16
  ret
