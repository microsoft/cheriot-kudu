// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// review5/collide debug ROM (RV32, at 0x8400_0000). Transparent (t0..t3 restored).
// Mailbox (TB shadow, 0x8380_0170 + 4*i):
//   0 allowed dcsr.cause mask (bit c)      1 last dcsr      2 last dpc
//   3 step budget (ROM sets dcsr.step while >0, decrementing per entry)
//   4 dcsr ctrl (bit15 ebreakm)            5 trigger-0 execute address (0 = none)
//   6 per-cause entry counters (4 bits/cause)
//   7/8 t2/t3 save                         9/10 first bad dcsr/dpc
// scratch0 (0x8380_0000) += 1 per entry; scratch1 (0x8380_0004) += 1 per bad cause,
// += 0x100 per exception inside debug mode.
// cause 1 (ebreak): dpc advanced past the ebreak. cause 2 (trigger): trigger disabled and
// mailbox 5 cleared. cause 3 (haltreq): ack (write 0 to 0x140); if s8 != 0, no step burst is pending (mb3 == 0) and
// s8 <= dpc <= s3, dpc := a6 (test-side redirect, used to skip a wfi).
.option norvc
.section .text
.globl _start
_start:
    j entry
    nop
    j exc_entry

entry:
    csrw 0x7b2, t0
    csrw 0x7b3, t1
    li t0, 0x83800000
    sw t2, 0x18c(t0)
    sw t3, 0x190(t0)
    csrr t1, 0x7b0
    sw t1, 0x174(t0)
    csrr t2, 0x7b1
    sw t2, 0x178(t0)
    srli t1, t1, 6
    andi t1, t1, 7
    slli t2, t1, 2
    li t3, 1
    sll t3, t3, t2
    lw t2, 0x188(t0)
    add t2, t2, t3
    sw t2, 0x188(t0)
    lw t2, 0x170(t0)
    srl t2, t2, t1
    andi t2, t2, 1
    bnez t2, cause_ok
    lw t2, 4(t0)
    addi t2, t2, 1
    sw t2, 4(t0)
    lw t3, 0x194(t0)
    bnez t3, cause_ok
    csrr t3, 0x7b0
    sw t3, 0x194(t0)
    csrr t3, 0x7b1
    sw t3, 0x198(t0)
cause_ok:
    lw t2, 0(t0)
    addi t2, t2, 1
    sw t2, 0(t0)
    li t2, 1
    bne t1, t2, 1f
    csrr t2, 0x7b1           // ebreak: skip it
    lhu t3, 0(t2)
    andi t3, t3, 3
    addi t2, t2, 2
    addi t3, t3, -3
    bnez t3, 2f
    addi t2, t2, 2
2:  csrw 0x7b1, t2
1:  li t2, 2
    bne t1, t2, 3f
    sw zero, 0x184(t0)       // trigger fired: disable
    csrw 0x7a0, zero
    csrw 0x7a1, zero
3:  li t2, 3
    bne t1, t2, 4f
    sw zero, 0x140(t0)       // ack haltreq
    beqz s8, 4f
    lw t2, 0x17c(t0)         // no redirect while a step burst is pending (step-start haltreq)
    bnez t2, 4f
    csrr t2, 0x7b1
    bltu t2, s8, 4f
    bltu s3, t2, 4f
    csrw 0x7b1, a6
4:  lw t2, 0x184(t0)         // (re)program trigger 0
    beqz t2, 5f
    csrw 0x7a0, zero
    csrw 0x7a2, t2
    li t3, 4
    csrw 0x7a1, t3
5:  li t2, 0x8000
    csrc 0x7b0, t2
    lw t3, 0x180(t0)
    and t3, t3, t2
    csrs 0x7b0, t3
    lw t2, 0x17c(t0)
    beqz t2, 6f
    addi t2, t2, -1
    sw t2, 0x17c(t0)
    csrsi 0x7b0, 4
    j 7f
6:  csrci 0x7b0, 4
7:  lw t2, 0x18c(t0)
    lw t3, 0x190(t0)
    csrr t0, 0x7b2
    csrr t1, 0x7b3
    dret

exc_entry:
    li t0, 0x83800000
    lw t1, 4(t0)
    addi t1, t1, 0x100
    sw t1, 4(t0)
    lw t2, 0x18c(t0)
    lw t3, 0x190(t0)
    csrr t0, 0x7b2
    csrr t1, 0x7b3
    dret
