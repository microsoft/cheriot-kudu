# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# KUDU-072: an interrupt whose pending line withdraws (without a CPU ack)
# just after the core decided to take it is still taken, with
# mcause = machine timer (0x80000007), although MTIE = 0 and MTIP = 0.
#
# Uses the collide testbench scheduler (common/patches/collide_sched.patch):
# only fast interrupt 0 (mie bit 16, TB irq vector bit 3) is enabled. A pulse
# on that line of hold H in {1,2,3,4} cycles is fired D in {1..12} cycles after
# the arming store, followed by 24 x c.addi. Every interrupt taken must report
# mcause 0x80000010; the handler counts any other cause.
# Prints "IRQ WITHDRAW PASS ..." or "FAIL irq-withdraw bad_mcause=<n> ...".
.option norelax
.section .text.low, "ax"
.globl _start
.org 0x80
_start:
    j main
.org 0x100
vecA:                         # direct-mode trap handler; uses s9..s11 only
    addi s10, s10, 1          # traps taken
    csrr s11, mcause
    li t6, 0x80000010
    beq s11, t6, 1f
    addi s9, s9, 1            # bad cause
    bltz s11, 1f
    j vecA                    # an exception is a test error: hang -> timeout
1:  li s11, 0x8
    sw s11, 0x104(s0)         # ack fast0 (no-op if the line already withdrew)
    mret
.section .text
main:
    li s0, 0x83800000
    li s9, 0
    li s10, 0
    la t0, vecA
    csrw mtvec, t0
    li t0, 0x8                # scheduler IRQ vector: TB bit 3 = fast0
    sw t0, 0x164(s0)
    li t0, 0x10000            # mie: fast0 only
    csrw mie, t0
    csrsi mstatus, 8          # mstatus.MIE
    li s1, 1                  # hold
1:  li s2, 1                  # delay
2:  slli t0, s1, 12
    or t0, t0, s2
    li t1, 0x1000000          # arm IRQ
    or t0, t0, t1
    sw t0, 0x160(s0)
    .rept 24
    c.addi a0, 1
    .endr
    addi s2, s2, 1
    li t1, 13
    blt s2, t1, 2b
    addi s1, s1, 1
    li t1, 5
    blt s1, t1, 1b
    csrci mstatus, 8

    bnez s9, 3f
    la a0, msg_pass
    jal puts
    j 4f
3:  la a0, msg_fail
    jal puts
    mv a0, s9
    jal puthex
4:  la a0, msg_traps
    jal puts
    mv a0, s10
    jal puthex
    li t0, 10
    sw t0, 0x200(s0)
    li t0, 0x80
    sw t0, 0x200(s0)
5:  j 5b

puts:                         # a0: NUL-terminated string -> UART
    lbu t0, 0(a0)
    beqz t0, 1f
    sw t0, 0x200(s0)
    addi a0, a0, 1
    j puts
1:  ret

puthex:                       # a0: value -> 8 hex digits
    li t1, 28
1:  srl t0, a0, t1
    andi t0, t0, 15
    addi t0, t0, '0'
    li t2, '9'
    ble t0, t2, 2f
    addi t0, t0, 'a' - '0' - 10
2:  sw t0, 0x200(s0)
    addi t1, t1, -4
    bgez t1, 1b
    ret

msg_pass:  .asciz "IRQ WITHDRAW PASS"
msg_fail:  .asciz "FAIL irq-withdraw bad_mcause=0x"
msg_traps: .asciz " traps=0x"
