# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# KUDU-073: a debug request withdrawn shortly after the core decided to halt
# still enters debug mode, with dcsr.cause = 0.
#
# Uses the collide testbench scheduler (common/patches/collide_sched.patch):
# a debug_req pulse of hold H in {1,2,3,4} cycles is fired D in {1..12} cycles
# after the arming store, followed by 24 x c.addi. The debug ROM (debug_rom.S,
# mailbox 0 = allowed-cause mask = HALTREQ only) counts every entry whose
# dcsr.cause is not 3 in scratch1 (0x8380_0004). A 1-cycle pulse may be
# ignored; a pulse that halts must report cause 3.
# Prints "DBG WITHDRAW PASS ..." or "FAIL dbg-withdraw bad_cause=<n> ...".
.option norelax
.section .text.low, "ax"
.globl _start
.org 0x80
_start:
    j main
.org 0x100
vecA:
    j vecA
.section .text
main:
    li s0, 0x83800000
    la t0, vecA
    csrw mtvec, t0
    li s8, 0                  # no ROM dpc redirect
    li t0, 0x8
    sw t0, 0x170(s0)          # mb0: only cause 3 allowed
    sw zero, 0x17c(s0)        # mb3: no step
    sw zero, 0x180(s0)        # mb4: ebreakm=0
    sw zero, 0x184(s0)        # mb5: no trigger
    li s1, 1                  # hold
1:  li s2, 1                  # delay
2:  slli t0, s1, 12
    or t0, t0, s2
    li t1, 0x2000000          # debug_req
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

    lw s3, 4(s0)              # scratch1: entries with a bad cause
    lw s4, 0(s0)              # scratch0: debug entries
    bnez s3, 3f
    la a0, msg_pass
    jal puts
    j 4f
3:  la a0, msg_fail
    jal puts
    mv a0, s3
    jal puthex
4:  la a0, msg_entries
    jal puts
    mv a0, s4
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

msg_pass:    .asciz "DBG WITHDRAW PASS"
msg_fail:    .asciz "FAIL dbg-withdraw bad_cause=0x"
msg_entries: .asciz " entries=0x"
