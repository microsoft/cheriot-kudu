# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# KUDU-049: the return-address prediction register (ir_stage cur_ra32_q)
# reset to RALimitLo (0x00080000) instead of {RALimitLo, 12'h0}
# (0x80000000), so a return predicted before any in-range write to x1
# fetched from unpopulated address 0x00080000.
#
# Phase 1 (from reset, before anything writes x1): the RA review's startup
# sequence. Each always-taken beq skips a c.jr ra (0x8082) that lies on the
# fall-through path; the c.jr ra is fetched before the beq resolves, and
# the front end predicts it as a return to cur_ra32.
# Phase 2: x1 is set to an out-of-range value (0x2000), which the RA clamp
# ignores, so cur_ra32 keeps its reset value; then the same pattern repeats
# at fresh addresses (no BHT history) with 0- and 2-byte alignment offsets.
# The checker (ra_rst_chk.sv) counts the predicted returns and flags any
# instruction fetch outside populated memory. The program prints
# "RA RESET PROGRAM DONE" and stops the simulation through the UART.
.option norelax
.option norvc
.section .text.low, "ax"
.globl _start
.org 0x80
_start:
    beq x0, x0, 9f
    .2byte 0x8082
    .2byte 0x8082
    nop
    nop
9:
    beq x0, x0, 8f
    nop
    .2byte 0x8082
    nop
8:
    j main

.section .text
.macro WRONG_PATH_RET pad
    .balign 8
    .if \pad
    .2byte 0x0001             # c.nop: shift the pattern by 2 bytes
    .endif
    beq x0, x0, 1f
    .2byte 0x8082
    .2byte 0x8082
    nop
1:  beq x0, x0, 2f
    nop
    .2byte 0x8082
    nop
2:
.endm

main:
    li ra, 0x00002000         # out of RA range: cur_ra32 keeps its reset value
    WRONG_PATH_RET 0
    WRONG_PATH_RET 1
    WRONG_PATH_RET 0
    WRONG_PATH_RET 1
    WRONG_PATH_RET 0
    WRONG_PATH_RET 1
    WRONG_PATH_RET 0
    WRONG_PATH_RET 1

    li s0, 0x83800000
    la a0, msg_done
    jal puts
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

msg_done: .asciz "RA RESET PROGRAM DONE"
