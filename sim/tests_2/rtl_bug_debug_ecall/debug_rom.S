// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Debug ROM for rtl_bug_debug_ecall. The test writes the integer address of
// its mailbox to TB scratch_reg1 (0x8380_0004) and the case number to mb[0],
// then raises debug_req. CHERI checks are off in debug mode, so the ROM uses
// untagged integer addresses. It may clobber t0-t2 and a0-a5 only.
// Offset +0 is the halt entry (DmHaltAddr) and +8 the debug-mode exception
// entry (DmExcAddr).
//
// Mailbox (32-bit words):
//   0 case          1 ROM entry count   2 in-ROM flag    3 mtvec hits
//   4 mcause before 5 MEPCC before      6 mcause at DmExcAddr
//   7 MEPCC at DmExcAddr                12 DmExcAddr hits
//   13 handler mcause 14 handler mepcc  15 fall-through mark

.section .text
.globl _start

_start:
    .option push
    .option norvc
    j rom_start              // +0: DmHaltAddr
    nop
    j rom_exc                // +8: DmExcAddr
    .option pop

rom_start:
    li x5, 0x83800000
    csw x0, 0x140(c5)        // deassert debug_req
    clw x5, 4(c5)            // x5 = mailbox address
    clw x6, 4(c5)
    addi x6, x6, 1
    csw x6, 4(c5)            // entry count++
    li x7, 1
    csw x7, 8(c5)            // in-ROM flag
    csrr x7, mcause
    csw x7, 16(c5)           // mb[4]
    cspecialr c7, 31         // MEPCC
    csw x7, 20(c5)           // mb[5]
    clw x10, 0(c5)           // case number

    li x7, 1
    beq x10, x7, case_ecall
    li x7, 2
    beq x10, x7, case_illegal
    j rom_exit

// E1: ECALL in debug mode must enter DmExcAddr without updating any
// register; it must not run the M-mode handler at mtvec.
case_ecall:
    ecall
    li x7, 0xbad1
    csw x7, 60(c5)           // ecall fell through
    j rom_exit

// E2 (control, KUDU-022): an illegal instruction in debug mode enters
// DmExcAddr.
case_illegal:
    .word 0xffffffff
    li x7, 0xbad2
    csw x7, 60(c5)
    j rom_exit

// Exception taken in debug mode: count it and record mcause/MEPCC.
rom_exc:
    clw x7, 48(c5)
    addi x7, x7, 1
    csw x7, 48(c5)           // mb[12]
    csrr x7, mcause
    csw x7, 24(c5)           // mb[6]
    cspecialr c7, 31
    csw x7, 28(c5)           // mb[7]

rom_exit:
    csw x0, 8(c5)            // clear in-ROM flag
    dret
