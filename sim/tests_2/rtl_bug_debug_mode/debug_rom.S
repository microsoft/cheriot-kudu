// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Debug ROM for rtl_bug_debug_mode. The test writes the integer address of
// its mailbox to TB scratch_reg1 (0x8380_0004) and the case number to mb[0],
// then raises debug_req. CHERI checks are off in debug mode, so the ROM uses
// untagged integer addresses. It may clobber t0-t2 and a0-a5 only.
// At PMODE=1 the RV32 dpc/dscratch CSRs are illegal, so dpc is read through
// DEPCC (SCR 24). a1 (x11) selects where rom_exc resumes in case P1.
// Offset +0 is the halt entry (DmHaltAddr) and +8 the debug-mode exception
// entry (DmExcAddr).
//
// Mailbox (32-bit words):
//   0 case          1 ROM entry count   2 in-ROM flag    3 mtvec hits
//   4..11 results   12 DmExcAddr hits   13 handler mcause 14 handler mepcc
//   15 fall-through mark

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
    clw x10, 0(c5)           // case number
    li x11, 0                // no P1 resume point

    li x7, 1
    beq x10, x7, case_ebreak_m1
    li x7, 2
    beq x10, x7, case_ebreak_m0
    li x7, 3
    beq x10, x7, case_illegal
    li x7, 4
    beq x10, x7, case_csr
    li x7, 5
    beq x10, x7, case_clc
    li x7, 6
    beq x10, x7, case_pcc
    li x7, 7
    beq x10, x7, case_dpc
    j rom_exit

// D1: ebreak in debug mode with dcsr.ebreakm = 1 must halt again without
// updating dpc or dcsr.
case_ebreak_m1:
    li x7, 2
    beq x6, x7, ebreak_second_entry
    cspecialr c7, 24         // DEPCC
    cspecialw 26, c7         // save it in DSCRATCHC1 for the restore
    csw x7, 16(c5)           // mb[4] = dpc before ebreak
    csrr x7, 0x7b0           // dcsr
    csw x7, 20(c5)           // mb[5] = dcsr before ebreak
    li x7, 0x8000
    csrs 0x7b0, x7           // dcsr.ebreakm = 1
    ebreak
    li x7, 0xbad1
    csw x7, 60(c5)           // ebreak fell through
    j rom_exit

// D1: ebreak in debug mode with dcsr.ebreakm = 0 must also halt again
// (it must not take a breakpoint exception to mtvec).
case_ebreak_m0:
    li x7, 2
    beq x6, x7, ebreak_second_entry
    cspecialr c7, 24
    cspecialw 26, c7
    csw x7, 16(c5)
    csrr x7, 0x7b0
    csw x7, 20(c5)
    li x7, 0x8000
    csrc 0x7b0, x7           // dcsr.ebreakm = 0
    ebreak
    li x7, 0xbad2
    csw x7, 60(c5)
    j rom_exit

ebreak_second_entry:
    cspecialr c7, 24
    csw x7, 24(c5)           // mb[6] = dpc after re-entry
    csrr x7, 0x7b0
    csw x7, 28(c5)           // mb[7] = dcsr after re-entry
    li x7, 0x8000
    csrc 0x7b0, x7
    cspecialr c7, 26         // restore the original DEPCC
    cspecialw 24, c7
    j rom_exit

// D2: an illegal instruction in debug mode must trap, but must not run the
// M-mode handler at mtvec.
case_illegal:
    .word 0xffffffff
    li x7, 0xbad3
    csw x7, 60(c5)
    j rom_exit

// D3: an illegal CSR access in debug mode must raise an illegal-instruction
// exception. mtvec is illegal at PMODE=1 and 0x3ff is unimplemented.
case_csr:
    li x7, 0x5a5a5a5a
    csrr x7, 0x305           // mtvec
    csw x7, 16(c5)           // mb[4]
    li x7, 0x5a5a5a5a
    csrr x7, 0x3ff
    csw x7, 20(c5)           // mb[5]
    li x7, 0xbad4
    csw x7, 60(c5)           // no trap
    j rom_exit

// D4: CLC must apply the load-permission stripping exactly as outside debug
// mode. c8 = authority without MC, c9 = authority without LM (set up by the
// test). Both point at a valid stored capability.
case_clc:
    clc c6, 0(c8)
    cgettag x7, c6
    csw x7, 16(c5)           // mb[4] = tag via no-MC authority
    clc c6, 0(c9)
    cgetperm x7, c6
    csw x7, 20(c5)           // mb[5] = perms via no-LM authority
    cgettag x7, c6
    csw x7, 24(c5)           // mb[6] = tag via no-LM authority
    j rom_exit

// D5: PCC seen by debug-mode code.
case_pcc:
    auipcc c6, 0
    cgetbase x7, c6
    csw x7, 16(c5)           // mb[4]
    cgetlen x7, c6
    csw x7, 20(c5)           // mb[5]
    cgetperm x7, c6
    csw x7, 24(c5)           // mb[6]
    cgettag x7, c6
    csw x7, 28(c5)           // mb[7]
    j rom_exit

// P1: at PMODE=1 the RV32 dpc/dscratch1 CSRs must be illegal in debug mode.
// Each of the four accesses must trap to DmExcAddr (counted in mb[12]);
// rom_exc resumes at the next step selected by x11. DEPCC and DSCRATCHC1
// must be unchanged.
case_dpc:
    cspecialr c7, 24
    csw x7, 16(c5)           // mb[4] = dpc before
    cspecialr c7, 26
    csw x7, 28(c5)           // mb[7] = dscratch1 before
    li x11, 1
    csrr x7, 0x7b1           // csrr dpc
p1_s2:
    li x11, 2
    clw x7, 16(c5)
    addi x7, x7, 4
    csrw 0x7b1, x7           // csrw dpc, dpc+4
p1_s3:
    li x11, 3
    li x7, 0x1234
    csrw 0x7b3, x7           // csrw dscratch1, 0x1234
p1_s4:
    li x11, 4
    csrr x7, 0x7b3           // csrr dscratch1
p1_done:
    li x11, 0
    cspecialr c7, 24
    csw x7, 20(c5)           // mb[5] = dpc after
    cspecialr c7, 26
    csw x7, 24(c5)           // mb[6] = dscratch1 after
    j rom_exit

// Exception taken in debug mode: count it in mb[12], then resume at the P1
// step selected by x11, or leave.
rom_exc:
    clw x7, 48(c5)
    addi x7, x7, 1
    csw x7, 48(c5)
    li x7, 1
    beq x11, x7, p1_s2
    li x7, 2
    beq x11, x7, p1_s3
    li x7, 3
    beq x11, x7, p1_s4
    li x7, 4
    beq x11, x7, p1_done
    j rom_exit

rom_exit:
    csw x0, 8(c5)            // clear in-ROM flag
    dret
