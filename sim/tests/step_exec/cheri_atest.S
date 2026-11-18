// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// step_exec: deterministic instruction-mix workload, run with dcsr.step = 0
// and 1; results must match.

.option norelax
.option norvc
.section .text
.globl install_handler
.globl dbg_request
.globl workload

// funct5, rd, rs2, rs1 (rs1 is a capability register)
.macro AMO f5, rd, rs2, rs1
    .word ((\f5 << 27) | (\rs2 << 20) | (\rs1 << 15) | (2 << 12) | (\rd << 7) | 0x2f)
.endm

install_handler:
1:  auipcc c10, %cheri_compartment_pccrel_hi(trap_handler)
    cincoffset c10, c10, %cheri_compartment_pccrel_lo(1b)
    cspecialw mtcc, c10
    cret

// int dbg_request(volatile int *mb): raise debug_req, wait for a ROM entry.
// Returns 1 if the ROM was entered, 0 on timeout.
dbg_request:
    cspecialr c13, mtdc
    li x14, 0x83800000
    csetaddr c13, c13, x14
    cgetaddr x14, c10
    csw x14, 4(c13)          // scratch_reg1 = mailbox
    clw x15, 4(c10)
    li x14, 1
    csw x14, 320(c13)        // debug_req = 1
    li x12, 200000
1:  clw x11, 4(c10)
    bne x11, x15, 2f
    addi x12, x12, -1
    bnez x12, 1b
    li x10, 0
    cret
2:  li x10, 1
    cret

// Adds mcause to s1 and resumes at mepc + 4. Preserves everything but s1.
.balign 4
trap_handler:
    cspecialw mscratchc, c13
    csrr x13, mcause
    add x9, x9, x13
    cspecialr c13, mepcc
    cincoffset c13, c13, 4
    cspecialw mepcc, c13
    cspecialr c13, mscratchc
    mret

// int workload(int *buf, int seed, int iters)
// buf: 160 words, 8-byte aligned. Returns checksum; buf[150] = trap sum,
// buf[151] = SC.W failure count.
workload:
    cincoffset csp, csp, -32
    csc cs0, 0(csp)
    csc cs1, 8(csp)
    csc cra, 16(csp)
    li s0, 0x13579bdf
    li s1, 0
    mv a2, a2
loop:
    // LCG
    li t0, 1103515245
    mul a1, a1, t0
    li t0, 12345
    add a1, a1, t0
    // ALU
    srli t1, a1, 7
    xor s0, s0, t1
    slli t2, s0, 3
    srli t0, s0, 29
    or s0, t2, t0
    add s0, s0, a1
    sra t1, a1, a2
    sub s0, s0, t1
    sll t2, a1, a2
    xor s0, s0, t2
    srl t0, s0, a2
    add s0, s0, t0
    slt t2, a1, s0
    sltu t0, s0, a1
    add s0, s0, t2
    sub s0, s0, t0
    slti t1, a1, -5
    sltiu t2, a1, 100
    add s0, s0, t1
    add s0, s0, t2
    andi t0, a1, 0x3f0
    ori t1, s0, 0x101
    xori t2, a1, -1
    and t0, t0, t1
    or s0, s0, t0
    xor s0, s0, t2
    lui t0, 0xabcde
    add s0, s0, t0
    // mul family
    mulh t0, a1, s0
    mulhu t1, a1, s0
    mulhsu t2, s0, a1
    add s0, s0, t0
    xor s0, s0, t1
    sub s0, s0, t2
    // div family (divisor odd, plus divide by zero)
    ori t0, a1, 1
    div t1, s0, t0
    rem t2, s0, t0
    add s0, s0, t1
    xor s0, s0, t2
    divu t1, s0, t0
    remu t2, s0, t0
    add s0, s0, t1
    add s0, s0, t2
    divu t1, s0, zero
    rem t2, s0, zero
    xor s0, s0, t1
    add s0, s0, t2
    // memory: offset (a1 >> 8) & 0x1fc
    srli t0, a1, 8
    andi t0, t0, 0x1fc
    cincoffset c14, c10, t0
    clw t1, 0(c14)
    add s0, s0, t1
    csw s0, 0(c14)
    csh a1, 2(c14)
    csb s0, 1(c14)
    clw t1, 0(c14)
    clh t2, 2(c14)
    add s0, s0, t1
    xor s0, s0, t2
    clbu t0, 1(c14)
    clb t1, 3(c14)
    clhu t2, 0(c14)
    add s0, s0, t0
    sub s0, s0, t1
    add s0, s0, t2
    // second location, load right after store
    xori t0, t0, 0x10
    andi t0, t0, 0x1fc
    cincoffset c14, c10, t0
    csw a1, 0(c14)
    clw t1, 0(c14)
    add s0, s0, t1
    // branches
    andi t0, a1, 1
    beqz t0, 1f
    addi s0, s0, 77
1:  blt a1, s0, 2f
    xori s0, s0, 0x55
2:  bgeu a1, s0, 3f
    addi s0, s0, -3
3:  bne a1, s0, 4f
    addi s0, s0, 1
4:  bge s0, a1, 5f
    slli s0, s0, 1
5:  bltu s0, a1, 6f
    srli s0, s0, 1
6:
    // direct call
    cjal sub_mix
    // indirect call through a two-entry table
    andi t0, a1, 2
    slli t0, t0, 2           // 0 or 8
91: auipcc c14, %cheri_compartment_pccrel_hi(jtab)
    cincoffset c14, c14, %cheri_compartment_pccrel_lo(91b)
    cincoffset c14, c14, t0
    cjalr cra, c14
    // compressed instructions
.option rvc
    c.addi s0, 3
    c.slli s0, 1
    c.srli s0, 2
    c.srai s0, 1
    c.andi s0, -2
    c.add s0, a1
    c.xor s0, a1
    c.mv t0, s0
    c.sub s0, a1
    c.or s0, a1
    c.and s0, a1
    c.li t1, 9
    c.add s0, t1
    c.beqz a1, 7f
    c.addi s0, 5
7:  c.bnez s0, 8f
    c.addi s0, 1
8:  c.j 9f
    c.addi s0, 11
9:  c.nop
.option norvc
    .balign 4
    // SCR round trip
    cspecialw mscratchc, c14
    cspecialr c15, mscratchc
    cgetoffset t1, c15
    add s0, s0, t1
    // CHERI ops
    csetbounds c14, c10, 64
    cgetlen t0, c14
    cgettag t1, c14
    cgetperm t2, c14
    add s0, s0, t0
    add s0, s0, t1
    xor s0, s0, t2
    csc c14, 528(c10)
    clc c15, 528(c10)
    cgettag t0, c15
    cgetlen t1, c15
    add s0, s0, t0
    add s0, s0, t1
    cincoffset c15, c15, 12
    cgetoffset t2, c15
    add s0, s0, t2
    csub t0, c15, c14
    add s0, s0, t0
    // AMO / LR / SC on buf[130]
    cincoffset c13, c10, 520
    AMO 0, 5, 8, 13          // amoadd.w t0, s0, (c13)
    add s0, s0, t0
    AMO 1, 6, 11, 13         // amoswap.w t1, a1, (c13)
    xor s0, s0, t1
    AMO 4, 7, 8, 13          // amoxor.w t2, s0, (c13)
    add s0, s0, t2
    AMO 28, 5, 8, 13         // amomaxu.w t0, s0, (c13)
    add s0, s0, t0
    AMO 16, 6, 11, 13        // amomin.w t1, a1, (c13)
    xor s0, s0, t1
    AMO 2, 6, 0, 13          // lr.w t1, (c13)
    addi t1, t1, 1
    AMO 3, 7, 6, 13          // sc.w t2, t1, (c13)
    add s0, s0, t2           // sc failure (legal under step) cancels below
    clw t1, 604(c10)
    add t1, t1, t2
    csw t1, 604(c10)         // buf[151] = sc failure count
    clw t0, 0(c13)
    add s0, s0, t0
    // fences
    fence
    fence.i
    // traps: ecall when (iters & 7) == 0, illegal when (iters & 7) == 4
    andi t0, a2, 7
    bnez t0, 10f
    ecall
10: addi t0, t0, -4
    bnez t0, 11f
    .word 0xffffffff
11: add s0, s0, s1
    addi a2, a2, -1
    bnez a2, loop

    csw s1, 600(c10)
    mv a0, s0
    clc cs0, 0(csp)
    clc cs1, 8(csp)
    clc cra, 16(csp)
    cincoffset csp, csp, 32
    cret

sub_mix:
    slli t0, s0, 1
    add s0, s0, t0
    add s0, s0, a1
    cret

.balign 4
jtab:
    addi s0, s0, 5
    cret
    xori s0, s0, 0x33
    cret
