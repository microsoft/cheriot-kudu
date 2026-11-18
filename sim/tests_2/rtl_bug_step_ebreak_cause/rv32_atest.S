// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// RV32 (PMODE=0) wrapper for the directed debug tests.

#define LDW(rd, off, rb)   lw x##rd, off(x##rb)
#define STW(rs, off, rb)   sw x##rs, off(x##rb)
#define LAI(rd, l)         la x##rd, l
#define LAC(rd, l)         la x##rd, l
#define JR(rs)             jr x##rs
#define CALL(l)            jal x1, l
#define RET                ret
#define MOVP(rd, rs)       mv x##rd, x##rs
#define MKPTR(rd, rs)      mv x##rd, x##rs
#define MKCPTR(rd, rs)     mv x##rd, x##rs
#define PTRADD(rd, rs, i)  addi x##rd, x##rs, i
#define SETMEPC(rs)        csrw mepc, x##rs
#define GETMEPC(rd)        csrr x##rd, mepc
#define SETMTVEC(l)        la x13, l; csrw mtvec, x13
#define HSAVE12            sw x12, MB_HSAVE12(x9)
#define HREST12            lw x12, MB_HSAVE12(x9)
#define MEPC_ADD4          csrr x12, mepc; addi x12, x12, 4; csrw mepc, x12
#define MSCR_SAVE13        csrw mscratch, x13
#define MSCR_REST13        csrr x13, mscratch
#define FN_ENTER           addi sp, sp, -16; sw ra, 0(sp); sw s0, 4(sp); sw s1, 8(sp)
#define FN_EXIT            lw ra, 0(sp); lw s0, 4(sp); lw s1, 8(sp); addi sp, sp, 16; ret

#define CASE_LIST DISPATCH 33; DISPATCH 34

#include "cases_common.S"
#include "cases_step.S"
