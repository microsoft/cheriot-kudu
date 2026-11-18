// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// CHERIoT (PMODE=1) wrapper for the directed debug tests. MB_SAVE_RA holds a
// full-bounds code capability used to build mepcc values.

#define LDW(rd, off, rb)   clw x##rd, off(c##rb)
#define STW(rs, off, rb)   csw x##rs, off(c##rb)
#define LAC(rd, l)         97: auipcc c##rd, %cheri_compartment_pccrel_hi(l); cincoffset c##rd, c##rd, %cheri_compartment_pccrel_lo(97b)
#define LAI(rd, l)         LAC(rd, l); cgetaddr x##rd, c##rd
#define JR(rs)             cjr c##rs
#define CALL(l)            cjal cra, l
#define RET                cret
#define MOVP(rd, rs)       cmove c##rd, c##rs
#define MKPTR(rd, rs)      csetaddr c##rd, c8, x##rs
#define MKCPTR(rd, rs)     clc c##rd, MB_SAVE_RA(c9); csetaddr c##rd, c##rd, x##rs
#define PTRADD(rd, rs, i)  cincoffset c##rd, c##rs, i
#define SETMEPC(rs)        clc c13, MB_SAVE_RA(c9); csetaddr c13, c13, x##rs; cspecialw mepcc, c13
#define GETMEPC(rd)        cspecialr c##rd, mepcc; cgetaddr x##rd, c##rd
#define SETMTVEC(l)        LAC(13, l); cspecialw mtcc, c13
#define HSAVE12            csc c12, MB_SAVE_S0(c9)
#define HREST12            clc c12, MB_SAVE_S0(c9)
#define MEPC_ADD4          cspecialr c12, mepcc; cincoffset c12, c12, 4; cspecialw mepcc, c12
#define MSCR_SAVE13        cspecialw mscratchc, c13
#define MSCR_REST13        cspecialr c13, mscratchc
#define FN_ENTER           cincoffset csp, csp, -32; csc cra, 0(csp); csc cs0, 8(csp); csc cs1, 16(csp); cmove c9, c12; auipcc c13, 0; csc c13, MB_SAVE_RA(c9)
#define FN_EXIT            clc cra, 0(csp); clc cs0, 8(csp); clc cs1, 16(csp); cincoffset csp, csp, 32; cret

#define CASE_LIST DISPATCH 33; DISPATCH 34

#include "cases_common.S"
#include "cases_step.S"
