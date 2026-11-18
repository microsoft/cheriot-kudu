// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// KUDU-013 straddle: a 32-bit "addi a3,x0,6" starts at ERR_WORD-2 and its
// upper half lies in the faulting 64-bit word ERR_WORD.  Different layouts of
// the preceding instructions, entry points and stall padding make the aligner
// hand it out as slot 0 or slot 1.  Expected: mcause 1, mepc = ERR_WORD-2,
// mtval = ERR_WORD, a3 untouched (0), a4 untouched.

#include <util.h>

#define ERR_BUF   0x80010000u
#define ERR_WORD  0x80010060u
#define OK_BUF    0x80011000u
#define NHW       128u
#define MAGIC_A4  0xdead0004u
#define ERR_HW    (0x60u / 2u)                // halfword index of ERR_WORD

struct obs { unsigned trapped, mcause, mepc, mtval, a4, a3; };
extern void rv32_atest(struct obs *r, unsigned entry);
static struct obs r;

static void hex(unsigned v)
{
    char t[] = "0x00000000";
    const char *d = "0123456789abcdef";
    for (unsigned i = 0; i < 8; ++i) t[9 - i] = d[(v >> (4 * i)) & 15];
    prints(t);
}

static void put32(volatile unsigned short *h, unsigned i, unsigned w)
{
    h[i] = w & 0xffff; h[i + 1] = w >> 16;
}

// Layouts of the 64-bit word N (halfwords ERR_HW-4 .. ERR_HW-1) and of the
// tail of word N-1.  'C' = 16-bit, 'W' = 32-bit, S = straddler at ERR_HW-1.
//   0: N = C C C S
//   1: N = C W S
//   2: N = W C S
//   3: N-1 = W C C ; N = W C S
//   4: N-1 = C W C ; N = C W S
//   5: N-1 = W W   ; N = C C C S
//   6: N-1 = W C C ; N = C W S
//   7: N-1 = C W C ; N = W C S
#define NLAY 8
static const char *lay_n[NLAY]   = { "CCC", "CW", "WC", "WC", "CW", "CCC", "CW", "WC" };
static const char *lay_nm1[NLAY] = { "WW",  "WW", "WW", "WCC", "CWC", "WW", "WCC", "CWC" };

static unsigned emit(volatile unsigned short *h, unsigned i, const char *s,
                     unsigned *bnd, unsigned *nb)
{
    for (; *s; ++s) {
        bnd[(*nb)++] = i;
        if (*s == 'C') { h[i] = 0x4615; i += 1; }                 // c.li a2,5
        else           { put32(h, i, 0x01100813u); i += 2; }      // addi a6,x0,0x11
    }
    return i;
}

#define DIV_T6 0x034fcfb3u
#define ADD_T6 0x01ff8fb3u
#define NOP    0x00000013u

// entry: -1..-6 = DIV stall + (-entry-1) NOP words before word N-1;
//        k >= 0 = jump directly to the k-th instruction boundary of N-1/N.
static unsigned build(unsigned base, unsigned lay, int entry, unsigned *ok)
{
    volatile unsigned short *h = (volatile unsigned short *)base;
    unsigned bnd[16], nb = 0, i;
    for (i = 0; i < NHW; i += 2) put32(h, i, NOP);
    i = emit(h, ERR_HW - 8, lay_nm1[lay], bnd, &nb);
    if (i != ERR_HW - 4) { *ok = 0; return 0; }
    i = emit(h, ERR_HW - 4, lay_n[lay], bnd, &nb);
    if (i != ERR_HW - 1) { *ok = 0; return 0; }
    bnd[nb++] = i;
    put32(h, ERR_HW - 1, 0x00600693u);      // addi a3,x0,6 (straddler)
    h[ERR_HW + 1] = 0x0001;                 // c.nop
    put32(h, ERR_HW + 2, 0x04400713u);      // addi a4,x0,0x44
    put32(h, ERR_HW + 4, 0x05500793u);      // addi a5,x0,0x55
    put32(h, ERR_HW + 6, 0x00098067u);      // jalr x0,0(s3)
    *ok = 1;
    if (entry >= 0) {
        if ((unsigned)entry >= nb) { *ok = 0; return 0; }
        return base + 2 * bnd[entry];
    }
    unsigned pad = (unsigned)(-entry - 1);
    unsigned e = ERR_HW - 8 - 2 * pad - 6;
    put32(h, e, DIV_T6); put32(h, e + 2, DIV_T6); put32(h, e + 4, ADD_T6);
    return base + 2 * e;
}

int mymain(int argc, int argv)
{
    unsigned fails = 0, tries = 0, ctrl_bad = 0, mt_pc = 0, other = 0, ok;
    (void)argc; (void)argv;
    for (unsigned lay = 0; lay < NLAY; ++lay)
        for (int entry = -6; entry < 10; ++entry) {
            unsigned e = build(OK_BUF, lay, entry, &ok);
            if (!ok) continue;
            rv32_atest(&r, e);
            if (r.trapped || r.a4 != 0x44 || r.a3 != 6) {
                ++ctrl_bad;
                prints("FSTR_INFO ctrl wrong lay="); hex(lay); prints(" entry="); hex((unsigned)entry);
                prints(" mepc="); hex(r.mepc); prints("\n");
            }
            e = build(ERR_BUF, lay, entry, &ok);
            rv32_atest(&r, e);
            ++tries;
            unsigned good = r.trapped == 1 && r.mcause == 1 && r.mepc == ERR_WORD - 2 &&
                            r.mtval == ERR_WORD && r.a4 == MAGIC_A4 && r.a3 == 0;
            unsigned pcval = r.trapped == 1 && r.mcause == 1 && r.mepc == ERR_WORD - 2 &&
                             r.mtval == ERR_WORD - 2 && r.a4 == MAGIC_A4 && r.a3 == 0;
            mt_pc += pcval;
            other += !good && !pcval;
            fails += !good;
            prints("FSTR_INFO lay="); hex(lay); prints(" entry="); hex((unsigned)entry);
            prints(good ? " ok" : (pcval ? " mtval=pc" : " wrong"));
            prints(" trapped="); hex(r.trapped); prints(" mcause="); hex(r.mcause);
            prints(" mepc="); hex(r.mepc); prints(" mtval="); hex(r.mtval);
            prints(" a4="); hex(r.a4); prints(" a3="); hex(r.a3); prints("\n");
        }
    prints(fails || ctrl_bad ? "FSTR FAIL" : "FSTR PASS");
    prints(" tries="); hex(tries); prints(" fails="); hex(fails);
    prints(" mtval_eq_pc="); hex(mt_pc); prints(" other="); hex(other);
    prints(" ctrl_bad="); hex(ctrl_bad); prints("\n");
    stop_sim();
    return fails != 0;
}
