// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// KUDU-013 reached through the ALT (fall-through) buffer: a predicted-taken
// backward loop branch whose fall-through runs into an instruction-fetch-error
// word. On the final (mispredicted not-taken) iteration the fall-through is
// restored from the ALT buffer; the fall-through instructions before the error
// word must execute and the first instruction of the error word must take an
// instruction access fault. Needs +INSTR_ERR_ADDR=80010100.

#include <util.h>

#define ERR_BUF   0x80010000u
#define OK_BUF    0x80011000u
#define ERR_HW    128u                         // ERR_WORD = ERR_BUF + 0x100
#define ERR_WORD  (ERR_BUF + 2u * ERR_HW)
#define BUF_HW    160u
#define MAGIC_A4  0xdead0004u

#define C_NOP      0x0001u
#define C_LI_A5_3  0x478du
#define C_ADDI_A5M 0x17fdu                     // c.addi a5, -1
#define C_ADDI_A4  0x0705u                     // c.addi a4, 1
#define C_ADDI_A3  0x0685u                     // c.addi a3, 1
#define DIV_T6     0x034fcfb3u                 // div t6, t6, s4
#define JR_S3      0x00098067u

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

static unsigned short enc_cbnez_a5(int off)
{
    unsigned o = (unsigned)off;
    unsigned v = 0xe001u | (7u << 7);           // c.bnez, rs1' = a5
    v |= ((o >> 8) & 1) << 12;
    v |= ((o >> 3) & 3) << 10;
    v |= ((o >> 6) & 3) << 5;
    v |= ((o >> 1) & 3) << 3;
    v |= ((o >> 5) & 1) << 2;
    return (unsigned short)v;
}

static unsigned enc_bne_a5(int off)
{
    unsigned o = (unsigned)off;
    unsigned v = 0x63u | (1u << 12) | (15u << 15);
    v |= ((o >> 12) & 1) << 31;
    v |= ((o >> 5) & 0x3f) << 25;
    v |= ((o >> 1) & 0xf) << 8;
    v |= ((o >> 11) & 1) << 7;
    return v;
}

static void put32(volatile unsigned short *h, unsigned i, unsigned w)
{
    h[i] = (unsigned short)(w & 0xffff);
    h[i + 1] = (unsigned short)(w >> 16);
}

// Returns entry address; *nfall = fall-through halfwords executed before ERR word.
static unsigned build(unsigned base, unsigned b32, unsigned bpos, unsigned k, unsigned div,
                      unsigned *nfall)
{
    volatile unsigned short *h = (volatile unsigned short *)base;
    unsigned bsz = b32 ? 2 : 1;
    unsigned top = bpos - k - 1 - (div ? 2 : 0);
    for (unsigned i = 0; i < BUF_HW; ++i) h[i] = C_NOP;
    h[top - 1] = C_LI_A5_3;
    unsigned p = top;
    if (div) { put32(h, p, DIV_T6); p += 2; }
    h[p++] = C_ADDI_A5M;
    for (unsigned i = 0; i < k; ++i) h[p++] = C_ADDI_A3;
    int off = 2 * ((int)top - (int)bpos);
    if (b32) put32(h, bpos, enc_bne_a5(off));
    else h[bpos] = enc_cbnez_a5(off);
    for (unsigned i = bpos + bsz; i < ERR_HW; ++i) h[i] = C_ADDI_A4;
    *nfall = ERR_HW - (bpos + bsz);
    h[ERR_HW + 0] = C_ADDI_A4;
    h[ERR_HW + 1] = C_ADDI_A4;
    put32(h, ERR_HW + 2, JR_S3);
    return base + 2 * (top - 1);
}

int mymain(int argc, int argv)
{
    unsigned fails = 0, tries = 0, injecting = 0;
    (void)argc; (void)argv;
    for (unsigned b32 = 0; b32 < 2; ++b32)
        for (unsigned bpos = 116; bpos + (b32 ? 2 : 1) <= ERR_HW; ++bpos)
            for (unsigned k = 0; k < 4; ++k)
                for (unsigned div = 0; div < 2; ++div)
                    for (unsigned err = 0; err < 2; ++err) {
                        unsigned nfall, bad, k013 = 0;
                        unsigned base = err ? ERR_BUF : OK_BUF;
                        unsigned entry = build(base, b32, bpos, k, div, &nfall);
                        rv32_atest(&r, entry);
                        ++tries;
                        if (err) {
                            unsigned ew = base + 2 * ERR_HW;
                            if (r.trapped) injecting = 1;
                            bad = !(r.trapped == 1 && r.mcause == 1 && r.mepc == ew && r.mtval == ew &&
                                    r.a4 == MAGIC_A4 + nfall && r.a3 == 3 * k);
                            // KUDU-013 signature: the first instruction of the error word retired
                            k013 = r.trapped == 1 && r.mcause == 1 && r.mepc == ew + 2 && r.mtval == ew + 2 &&
                                   r.a4 == MAGIC_A4 + nfall + 1 && r.a3 == 3 * k;
                        } else {
                            bad = !(r.trapped == 0 && r.a4 == MAGIC_A4 + nfall + 2 && r.a3 == 3 * k);
                        }
                        if (bad) {
                            ++fails;
                            prints(k013 ? "ALTERR FAIL KUDU013 b32=" : "ALTERR FAIL MISMATCH b32="); hex(b32); prints(" bpos="); hex(bpos);
                            prints(" k="); hex(k); prints(" div="); hex(div); prints(" err="); hex(err);
                            prints(" nfall="); hex(nfall);
                            prints(" trapped="); hex(r.trapped); prints(" mcause="); hex(r.mcause);
                            prints(" mepc="); hex(r.mepc); prints(" mtval="); hex(r.mtval);
                            prints(" a4="); hex(r.a4); prints(" a3="); hex(r.a3); prints("\n");
                        }
                    }
    prints("ALTERR tries="); hex(tries); prints(" injecting="); hex(injecting); prints("\n");
    prints(fails || !injecting ? "ALTERR FAIL failures=" : "ALTERR PASS failures="); hex(fails); prints("\n");
    stop_sim();
    return fails != 0;
}
