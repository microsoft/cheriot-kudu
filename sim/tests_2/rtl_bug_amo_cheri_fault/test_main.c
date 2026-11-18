// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

#define NOBS 5
#define NCASES 8
#define MEM_INIT 0x11223344u
#define DATA 0xaabbccddu
#define RD_INIT 0xdeadbeefu
#define CHERI_FAULT 0x1cu
#define MTVAL_C14_SD 0x1d3u   // (14 << 5) | SD violation (0x13)
#define MTVAL_C14_LD 0x1d2u   // (14 << 5) | LD violation (0x12)
#define MPIE 0x80u

struct obs { unsigned rd, unused0, mem, trapped, mcause, mtval, mstatus, unused1; };
extern void cheri_atest(struct obs *results, unsigned *word);
static struct obs r[NOBS];
static unsigned word[2] __attribute__((aligned(8)));

static void hex(unsigned value)
{
    const char *digits = "0123456789abcdef";
    prints("0x");
    for (int i = 7; i >= 0; --i)
        send_char(digits[(value >> (4 * i)) & 15]);
}

static void dec(unsigned v)
{
    char buf[11];
    int n = 0;
    do {
        buf[n++] = '0' + v % 10;
        v /= 10;
    } while (v);
    while (n)
        send_char(buf[--n]);
}

static unsigned report(int ok, const char *tag, const struct obs *o, unsigned mtval_exp)
{
    prints(ok ? "PASS " : "FAIL ");
    prints((char *)tag);
    prints(" trapped="); hex(o->trapped);
    prints(" mcause="); hex(o->mcause);
    prints(" mtval="); hex(o->mtval);
    prints(" (exp "); hex(mtval_exp);
    prints(") rd="); hex(o->rd);
    prints(" mem="); hex(o->mem);
    prints(" handler_mstatus="); hex(o->mstatus);
    prints("\n");
    return !ok;
}

// Trapped with the expected CHERI fault, rd and memory untouched.
static int clean_fault(const struct obs *o, unsigned mtval)
{
    return o->trapped == 1 && o->mcause == CHERI_FAULT && o->mtval == mtval &&
           o->rd == RD_INIT && o->mem == MEM_INIT;
}

static int mpie_set(const struct obs *o)
{
    return o->trapped == 1 && (o->mstatus & MPIE) != 0;
}

int mymain(int argc, int argv)
{
    unsigned f = 0;
    (void)argc;
    (void)argv;
    // cheri_atest initialises every field it reports before each case.
    cheri_atest(r, word);

    // KUDU-032: SD violation must be raised before the AMO writes rd.
    f += report(clean_fault(&r[0], MTVAL_C14_SD), "amo-rd amoswap.w LD-only cap: SD fault, rd kept:",
                &r[0], MTVAL_C14_SD);
    f += report(clean_fault(&r[1], MTVAL_C14_SD), "amo-rd amoadd.w LD-only cap: SD fault, rd kept:",
                &r[1], MTVAL_C14_SD);
    // KUDU-036: mstatus.MPIE must capture MIE=1 when an AMO traps.
    f += report(mpie_set(&r[0]), "amo-mpie amoswap.w LD-only cap: MPIE=1 in handler:",
                &r[0], MTVAL_C14_SD);
    f += report(mpie_set(&r[1]), "amo-mpie amoadd.w LD-only cap: MPIE=1 in handler:",
                &r[1], MTVAL_C14_SD);
    f += report(mpie_set(&r[2]), "amo-mpie amoswap.w SD-only cap: MPIE=1 in handler:",
                &r[2], MTVAL_C14_LD);
    // Controls.
    f += report(clean_fault(&r[2], MTVAL_C14_LD), "ctrl amoswap.w SD-only cap: LD fault, rd kept:",
                &r[2], MTVAL_C14_LD);
    f += report(r[3].trapped == 0 && r[3].rd == MEM_INIT && r[3].mem == DATA,
                "ctrl amoswap.w LD+SD cap succeeds:", &r[3], 0);
    f += report(r[4].trapped == 1 && r[4].mcause == CHERI_FAULT && r[4].mtval == MTVAL_C14_SD &&
                    r[4].mem == MEM_INIT && (r[4].mstatus & MPIE) != 0,
                "ctrl csw LD-only cap: SD fault, MPIE=1:", &r[4], MTVAL_C14_SD);

    prints(f ? "AMO CHERI FAULT FAIL failures=" : "AMO CHERI FAULT PASS failures=");
    dec(f);
    prints(" cases=");
    dec(NCASES);
    prints("\n");
    stop_sim();
    return f != 0;
}
