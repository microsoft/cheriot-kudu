// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

#define NCASES 4
#define MEM_INIT 0x11223344u
#define DATA 0x5a5a5a5au
#define RD_INIT 0xdeadbeefu

struct obs { unsigned mshwm, base, rd, mem; };
extern void cheri_atest(struct obs *results, unsigned *block);
static struct obs r[NCASES];
static unsigned block[4] __attribute__((aligned(16)));

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

static unsigned report(int i, unsigned mshwm, unsigned rd, unsigned mem, const char *tag)
{
    int ok = r[i].mshwm == mshwm && r[i].rd == rd && r[i].mem == mem;
    prints(ok ? "PASS " : "FAIL ");
    prints((char *)tag);
    prints(" mshwm="); hex(r[i].mshwm);
    prints(" rd="); hex(r[i].rd);
    prints(" mem="); hex(r[i].mem);
    prints(" expected="); hex(mshwm);
    prints("/"); hex(rd);
    prints("/"); hex(mem);
    prints("\n");
    return !ok;
}

int mymain(int argc, int argv)
{
    unsigned f = 0;
    (void)argc;
    (void)argv;
    // cheri_atest writes every field of every case.
    cheri_atest(r, block);
    // Each case arms MSHWMB = block, MSHWM = block + 16 and writes block + 4.
    f += report(0, r[0].base, 0, DATA, "sc-mshwm lr.w; sc.w success lowers MSHWM:");
    f += report(1, r[1].base, RD_INIT, DATA, "ctrl csw lowers MSHWM:");
    f += report(2, r[2].base, MEM_INIT, DATA, "ctrl amoswap.w lowers MSHWM:");
    f += report(3, r[3].base + 16, 1, MEM_INIT, "ctrl failed sc.w leaves MSHWM:");
    prints(f ? "SC MSHWM FAIL failures=" : "SC MSHWM PASS failures=");
    dec(f);
    prints(" cases=");
    dec(NCASES);
    prints("\n");
    stop_sim();
    return f != 0;
}
