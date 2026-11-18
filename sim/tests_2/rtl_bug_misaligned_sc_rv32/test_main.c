// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

#define NCASES 7
#define W0 0x11223344u
#define W1 0x55667788u
#define DATA 0xaabbccddu
#define RD_INIT 0xdeadbeefu

struct obs { unsigned rd, w0, w1, trapped, mcause, mtval, pad0, pad1; };
extern void rv32_atest(struct obs *r);
static struct obs r[NCASES];

static void hex(unsigned v)
{
    const char *digits = "0123456789abcdef";
    prints("0x");
    for (int i = 7; i >= 0; --i)
        send_char(digits[(v >> (4 * i)) & 15]);
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

static unsigned report(int i, int ok, const char *tag)
{
    prints(ok ? "PASS " : "FAIL ");
    prints((char *)tag);
    prints(" trapped="); hex(r[i].trapped);
    prints(" mcause="); hex(r[i].mcause);
    prints(" rd="); hex(r[i].rd);
    prints(" w0="); hex(r[i].w0);
    prints(" w1="); hex(r[i].w1);
    prints(" mtval(info)="); hex(r[i].mtval);
    prints("\n");
    return !ok;
}

static int trapped_unchanged(int i, unsigned cause)
{
    return r[i].trapped == 1 && r[i].mcause == cause && r[i].rd == RD_INIT &&
           r[i].w0 == W0 && r[i].w1 == W1;
}

int mymain(int argc, int argv)
{
    unsigned failures = 0;
    (void)argc;
    (void)argv;
    for (int i = 0; i < NCASES; ++i) {
        r[i].rd = r[i].w0 = r[i].w1 = r[i].mtval = 0;
        r[i].trapped = r[i].mcause = r[i].pad0 = r[i].pad1 = 0;
    }
    rv32_atest(r);

    // Misaligned SC with a valid reservation: SAMO-misaligned trap, no write.
    failures += report(0, trapped_unchanged(0, 6), "misaligned-sc lr.w X; sc.w X+1:");
    failures += report(1, trapped_unchanged(1, 6), "misaligned-sc lr.w X; sc.w X+2:");
    failures += report(2, trapped_unchanged(2, 6), "misaligned-sc lr.w X; sc.w X+3:");
    // Trapping misaligned LR must not register a reservation: a later SC fails.
    failures += report(3, r[3].trapped == 1 && r[3].mcause == 4 && r[3].rd == 1 &&
                          r[3].w0 == W0 && r[3].w1 == W1,
                       "misaligned-sc lr.w X+2 (trap); sc.w X must fail rd=1:");
    // Controls.
    failures += report(4, trapped_unchanged(4, 6), "ctrl amoswap.w X+2 traps, no write:");
    failures += report(5, trapped_unchanged(5, 4), "ctrl lr.w X+2 traps, rd kept:");
    failures += report(6, r[6].trapped == 0 && r[6].rd == 0 && r[6].w0 == DATA && r[6].w1 == W1,
                       "ctrl aligned lr.w X; sc.w X succeeds:");

    prints(failures ? "MISALIGNED SC RV32 FAIL failures=" : "MISALIGNED SC RV32 PASS failures=");
    dec(failures);
    prints(" cases=");
    dec(NCASES);
    prints("\n");
    stop_sim();
    return failures != 0;
}
