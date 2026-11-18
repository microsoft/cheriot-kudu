// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

extern unsigned sw_test(unsigned *rec);
static unsigned rec[12 * 8 * 3];

static void phex(unsigned v)
{
    const char *d = "0123456789abcdef";
    for (int k = 7; k >= 0; --k) send_char(d[(v >> (4 * k)) & 15]);
}

int mymain(int argc, int argv)
{
    static const char *nm[12] = {"st1 sw+13", "st1 sw+14", "st1 sw+15", "st1 sh+15",
                                 "st2 sw+13", "st2 sw+14", "st2 sw+15", "st2 sh+15",
                                 "ld1 lw+13", "ld1 lw+14", "ld1 lw+15", "ld1 lhu+15"};
    /* expected mapped-word contents if the non-faulting half is written */
    static const unsigned wexp[8] = {0x00000011, 0x00001122, 0x00112233, 0x00000033,
                                     0x22334400, 0x33440000, 0x44000000, 0x44000000};
    static const unsigned off[12] = {13, 14, 15, 15, 13, 14, 15, 15, 13, 14, 15, 15};
    unsigned nfail = 0;
    (void)argc; (void)argv;
    sw_test(rec);
    for (int o = 0; o < 12; ++o) {
        unsigned st = o < 8, base = (o >= 4 && o < 8) ? 0x8007fff0u : 0x7ffffff0u;
        unsigned a = base + off[o], hi = (a & ~3u) + 4;
        unsigned n_orig = 0, n_hi = 0, n_bad = 0, n_wr = 0, n_nowr = 0, b0 = 0, b1 = 0, b2 = 0;
        for (int r = 0; r < 8; ++r) {
            unsigned *p = &rec[(o * 8 + r) * 3];
            int ok = p[0] == (st ? 7u : 5u);
            if (!st) ok = ok && p[2] == 0xdeadbeefu;
            if (ok && p[1] == a) n_orig++;
            else if (ok && p[1] == hi && o >= 4 && o < 8) n_hi++;
            else { if (!n_bad) { b0 = p[0]; b1 = p[1]; b2 = p[2]; } n_bad++; }
            if (st && p[2] == wexp[o]) n_wr++;
            else if (st && p[2] == 0) n_nowr++;
            else if (st) { if (!n_bad) { b0 = p[0]; b1 = p[1]; b2 = p[2]; } n_bad++; }
        }
        prints(n_bad ? "FAIL " : "INFO ");
        prints((char *)nm[o]);
        prints(" mtval=orig:"); phex(n_orig);
        prints(" mtval=hiword:"); phex(n_hi);
        if (st) { prints(" other_half_written:"); phex(n_wr); prints(" not_written:"); phex(n_nowr); }
        prints(" bad:"); phex(n_bad);
        if (n_bad) { prints(" first_bad "); phex(b0); send_char(' '); phex(b1); send_char(' '); phex(b2); }
        prints("\n");
        nfail += n_bad != 0;
    }
    prints(nfail ? "SPLIT WR FAIL\n" : "SPLIT WR DONE\n");
    stop_sim();
    return 0;
}
