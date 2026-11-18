// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

extern void cheri_atest(unsigned *rec);
static unsigned rec[9 * 16 * 3];

static void phex(unsigned v)
{
    const char *d = "0123456789abcdef";
    for (int k = 7; k >= 0; --k) send_char(d[(v >> (4 * k)) & 15]);
}

int mymain(int argc, int argv)
{
    static const char *nm[9] = {"clw+13", "clw+14", "clw+15", "clh+15", "clhu+15",
                                "csw+13", "csw+14", "csw+15", "csh+15"};
    static const unsigned off[9] = {13, 14, 15, 15, 15, 13, 14, 15, 15};
    unsigned nfail = 0;
    (void)argc; (void)argv;
    cheri_atest(rec);
    for (int o = 0; o < 9; ++o) {
        unsigned is_ld = o < 5, n_hi = 0, n_orig = 0, n_bad = 0, bad = 0, bad_c = 0;
        for (int r = 0; r < 16; ++r) {
            unsigned *p = &rec[(o * 16 + r) * 3];
            unsigned a = 0x8007fff0u + off[o];
            int ok = (p[0] == (is_ld ? 5u : 7u)) && (!is_ld || p[2] == 0x5eadbeefu);
            if (ok && p[1] == 0x80080000u) n_hi++;
            else if (ok && p[1] == a) n_orig++;
            else { n_bad++; if (n_bad == 1) { bad = p[1]; bad_c = p[0]; } }
        }
        prints(n_bad ? "FAIL " : "PASS ");
        prints((char *)nm[o]);
        prints(" mtval=0x80080000:"); phex(n_hi);
        prints(" mtval=orig:"); phex(n_orig);
        prints(" bad:"); phex(n_bad);
        if (n_bad) { prints(" first_bad mcause="); phex(bad_c); prints(" mtval="); phex(bad); }
        prints("\n");
        nfail += n_bad != 0;
    }
    prints(nfail ? "SPLIT MTVAL C FAIL\n" : "SPLIT MTVAL C PASS\n");
    stop_sim();
    return 0;
}
