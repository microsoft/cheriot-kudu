// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>
extern unsigned cheri_atest(void);
extern unsigned *rec_base(void);
static void phex(unsigned v)
{
    const char *d = "0123456789abcdef";
    for (int k = 7; k >= 0; --k) send_char(d[(v >> (4 * k)) & 15]);
}
// Record words: 0 mcause, 1 mtval, 2-8 rd (x8: addr high tag perm type base top),
// 9-10 memory words, 11 memory cap high, 12 memory tag, 13 mshwm, 14 x13, 15 case index.
// Every case is an AMO through a cap with LD but no SD (rs1 = c5), so it must take a
// CHERI SD violation (mcause 0x1c, mtval (5 << 5) | 0x13) and leave rd/memory unchanged.
static const unsigned expect[15] = {0x1c, 0xb3, 0x5a5a5a5a, 0, 0, 0, 0, 0x5a5a5a00,
                                    0x5a5a5a00, 0, 0, 0, 0, 0, 0};
static const char *desc[4] = {"amoadd noSD in-bounds aligned", "amoadd noSD at top",
                              "amoswap noSD misaligned", "amoadd noSD zero-length cap"};
int mymain(int argc, int argv)
{
    unsigned fails = 0;
    (void)argc; (void)argv;
    unsigned n = cheri_atest();
    unsigned *rec = rec_base();
    for (unsigned i = 0; i < n; ++i) {
        prints("R ");
        for (int j = 0; j < 16; ++j) { phex(rec[i * 16 + j]); send_char(' '); }
        send_char('\n');
    }
    for (unsigned i = 0; i < 4; ++i) {
        unsigned *r = &rec[i * 16];
        int bad_cause = i >= n || r[0] != expect[0] || r[1] != expect[1];
        int bad_state = 0;
        for (int j = 2; j < 15 && i < n; ++j) bad_state |= r[j] != expect[j];
        fails += bad_cause || bad_state;
        if (bad_cause) prints("FAIL amo-sd case ");
        else if (bad_state) prints("FAIL amo-state case ");
        else prints("PASS case ");
        phex(i); send_char(' '); prints((char *)desc[i]);
        prints(" mcause="); phex(r[0]); prints(" mtval="); phex(r[1]);
        prints(" (expected 0000001c/000000b3)\n");
    }
    if (fails) { prints("AMO SD PERM FAIL failures="); phex(fails); send_char('\n'); }
    else prints("AMO SD PERM PASS cases=4\n");
    stop_sim();
    return 0;
}
