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
int mymain(int argc, int argv)
{
    (void)argc; (void)argv;
    unsigned n = cheri_atest();
    unsigned *rec = rec_base();
    for (unsigned i = 0; i < n; ++i) {
        prints("R ");
        for (int j = 0; j < 16; ++j) { phex(rec[i * 16 + j]); send_char(' '); }
        send_char('\n');
    }
    prints("DONE\n");
    stop_sim();
    return 0;
}
