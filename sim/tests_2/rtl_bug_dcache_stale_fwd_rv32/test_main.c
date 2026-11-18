// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include <util.h>
extern void dcs_main(unsigned *d);
static unsigned d[512] __attribute__((aligned(16)));
static void hex(unsigned v)
{
    const char *x = "0123456789abcdef";
    prints("0x");
    for (int i = 7; i >= 0; --i) send_char(x[(v >> (4 * i)) & 15]);
}
int mymain(int argc, int argv)
{
    (void)argc; (void)argv;
    for (int i = 0; i < 64; i++) d[i] = 0;
    dcs_main(d);
    int ok = d[0] == 0 && d[1] == 48u;
    prints(ok ? "RW PASS" : "RW FAIL");
    prints(" bad="); hex(d[0]); prints(" cases="); hex(d[1]);
    prints(" fwd="); hex(d[2]); prints(" mem="); hex(d[3]); prints(" case="); hex(d[4]);
    prints("\nCASES:");
    for (int i = 0; i < 48; i++) send_char('0' + d[32 + i]);
    prints("\n");
    stop_sim();
    return !ok;
}
