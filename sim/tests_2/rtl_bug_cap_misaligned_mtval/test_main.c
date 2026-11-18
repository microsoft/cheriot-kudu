// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

extern void cheri_atest(unsigned *results, unsigned *area);
static unsigned results[8];
static unsigned area[8] __attribute__((aligned(8)));

static void hex(unsigned value)
{
    const char *digits = "0123456789abcdef";
    prints("0x");
    for (int i = 7; i >= 0; --i)
        send_char(digits[(value >> (4 * i)) & 15]);
}

int mymain(int argc, int argv)
{
    unsigned failures = 0;
    (void)argc;
    (void)argv;
    cheri_atest(results, area);
    for (unsigned i = 0; i < 2; ++i) {
        unsigned *r = results + 4 * i;
        unsigned failed = r[0] != (i ? 4u : 6u) || r[1] != r[3] || r[2] != 1;
        failures += failed;
        prints(failed ? "FAIL " : "PASS ");
        prints(i ? "misaligned-clc" : "misaligned-csc");
        prints(" mcause="); hex(r[0]);
        prints(" mtval="); hex(r[1]);
        prints(" traps="); hex(r[2]);
        prints(" expected_mtval="); hex(r[3]);
        prints("\n");
    }
    prints(failures ? "CAP ALIGN MTVAL FAIL failures=" : "CAP ALIGN MTVAL PASS failures=");
    hex(failures);
    prints(" cases=0x00000002\n");
    stop_sim();
    return failures != 0;
}
