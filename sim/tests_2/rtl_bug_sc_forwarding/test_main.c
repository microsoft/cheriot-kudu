// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

extern void rv32_atest(unsigned *results);
static unsigned results[8];

static void hex(unsigned value)
{
    char text[] = "0x00000000";
    const char *digits = "0123456789abcdef";
    for (unsigned i = 0; i < 8; ++i)
        text[9 - i] = digits[(value >> (4 * i)) & 15];
    prints(text);
}

int mymain(int argc, int argv)
{
    unsigned failures = 0;
    (void)argc;
    (void)argv;
    rv32_atest(results);
    for (unsigned i = 0; i < 2; ++i) {
        unsigned *r = results + 4 * i;
        unsigned failed = r[0] != 1 || r[1] != 0x11223344 ||
                          r[2] != 0x11223345 || r[3] != 0x11223344;
        failures += failed;
        prints(failed ? "FAIL " : "PASS ");
        prints(i ? "failed-sc spaced-load" : "failed-sc immediate-load");
        prints(" sc="); hex(r[0]);
        prints(" load="); hex(r[1]);
        prints(" dependent="); hex(r[2]);
        prints(" memory="); hex(r[3]);
        prints("\n");
    }
    prints(failures ? "SC FORWARDING FAIL failures=" : "SC FORWARDING PASS failures=");
    hex(failures);
    prints(" cases=0x00000002\n");
    stop_sim();
    return failures != 0;
}
