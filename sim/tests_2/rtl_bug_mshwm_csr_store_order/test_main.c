// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

#define NCASES 6

extern void cheri_atest(unsigned *results, unsigned *area);
static unsigned results[16];
static unsigned area[64] __attribute__((aligned(16)));

static void hex(unsigned value)
{
    const char *digits = "0123456789abcdef";
    prints("0x");
    for (int i = 7; i >= 0; --i)
        send_char(digits[(value >> (4 * i)) & 15]);
}

static void dec(unsigned value)
{
    char buf[11];
    int n = 0;
    do {
        buf[n++] = '0' + value % 10;
        value /= 10;
    } while (value);
    while (n)
        send_char(buf[--n]);
}

int mymain(int argc, int argv)
{
    static const char *names[NCASES] = {
        "store-csrw-raise-mshwm-csw", "store-csrw-raise-mshwmb-csw",
        "store-csrw-pair-raise-mshwm-csw", "store-csrw-raise-mshwm-csc",
        "control-no-older-store", "control-gap-before-store"};
    static const unsigned offsets[NCASES] = {96, 256, 96, 96, 96, 96};
    unsigned failures = 0;
    unsigned base = (unsigned)area;
    (void)argc;
    (void)argv;
    for (int i = 0; i < 16; ++i)
        results[i] = 0;
    cheri_atest(results, area);
    for (int i = 0; i < NCASES; ++i) {
        unsigned expected = base + offsets[i];
        unsigned failed = results[i] != expected;
        failures += failed;
        prints(failed ? "FAIL " : "PASS ");
        prints((char *)names[i]);
        prints(" mshwm="); hex(results[i]);
        prints(" expected="); hex(expected);
        prints("\n");
    }
    prints(failures ? "MSHWM ORDER FAIL failures=" : "MSHWM ORDER PASS failures=");
    dec(failures);
    prints(" cases=");
    dec(NCASES);
    prints("\n");
    stop_sim();
    return failures != 0;
}
