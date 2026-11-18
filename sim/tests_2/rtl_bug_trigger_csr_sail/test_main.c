// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

extern void rv32_atest(unsigned *obs);
static unsigned obs[2];

static void print_hex(unsigned value)
{
    char text[11] = "0x00000000";
    char *digits = "0123456789abcdef";
    for (unsigned i = 0; i < 8; ++i)
        text[9 - i] = digits[(value >> (4 * i)) & 15];
    prints(text);
}

static unsigned check_equal(const char *name, unsigned actual, unsigned expected)
{
    unsigned fail = actual != expected;
    prints(fail ? "FAIL " : "PASS ");
    prints(name);
    prints(" actual=");
    print_hex(actual);
    prints(" expected=");
    print_hex(expected);
    prints("\n");
    return fail;
}

int mymain(int argc, int argv)
{
    unsigned failures = 0;
    (void)argc;
    (void)argv;

    prints("Sail trigger/debug CSR check: trigger module disabled in Sail\n");
    rv32_atest(obs);

    failures += check_equal("tselect_reset_read", obs[0], 0xffffffffu);
    failures += check_equal("tselect_after_write_read", obs[1], 0xfffffffeu);

    prints(failures ? "SAIL TRIGGER CSR FAIL failures=" : "SAIL TRIGGER CSR PASS failures=");
    print_hex(failures);
    prints(" cases=0x00000002\n");
    stop_sim();
    return failures != 0;
}
