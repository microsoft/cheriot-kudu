// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

struct observation {
    unsigned traps;
    unsigned mcause;
    unsigned rd_after;
    unsigned marker;
};

extern void rv32_atest(struct observation *obs);

static struct observation obs;

static void print_hex(unsigned value)
{
    char text[11] = "0x00000000";
    char *digits = "0123456789abcdef";
    for (unsigned i = 0; i < 8; ++i)
        text[9 - i] = digits[(value >> (4 * i)) & 15];
    prints(text);
}

int mymain(int argc, int argv)
{
    (void)argc;
    (void)argv;
    rv32_atest(&obs);

    unsigned pass = obs.traps == 1 && obs.mcause == 2 &&
                    obs.rd_after == 0xa5a5a5a5 && obs.marker == 0x13579bdf;
    prints("RTYPE REV8 RESERVED traps=");
    print_hex(obs.traps);
    prints(" mcause=");
    print_hex(obs.mcause);
    prints(" rd_after=");
    print_hex(obs.rd_after);
    prints(" marker=");
    print_hex(obs.marker);
    prints(pass ? " PASS\n" : " FAIL\n");
    stop_sim();
    return pass ? 0 : 1;
}
