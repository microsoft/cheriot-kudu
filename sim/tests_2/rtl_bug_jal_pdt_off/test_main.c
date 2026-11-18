// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

struct observation {
    unsigned old_cpuctrl;
    unsigned new_cpuctrl;
    unsigned jal_marker;
    unsigned jalr_marker;
};

extern unsigned rv32_atest(struct observation *obs);

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

    unsigned fail = rv32_atest(&obs);
    prints("JAL PDT OFF old=");
    print_hex(obs.old_cpuctrl);
    prints(" new=");
    print_hex(obs.new_cpuctrl);
    prints(" jal=");
    print_hex(obs.jal_marker);
    prints(" jalr=");
    print_hex(obs.jalr_marker);
    prints(fail ? " FAIL\n" : " PASS\n");
    stop_sim();
    return fail ? 1 : 0;
}
