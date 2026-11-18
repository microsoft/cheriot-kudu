// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

struct observation {
    unsigned written;
    unsigned old;
    unsigned after;
};

extern void rv32_atest(struct observation *results);

static struct observation results[27];
static const unsigned initial[9] = {
    0x80000100, 0x80000100, 0x80000300, 0x80000100, 0x80000100,
    0x80000100, 0x80000108, 0x80000100, 0x80000100
};
static const unsigned expected[9] = {
    0x80000300, 0x80000300, 0x80000100, 0x80000100, 0x80000100,
    0x80000108, 0x80000100, 0x80000100, 0x80000100
};
static char *csr_names[3] = {"mscratch", "mtvec", "mepc"};
static char *operations[9] = {
    "CSRRW", "CSRRS", "CSRRC", "CSRRS register-zero", "CSRRC register-zero",
    "CSRRSI", "CSRRCI", "CSRRSI zimm-zero", "CSRRCI zimm-zero"
};

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
    unsigned failures = 0;
    (void)argc;
    (void)argv;
    prints("CSR RMW: PMODE=0; aligned addresses; interrupts disabled during matrix\n");
    rv32_atest(results);
    for (unsigned csr = 0; csr < 3; ++csr) {
        for (unsigned op = 0; op < 9; ++op) {
            struct observation *r = &results[csr * 9 + op];
            unsigned failed = r->written != initial[op] ||
                              r->old != initial[op] || r->after != expected[op];
            failures += failed;
            prints(failed ? "FAIL " : "PASS ");
            prints(csr_names[csr]);
            prints(" ");
            prints(operations[op]);
            prints(" initial=");
            print_hex(r->written);
            prints(" old=");
            print_hex(r->old);
            prints(" actual=");
            print_hex(r->after);
            prints(" expected=");
            print_hex(expected[op]);
            prints("\n");
        }
    }
    prints(failures ? "CSR RMW FAIL failures=" : "CSR RMW PASS failures=");
    print_hex(failures);
    prints(" cases=0x0000001b\n");
    stop_sim();
    return failures != 0;
}
