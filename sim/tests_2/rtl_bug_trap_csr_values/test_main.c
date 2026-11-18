// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

struct observation {
    unsigned dret_mcause;
    unsigned dret_mtval;
    unsigned dret_mepc;
    unsigned ecall_mcause;
    unsigned ecall_mtval;
    unsigned ecall_mepc;
};

extern void rv32_atest(struct observation *obs);
extern char dret_site[];
extern char ecall_site[];

static struct observation obs;

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

    prints("Trap CSR values: DRET outside debug and ECALL in M-mode, PMODE=0\n");
    rv32_atest(&obs);

    failures += check_equal("dret_mcause", obs.dret_mcause, 2);
    failures += check_equal("dret_mtval", obs.dret_mtval, 0x7b200073);
    failures += check_equal("dret_mepc", obs.dret_mepc, (unsigned)dret_site);
    failures += check_equal("ecall_mcause", obs.ecall_mcause, 11);
    failures += check_equal("ecall_mtval", obs.ecall_mtval, 0);
    failures += check_equal("ecall_mepc", obs.ecall_mepc, (unsigned)ecall_site);

    prints(failures ? "TRAP CSR VALUES FAIL failures=" : "TRAP CSR VALUES PASS failures=");
    print_hex(failures);
    prints(" cases=0x00000006\n");
    stop_sim();
    return failures != 0;
}
