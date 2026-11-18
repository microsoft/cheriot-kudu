// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

struct observation {
    unsigned traps;
    unsigned first_mcause;
    unsigned packh_result;
    unsigned xperm8_result;
    unsigned brev8_result;
    unsigned zip_result;
    unsigned unzip_result;
    unsigned marker;
};

extern void cheri_atest(struct observation *obs);
static struct observation obs;

static void print_hex(unsigned value)
{
    static const char hex[] = "0123456789abcdef";
    prints("0x");
    for (int i = 7; i >= 0; --i)
        send_char(hex[(value >> (i * 4)) & 0xf]);
}

static unsigned check_equal(const char *name, unsigned actual, unsigned expected)
{
    unsigned fail = actual != expected;
    prints(fail ? "FAIL " : "PASS ");
    prints((char *)name);
    prints(" actual=");
    print_hex(actual);
    prints(" expected=");
    print_hex(expected);
    prints("\n");
    return fail;
}

int mymain(int argc, int argv)
{
    (void)argc;
    (void)argv;

    cheri_atest(&obs);

    unsigned failures = 0;
    failures += check_equal("traps", obs.traps, 0);
    failures += check_equal("first_mcause", obs.first_mcause, 0);
    failures += check_equal("packh", obs.packh_result, 0x00008844u);
    failures += check_equal("xperm8", obs.xperm8_result, 0x11223344u);
    failures += check_equal("brev8", obs.brev8_result, 0x80c4a2e6u);
    failures += check_equal("zip", obs.zip_result, 0x10131c1fu);
    failures += check_equal("unzip", obs.unzip_result, 0x01234567u);
    failures += check_equal("marker", obs.marker, 0x13579bdfu);

    prints(failures ? "SAIL ZBKB ZBKX FAIL failures=" : "SAIL ZBKB ZBKX PASS failures=");
    print_hex(failures);
    prints(" cases=0x00000008 traps=");
    print_hex(obs.traps);
    prints(" first_mcause=");
    print_hex(obs.first_mcause);
    prints("\n");
    stop_sim();
    return failures != 0;
}
