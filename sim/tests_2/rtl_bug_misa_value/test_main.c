// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

// misa for every KuduCfg (RV32A = RV32B = RV32M = 1, U-mode present):
//   RV32 build or PMODE=0: MXL=1 | U | M | I | C | B | A     = 0x40101107
//   CHERIoT PMODE=1      : MXL=1 | X | U | M | E | C | B | A = 0x40901017
#ifdef __CHERI_PURE_CAPABILITY__
#define MISA_EXPECTED 0x40901017u
#define MODE_STR "PMODE=1"
#else
#define MISA_EXPECTED 0x40101107u
#define MODE_STR "PMODE=0/RV32"
#endif

extern unsigned read_misa(void);

static void print_hex(unsigned value)
{
    static const char digits[] = "0123456789abcdef";
    prints("0x");
    for (int i = 7; i >= 0; --i)
        send_char(digits[(value >> (4 * i)) & 15]);
}

int mymain(int argc, int argv)
{
    (void)argc;
    (void)argv;
    unsigned misa = read_misa();
    unsigned fail = misa != MISA_EXPECTED;

    prints("MISA VALUE " MODE_STR " actual=");
    print_hex(misa);
    prints(" expected=");
    print_hex(MISA_EXPECTED);
    prints(fail ? " FAIL\n" : " PASS\n");
    return fail;
}
