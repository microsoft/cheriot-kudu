// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

extern void install_mtcc(void);
extern void dbg_case(int c, volatile int *mb);

#define NCASES 2
static volatile int mb[16];
static int fails;

static void print_hex(unsigned value)
{
    static const char digits[] = "0123456789abcdef";
    prints("0x");
    for (int i = 7; i >= 0; --i)
        send_char(digits[(value >> (4 * i)) & 15]);
}

static void kv(char *name, unsigned value)
{
    prints(" ");
    prints(name);
    prints("=");
    print_hex(value);
}

static void verdict(int fail)
{
    prints(fail ? " FAIL\n" : " PASS\n");
    fails += fail;
}

// An exception raised by the debug ROM must enter DmExcAddr exactly once,
// must not run the mtvec handler and must leave mcause/MEPCC unchanged.
static void exc_case(int c, char *name)
{
    for (int i = 0; i < 16; ++i)
        mb[i] = 0;
    dbg_case(c, mb);
    prints(name);
    kv("entries", mb[1]);
    kv("dmexc_hits", mb[12]);
    kv("mtvec_hits", mb[3]);
    kv("handler_mcause", mb[13]);
    kv("mcause0", mb[4]);
    kv("mcause1", mb[6]);
    kv("mepcc0", mb[5]);
    kv("mepcc1", mb[7]);
    kv("fallthru", mb[15]);
    verdict(mb[1] != 1 || mb[12] != 1 || mb[3] != 0 || mb[15] != 0 ||
            mb[6] != mb[4] || mb[7] != mb[5]);
}

int mymain(int argc, int argv)
{
    (void)argc;
    (void)argv;

    fails = 0;               // .bss is not zeroed by the startup code
    install_mtcc();

    exc_case(1, "DEBUG ECALL E1 ecall-in-debug");
    exc_case(2, "DEBUG ECALL E2 control-illegal-in-debug");

    prints(fails ? "DEBUG ECALL FAIL failures=" : "DEBUG ECALL PASS failures=");
    send_char('0' + fails);
    prints(" cases=");
    send_char('0' + NCASES);
    prints("\n");
    stop_sim();
    return fails != 0;
}
