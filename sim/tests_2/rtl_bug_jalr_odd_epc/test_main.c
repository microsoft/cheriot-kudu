// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

extern unsigned jo_loop(void);
extern unsigned jo_csrw(unsigned v);
extern volatile unsigned jo_irqs, jo_odd, jo_first_odd;
extern char jo_tgt[];

#define NCASES 3
#define MIN_IRQS 50
static int fails;

static void hx(unsigned v)
{
    char t[11] = "0x00000000";
    for (unsigned i = 0; i < 8; ++i)
        t[9 - i] = "0123456789abcdef"[(v >> (4 * i)) & 15];
    prints(t);
}

static void dec(unsigned v)
{
    char t[11];
    int i = 10;
    t[i] = 0;
    do {
        t[--i] = '0' + v % 10;
        v /= 10;
    } while (v);
    prints(&t[i]);
}

static void kv(char *name, unsigned value)
{
    prints(" ");
    prints(name);
    prints("=");
    hx(value);
}

static void verdict(int fail)
{
    prints(fail ? " FAIL\n" : " PASS\n");
    fails += fail;
}

int mymain(int argc, int argv)
{
    (void)argc;
    (void)argv;
    fails = 0;               // .bss is not zeroed by the startup code

    unsigned iters = jo_loop();

    // J1: no interrupt may report an odd mepc.
    prints("JALR ODD EPC J1 irq-mepc-bit0");
    kv("irqs", jo_irqs);
    kv("odd", jo_odd);
    kv("first_odd", jo_first_odd);
    kv("jalr_tgt", (unsigned)jo_tgt);
    verdict(jo_odd != 0);

    // J2 (control): the loop ran to completion and enough interrupts landed
    // in it for J1 to be meaningful (needs +INTR_RATE=4).
    prints("JALR ODD EPC J2 control-irq-count");
    kv("iters", iters);
    kv("irqs", jo_irqs);
    kv("min", MIN_IRQS);
    verdict(iters != 4000 || jo_irqs < MIN_IRQS);

    // J3 (control): csrw mepc legalizes bit 0.
    unsigned r = jo_csrw(0x80001235);
    prints("JALR ODD EPC J3 control-csrw-mepc");
    kv("read", r);
    kv("exp", 0x80001234);
    verdict(r != 0x80001234);

    prints(fails ? "JALR ODD EPC FAIL failures=" : "JALR ODD EPC PASS failures=");
    dec(fails);
    prints(" cases=");
    dec(NCASES);
    prints("\n");
    stop_sim();
    return fails != 0;
}
