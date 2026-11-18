// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

#ifdef CHERIOT
extern void *from_root(unsigned int);
#define MMIO ((volatile unsigned *)from_root(0x83800000U))
#define ADDR(p) ((unsigned)__builtin_cheri_address_get(p))
#else
#define MMIO ((volatile unsigned *)0x83800000U)
#define ADDR(p) ((unsigned)(p))
#endif

extern void ro_run(unsigned *r, unsigned n);

#define NITER 4000
#define NCASES 3
#define MIN_EVENTS 50

static volatile unsigned mb[4] __attribute__((aligned(16)));
static int fails;

static void hx(unsigned v)
{
    prints("0x");
    for (int i = 7; i >= 0; --i)
        send_char("0123456789abcdef"[(v >> (4 * i)) & 15]);
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
    unsigned r[5];
    (void)argc;
    (void)argv;
    fails = 0;               // .bss is not zeroed by the startup code
    for (int i = 0; i < 4; ++i)
        mb[i] = 0;
    MMIO[1] = ADDR(mb);      // debug ROM mailbox (TB scratch_reg1)

    ro_run(r, NITER);
    unsigned dbg = mb[0], dbg_odd = mb[1], dbg_first = mb[2];

    // R1: no interrupt may report an odd mepc.
    prints("RA ODD EPC R1 irq-mepc-bit0");
    kv("irqs", r[1]);
    kv("odd", r[2]);
    kv("first_odd", r[3]);
    verdict(r[2] != 0);

    // R2: no debug entry may report an odd dpc.
    prints("RA ODD EPC R2 dbg-dpc-bit0");
    kv("entries", dbg);
    kv("odd", dbg_odd);
    kv("first_odd", dbg_first);
    verdict(dbg_odd != 0);

    // R3 (control): the loop ran to completion with no exception, and enough
    // interrupts or debug entries landed in it for R1/R2 to be meaningful.
    prints("RA ODD EPC R3 control");
    kv("iters", r[0]);
    kv("exc", r[4]);
    kv("events", r[1] + dbg);
    kv("min", MIN_EVENTS);
    verdict(r[0] != NITER || r[4] != 0 || r[1] + dbg < MIN_EVENTS);

    prints(fails ? "RA ODD EPC FAIL failures=" : "RA ODD EPC PASS failures=");
    dec(fails);
    prints(" cases=");
    dec(NCASES);
    prints("\n");
    stop_sim();
    return fails != 0;
}
