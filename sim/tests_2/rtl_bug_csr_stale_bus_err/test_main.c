// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

extern void sb_run(unsigned *r);

#define NCASES 5
#define BAD_ADDR 0x7ffffffdu

static unsigned r[NCASES * 5];
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

int mymain(int argc, int argv)
{
    static char *name[NCASES] = {"control-csr-only", "lw-then-csrr", "sw-then-csrr",
                                 "lw-then-csrw-ro", "control-lw-lw-csrr"};
    // expected first trap (mcause, mtval); C0 has no first trap
    static const unsigned c1[NCASES] = {0, 5, 7, 5, 5};
    static const unsigned v1[NCASES] = {0, BAD_ADDR, BAD_ADDR, BAD_ADDR, BAD_ADDR};
    (void)argc;
    (void)argv;
    fails = 0;               // .bss is not zeroed by the startup code

    sb_run(r);
    for (int k = 0; k < NCASES; ++k) {
        unsigned *p = &r[k * 5];
        // the failing CSR access must be an illegal instruction, mtval = insn
        int fail = p[0] != c1[k] || p[1] != v1[k] || p[2] != 2 || p[3] != p[4];
        prints("CSR BUSERR C");
        dec(k);
        prints(" ");
        prints(name[k]);
        kv("mcause1", p[0]);
        kv("mtval1", p[1]);
        kv("mcause2", p[2]);
        kv("mtval2", p[3]);
        kv("insn", p[4]);
        prints(fail ? " FAIL\n" : " PASS\n");
        fails += fail;
    }
    prints(fails ? "CSR BUSERR FAIL failures=" : "CSR BUSERR PASS failures=");
    dec(fails);
    prints(" cases=");
    dec(NCASES);
    prints("\n");
    stop_sim();
    return fails != 0;
}
