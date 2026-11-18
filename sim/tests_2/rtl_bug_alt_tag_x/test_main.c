// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

extern unsigned alt_stress(unsigned seed, unsigned niter);
extern void stress_handler(void);
extern volatile unsigned irq_cnt, trap_cnt, last_mcause, last_mepc;
static const unsigned seeds[4] = {0x7fa91ed5u, 0x10133d03u, 0xac762cf6u, 0x41b1df3eu};
static const unsigned exp[4] = {0xf25d4e59u, 0x7ffc01d4u, 0xe0b75649u, 0xcf30b4d3u};

static void hex(unsigned v)
{
    char t[] = "0x00000000";
    const char *d = "0123456789abcdef";
    for (unsigned i = 0; i < 8; ++i) t[9 - i] = d[(v >> (4 * i)) & 15];
    prints(t);
}

int mymain(int argc, int argv)
{
    unsigned fails = 0;
    (void)argc; (void)argv;
    irq_cnt = 0; trap_cnt = 0;
    __asm__ volatile ("csrw mtvec, %0" :: "r"((unsigned)stress_handler));
    for (unsigned i = 0; i < 4; ++i) {
        unsigned got = alt_stress(seeds[i], 24u);
        prints("ALTSTRESS_RUN "); hex(i); prints(" got="); hex(got); prints(" exp="); hex(exp[i]);
        prints(got == exp[i] ? " ok\n" : " MISMATCH\n");
        fails += got != exp[i];
    }
    prints("ALTSTRESS irqs="); hex(irq_cnt); prints(" traps="); hex(trap_cnt);
    prints(" last_mcause="); hex(last_mcause); prints(" last_mepc="); hex(last_mepc); prints("\n");
    fails += trap_cnt != 0;
    prints(fails ? "ALTSTRESS FAIL fails=" : "ALTSTRESS PASS fails="); hex(fails); prints("\n");
    stop_sim();
    return fails != 0;
}
