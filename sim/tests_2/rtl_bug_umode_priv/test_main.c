// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

extern void rv32_atest(void);
extern volatile unsigned up_irqs[4], up_nexc[4], up_exc_cause[4], up_exc_epc[4];
extern volatile unsigned up_irq_epc[4], up_irq_ok[4];
extern volatile unsigned up_ucnt, up_ccnt, up_dwoke;
extern char uA_mret[], uB_wfi[], uC_start[], uC_end[];

#define NCASES 4
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

    rv32_atest();

    // The interrupt generator is needed by phases 1-3 (+INTR_RATE).
    if (!up_irq_ok[1] || !up_irq_ok[2] || !up_irq_ok[3]) {
        prints("UPRIV SETUP meip-pending (run with +INTR_RATE=3)");
        verdict(1);
    }

    // A: MRET in U-mode raises illegal instruction at the MRET; the U-mode
    // code runs once.
    prints("UPRIV A umode-mret");
    kv("ucnt", up_ucnt);
    kv("nexc", up_nexc[0]);
    kv("mcause", up_exc_cause[0]);
    kv("mepc", up_exc_epc[0]);
    kv("exp_mepc", (unsigned)uA_mret);
    verdict(up_ucnt != 1 || up_nexc[0] != 1 || up_exc_cause[0] != 2 ||
            up_exc_epc[0] != (unsigned)uA_mret);

    // B: WFI in U-mode with mstatus.TW = 1 raises illegal instruction.
    prints("UPRIV B umode-wfi-tw");
    kv("nexc", up_nexc[1]);
    kv("mcause", up_exc_cause[1]);
    kv("mepc", up_exc_epc[1]);
    kv("exp_mepc", (unsigned)uB_wfi);
    verdict(up_nexc[1] != 1 || up_exc_cause[1] != 2 || up_exc_epc[1] != (unsigned)uB_wfi);

    // C: a pending, enabled M-mode interrupt is taken in U-mode even though
    // mstatus.MIE = 0.
    prints("UPRIV C umode-irq-mie0");
    kv("irqs", up_irqs[2]);
    kv("mepc", up_irq_epc[2]);
    kv("ccnt", up_ccnt);
    verdict(up_irqs[2] == 0 || up_irq_epc[2] < (unsigned)uC_start ||
            up_irq_epc[2] >= (unsigned)uC_end || up_nexc[2] != 0 || up_ccnt != 3000);

    // D (control): WFI in M-mode with TW = 1 completes without a trap, and
    // no interrupt is taken in M-mode with MIE = 0.
    prints("UPRIV D control-mmode-wfi-tw");
    kv("woke", up_dwoke);
    kv("nexc", up_nexc[3]);
    kv("irqs", up_irqs[3]);
    verdict(up_dwoke != 1 || up_nexc[3] != 0 || up_irqs[3] != 0);

    prints(fails ? "UPRIV FAIL failures=" : "UPRIV PASS failures=");
    dec(fails);
    prints(" cases=");
    dec(NCASES);
    prints("\n");
    stop_sim();
    return fails != 0;
}
