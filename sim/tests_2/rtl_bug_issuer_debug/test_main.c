// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

typedef int (*case_fn)(volatile int *mb);

extern unsigned install_handler(void);
extern int step_illegal(volatile int *mb);
extern int step_irq(volatile int *mb);
extern int step_ebreak(volatile int *mb);
extern int step_wfi(volatile int *mb);
extern int mepc_halt(volatile int *mb);

#define DECL(n) extern int dpc_j##n(volatile int *); extern int dpc_b##n(volatile int *);
DECL(0) DECL(1) DECL(2) DECL(3) DECL(4) DECL(5)
DECL(6) DECL(7) DECL(8) DECL(9) DECL(10) DECL(11)

#define NDPC 12
static case_fn jfn[NDPC] = {dpc_j0, dpc_j1, dpc_j2, dpc_j3, dpc_j4, dpc_j5,
                            dpc_j6, dpc_j7, dpc_j8, dpc_j9, dpc_j10, dpc_j11};
static case_fn bfn[NDPC] = {dpc_b0, dpc_b1, dpc_b2, dpc_b3, dpc_b4, dpc_b5,
                            dpc_b6, dpc_b7, dpc_b8, dpc_b9, dpc_b10, dpc_b11};

// Mailbox: 0 case, 1 ROM entries, 2..5 dpc per entry, 6..9 dcsr per entry,
// 10/11 x15/x14 at entry 1, 12 traps, 13 mcause, 14 mepc, 15 I1 base,
// 16 step target / expected MEPC, 18 interrupts taken.
static volatile int mb[20];
static unsigned handler;
static int fails;

#define DCSR_CAUSE(x) (((unsigned)(x) >> 6) & 7)

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

static int run(int c, case_fn fn)
{
    for (int i = 0; i < 20; ++i)
        mb[i] = 0;
    mb[0] = c;
    return fn(mb);
}

// I1: dpc must name the next unexecuted instruction on the architectural
// path, as given by the progress counter (x15) and link register (x14)
// captured on debug entry. Offsets are relative to the block base.
static void dpc_case(int kind, int n)
{
    int ret = run(1, kind ? bfn[n] : jfn[n]);
    unsigned base = mb[15], dpc = mb[2] - base, s = mb[10], l = mb[11];
    unsigned e0 = ~0u, e1 = ~0u, n4 = 4 * n;
    int ok;

    if (s < (unsigned)n)
        e0 = e1 = 4 * s;
    else if (s == (unsigned)n)
        e0 = e1 = n4;
    else if (s == (unsigned)n + 0x40) {
        if (kind)               // branch: no way to tell whether it retired
            e0 = n4 + 4, e1 = n4 + 16;
        else
            e0 = e1 = (l == 1) ? n4 + 4 : n4 + 16;
    } else if (s == (unsigned)n + 0x50)
        e0 = e1 = n4 + 20;
    else if (s == (unsigned)n + 0x70)
        e0 = e1 = n4 + 24;

    if (s == (unsigned)n + 0xf0)   // halted in the delay loop
        ok = dpc >= n4 + 28 && dpc <= n4 + 40;
    else
        ok = dpc == e0 || dpc == e1;
    ok = ok && mb[1] == 1 && ret == n + 0xf0;

    prints(kind ? "ISSUER DBG I1 branch n=" : "ISSUER DBG I1 cjalr  n=");
    send_char('0' + n / 10);
    send_char('0' + n % 10);
    kv("x15", s);
    kv("dpc_off", dpc);
    kv("exp_off", e0);
    kv("ret", ret);
    verdict(!ok);
}

int mymain(int argc, int argv)
{
    (void)argc;
    (void)argv;

    fails = 0;               // .bss is not zeroed by the startup code
    handler = install_handler();

    for (int n = 0; n < NDPC; ++n) {
        dpc_case(0, n);
        dpc_case(1, n);
    }

    // I6: a halt request must not modify MEPCC.
    unsigned r6 = run(1, mepc_halt);
    prints("ISSUER DBG I6 halt-mepc");
    kv("entries", mb[1]);
    kv("mepc", r6);
    kv("exp", mb[16]);
    kv("dpc", mb[2]);
    verdict(mb[1] != 1 || r6 != (unsigned)mb[16]);

    // I2: stepping an instruction that traps at decode must halt at the
    // handler entry, before the handler executes.
    run(2, step_illegal);
    prints("ISSUER DBG I2 step-illegal");
    kv("entries", mb[1]);
    kv("traps", mb[12]);
    kv("mcause", mb[13]);
    kv("dpc2", mb[3]);
    kv("handler", handler);
    kv("cause2", DCSR_CAUSE(mb[7]));
    verdict(mb[1] != 2 || mb[12] != 1 || mb[13] != 2 ||
            (unsigned)mb[3] != handler || DCSR_CAUSE(mb[7]) != 4);

    // I4: ebreak stepped with ebreakm = 1 must report cause EBREAK.
    run(4, step_ebreak);
    prints("ISSUER DBG I4 step-ebreak");
    kv("entries", mb[1]);
    kv("dpc2", mb[3]);
    kv("target", mb[16]);
    kv("cause2", DCSR_CAUSE(mb[7]));
    verdict(mb[1] != 2 || mb[3] != mb[16] || DCSR_CAUSE(mb[7]) != 1);

    // I3: interrupts are disabled while stepping (dcsr.stepie = 0).
    int r3 = run(3, step_irq);
    prints("ISSUER DBG I3 step-irq");
    kv("entries", mb[1]);
    kv("irqs", mb[18]);
    kv("dpc2", mb[3]);
    kv("exp", mb[16] + 4);
    kv("ret", r3);
    verdict(mb[1] != 2 || mb[18] != 0 || mb[3] != mb[16] + 4 || r3 != 3);

    // I5: wfi stepped with no interrupt enabled must not hang.
    prints("ISSUER DBG I5 step-wfi start\n");
    run(5, step_wfi);
    prints("ISSUER DBG I5 step-wfi");
    kv("entries", mb[1]);
    kv("dpc2", mb[3]);
    kv("exp", mb[16] + 4);
    verdict(mb[1] != 2 || mb[3] != mb[16] + 4);

    prints(fails ? "ISSUER DBG SUMMARY FAIL\n" : "ISSUER DBG SUMMARY PASS\n");
    stop_sim();
    return fails != 0;
}
