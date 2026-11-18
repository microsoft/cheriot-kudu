// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

typedef int (*case_fn)(volatile int *mb);

extern void install_handler(void);
extern int halt_only(volatile int *mb);
extern int step_nop(volatile int *mb);
extern int step_haltreq(volatile int *mb);

#define NCASES 3
// Mailbox: 0 case, 1 ROM entries, 2/3 dpc per entry, 6/7 dcsr per entry,
// 16 step target.
static volatile int mb[20];
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

static void run(int c, case_fn fn)
{
    for (int i = 0; i < 20; ++i)
        mb[i] = 0;
    mb[0] = c;
    fn(mb);
}

static void step_case(case_fn fn, char *name, unsigned exp_cause)
{
    run(2, fn);
    prints(name);
    kv("entries", mb[1]);
    kv("cause1", DCSR_CAUSE(mb[6]));
    kv("dpc2", mb[3]);
    kv("exp_dpc2", mb[16] + 4);
    kv("cause2", DCSR_CAUSE(mb[7]));
    kv("exp_cause2", exp_cause);
    verdict(mb[1] != 2 || DCSR_CAUSE(mb[6]) != 3 || (unsigned)mb[3] != (unsigned)mb[16] + 4 ||
            DCSR_CAUSE(mb[7]) != exp_cause);
}

int mymain(int argc, int argv)
{
    (void)argc;
    (void)argv;

    fails = 0;               // .bss is not zeroed by the startup code
    install_handler();

    // H3 (control): plain halt request.
    run(1, halt_only);
    prints("HALT STEP CAUSE H3 control-haltreq");
    kv("entries", mb[1]);
    kv("cause1", DCSR_CAUSE(mb[6]));
    verdict(mb[1] != 1 || DCSR_CAUSE(mb[6]) != 3);

    // H2 (control): stepping a nop reports STEP.
    step_case(step_nop, "HALT STEP CAUSE H2 control-step", 4);

    // H1: halt request pending when the step completes reports HALTREQ.
    step_case(step_haltreq, "HALT STEP CAUSE H1 step-plus-haltreq", 3);

    prints(fails ? "HALT STEP CAUSE FAIL failures=" : "HALT STEP CAUSE PASS failures=");
    send_char('0' + fails);
    prints(" cases=");
    send_char('0' + NCASES);
    prints("\n");
    stop_sim();
    return fails != 0;
}
