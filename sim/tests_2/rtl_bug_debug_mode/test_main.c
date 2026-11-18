// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

extern void install_mtcc(void);
extern void dbg_case(int c, volatile int *mb, void **buf);
extern void clc_probe(void **buf, volatile int *out);
extern void pcc_probe(volatile int *out);

static volatile int mb[16];
static volatile int base[8];
static void *buf[2] __attribute__((aligned(8)));
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

static void run_case(int c)
{
    for (int i = 0; i < 16; ++i)
        mb[i] = 0;
    dbg_case(c, mb, buf);
}

#define DCSR_CAUSE(x) (((unsigned)(x) >> 6) & 7)

static void ebreak_case(int c, char *name)
{
    run_case(c);
    int fail = mb[1] != 2 || mb[3] != 0 || mb[15] != 0 || mb[6] != mb[4] ||
               DCSR_CAUSE(mb[7]) != DCSR_CAUSE(mb[5]);
    prints(name);
    kv("entries", mb[1]);
    kv("mtvec_hits", mb[3]);
    kv("dpc0", mb[4]);
    kv("dpc1", mb[6]);
    kv("cause0", DCSR_CAUSE(mb[5]));
    kv("cause1", DCSR_CAUSE(mb[7]));
    kv("fallthru", mb[15]);
    verdict(fail);
}

int mymain(int argc, int argv)
{
    (void)argc;
    (void)argv;

    fails = 0;               // .bss is not zeroed by the startup code
    install_mtcc();
    buf[0] = (void *)buf;
    buf[1] = 0;

    // D1: ebreak in debug mode must halt again without touching dpc/dcsr,
    // whatever dcsr.ebreakm says.
    ebreak_case(1, "DEBUG MODE D1a ebreak ebreakm=1");
    ebreak_case(2, "DEBUG MODE D1b ebreak ebreakm=0");

    // D2: an exception in debug mode must not enter the M-mode handler.
    run_case(3);
    prints("DEBUG MODE D2 illegal-insn");
    kv("mtvec_hits", mb[3]);
    kv("dmexc_hits", mb[12]);
    kv("fallthru", mb[15]);
    verdict(mb[3] != 0 || mb[12] != 1 || mb[15] != 0);

    // D3: an illegal CSR access in debug mode must raise an exception.
    run_case(4);
    prints("DEBUG MODE D3 illegal-csr");
    kv("mtvec_hits", mb[3]);
    kv("csrr_mtvec", mb[4]);
    kv("csrr_3ff", mb[5]);
    kv("fallthru", mb[15]);
    verdict(mb[15] == 0xbad4);

    // D4: CLC permission stripping must match normal mode.
    clc_probe(buf, base);
    run_case(5);
    prints("DEBUG MODE D4 clc-strip");
    kv("nomc_tag", mb[4]);
    kv("exp", base[0]);
    kv("nolm_perm", mb[5]);
    kv("exp", base[1]);
    kv("nolm_tag", mb[6]);
    kv("exp", base[2]);
    verdict(mb[4] != base[0] || mb[5] != base[1] || mb[6] != base[2]);

    // D5: PCC in debug mode (informational; cheriot-ibex also uses MTCC).
    pcc_probe(base);
    run_case(6);
    prints("DEBUG MODE D5 pcc");
    kv("main_base", base[0]);
    kv("main_len", base[1]);
    kv("mtcc_base", base[4]);
    kv("mtcc_len", base[5]);
    kv("dbg_base", mb[4]);
    kv("dbg_len", mb[5]);
    kv("dbg_perm", mb[6]);
    kv("dbg_tag", mb[7]);
    prints(" INFO\n");

    // P1: at PMODE=1 csrr/csrw dpc and dscratch1 must each raise an illegal
    // instruction exception to DmExcAddr and leave DEPCC/DSCRATCHC1 unchanged.
    run_case(7);
    prints("DEBUG MODE P1 dpc-dscratch1-illegal");
    kv("dmexc_hits", mb[12]);
    kv("dpc", mb[4]);
    kv("dpc_after", mb[5]);
    kv("dscratch1", mb[7]);
    kv("dscratch1_after", mb[6]);
    kv("mtvec_hits", mb[3]);
    verdict(mb[12] != 4 || mb[3] != 0 || mb[5] != mb[4] || mb[6] != mb[7]);

    prints(fails ? "DEBUG MODE SUMMARY FAIL\n" : "DEBUG MODE SUMMARY PASS\n");
    stop_sim();
    return fails != 0;
}
