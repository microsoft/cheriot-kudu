// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// step_exec: run the same workload with dcsr.step = 0 (reference) and
// dcsr.step = 1, and check that every result matches. Every step must enter
// debug mode with dcsr.cause = STEP: mb[2] counts the STEPPING entries and mb[6]
// those with another cause.

#include <util.h>

extern void install_handler(void);
extern int dbg_request(volatile int *mb);
extern int workload(int *buf, int seed, int iters);

#define NW 3
#define NBUF 160
static volatile int mb[16];
static long long buf64[NBUF / 2];
static int fails;

static const int seeds[NW] = {0x1234, 0x7f00ff01, 0x5a5a1};
static const int iters[NW] = {48, 40, 33};
static unsigned ref_sum[NW], ref_trap[NW], ref_mem[NW];
static int ref_buf[NW][NBUF];
static int saving;

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

static unsigned last_scfail;

static void run_w(int i, unsigned *sum, unsigned *trap, unsigned *mem)
{
    int *buf = (int *)buf64;
    unsigned h = 0;
    for (int k = 0; k < NBUF; ++k)
        buf[k] = k * 0x01010101;
    *sum = (unsigned)workload(buf, seeds[i], iters[i]);
    *trap = (unsigned)buf[150];
    last_scfail = (unsigned)buf[151] - 151u * 0x01010101u;
    int nd = 0;
    for (int k = 0; k < NBUF; ++k) {
        // 132/133: capability; 130: LR/SC word and 151: SC failure count
        // (debug entry between LR and SC may legally fail the SC)
        if (k == 130 || k == 151 || k == 132 || k == 133)
            continue;
        h = ((h << 5) | (h >> 27)) ^ (unsigned)buf[k];
        if (saving)
            ref_buf[i][k] = buf[k];
        else if (buf[k] != ref_buf[i][k] && nd < 4) {
            nd++;
            prints("STEP EXEC   diff");
            kv("idx", k);
            kv("got", buf[k]);
            kv("exp", ref_buf[i][k]);
            prints("\n");
        }
    }
    *mem = h;
}

static void check_w(char *tag, int i)
{
    unsigned s, t, m;
    run_w(i, &s, &t, &m);
    prints(tag);
    send_char('0' + i);
    kv("sum", s);
    kv("exp", ref_sum[i]);
    kv("traps", t);
    kv("exp", ref_trap[i]);
    kv("mem", m);
    kv("exp", ref_mem[i]);
    kv("sc_fail(info)", last_scfail);
    verdict(s != ref_sum[i] || t != ref_trap[i] || m != ref_mem[i]);
}

int mymain(int argc, int argv)
{
    (void)argc;
    (void)argv;
    int ok;

    fails = 0;               // .bss is not zeroed by the startup code
    for (int k = 0; k < 16; ++k)
        mb[k] = 0;
    install_handler();

    prints("STEP EXEC start\n");
    saving = 1;
    for (int i = 0; i < NW; ++i) {
        run_w(i, &ref_sum[i], &ref_trap[i], &ref_mem[i]);
        prints("STEP EXEC REF W");
        send_char('0' + i);
        kv("sum", ref_sum[i]);
        kv("traps", ref_trap[i]);
        kv("mem", ref_mem[i]);
        prints("\n");
    }
    saving = 0;
    // repeatability with step = 0
    check_w("STEP EXEC STEP0 W", 0);

    // turn on dcsr.step
    mb[0] = 1;
    ok = dbg_request(mb);
    prints("STEP EXEC SET");
    kv("rom_entered", ok);
    kv("dcsr", mb[3]);
    kv("phase", mb[0]);
    verdict(!ok || mb[0] != 2);

    for (int i = 0; i < NW; ++i)
        check_w("STEP EXEC STEP1 W", i);

    // clear dcsr.step: the ROM runs with dcsr.step = 1 in debug mode
    mb[0] = 3;
    ok = dbg_request(mb);
    prints("STEP EXEC CLEAR");
    kv("rom_entered", ok);
    kv("step_entries", mb[2]);
    kv("dcsr_at_clear", mb[4]);
    kv("rom_val", mb[5]);
    kv("bad_cause", mb[6]);
    kv("phase", mb[0]);
    verdict(!ok || mb[0] != 4 || !(mb[4] & 4) || mb[5] != 1682 || mb[2] < 1000 || mb[6] != 0);

    check_w("STEP EXEC POST W", 1);

    prints(fails ? "STEP EXEC FAIL failures=" : "STEP EXEC PASS failures=");
    print_hex(fails);
    prints("\n");
    stop_sim();
    return fails != 0;
}
