// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Directed debug-mode tests (review round 4), reduced to the KUDU-071
// cases: 33 (step onto ebreak) and 34 (step onto an execute trigger). Each
// case is preceded by a reset case (0).

#include <util.h>
#include "dbg_mb.h"

#ifdef CHERIOT
extern void *from_root(unsigned int);
#define MMIO ((volatile unsigned *)from_root(0x83800000U))
#define ADDR(p) ((unsigned)__builtin_cheri_address_get(p))
#else
#define MMIO ((volatile unsigned *)0x83800000U)
#define ADDR(p) ((unsigned)(p))
#endif

extern int run_case(int n, volatile unsigned *mmio, volatile unsigned *mb);

static volatile unsigned mb[MB_SIZE / 4] __attribute__((aligned(64)));

static void print_hex(unsigned v)
{
    prints("0x");
    for (int i = 7; i >= 0; --i)
        send_char("0123456789abcdef"[(v >> (4 * i)) & 15]);
}

static void print_dec(unsigned v)
{
    char b[12];
    int n = 0;
    do { b[n++] = '0' + v % 10; v /= 10; } while (v);
    while (n) send_char(b[--n]);
}

static void kv(char *k, unsigned v)
{
    prints(" "); prints(k); prints("="); print_hex(v);
}

static void clear_mb(void)
{
    for (int i = 0; i < MB_SIZE / 4; ++i)
        mb[i] = 0;
}

static const int cases[] = { 33, 34 };

int mymain(int a, int b)
{
    volatile unsigned *mmio = MMIO;
    int nf = 0;
    mmio[1] = ADDR(mb);
    prints("DBGT START\n");
    for (unsigned i = 0; i < sizeof(cases) / sizeof(cases[0]); ++i) {
        int n = cases[i];
        clear_mb();
        int r0 = run_case(0, mmio, mb);
        clear_mb();
        prints("CASE ");
        print_dec(n);
        int r = run_case(n, mmio, mb);
        if (r0 != 0 || r != 0) {
            nf++;
            prints(" FAIL");
            kv("r0", r0);
            kv("n", r);
            kv("fid", mb[MB_FID / 4]);
            kv("got", mb[MB_FGOT / 4]);
            kv("exp", mb[MB_FEXP / 4]);
        } else {
            prints(" PASS");
        }
        kv("cnt", mb[MB_CNT / 4]);
        kv("tcnt", mb[MB_TCNT / 4]);
        kv("w0", mb[MB_W0 / 4]);
        kv("w1", mb[MB_W1 / 4]);
        prints("\n");
        unsigned c = mb[MB_CNT / 4];
        if (c > 8) c = 8;
        for (unsigned k = 0; k < c; ++k) {
            prints("  log");
            print_dec(k);
            kv("dcsr", mb[(MB_LOG + 16 * k) / 4]);
            kv("dpc", mb[(MB_LOG + 16 * k + 4) / 4]);
            kv("mcause", mb[(MB_LOG + 16 * k + 8) / 4]);
            kv("mepc", mb[(MB_LOG + 16 * k + 12) / 4]);
            prints("\n");
        }
    }
    prints("DBGT DONE fails=");
    print_dec(nf);
    prints("\n");
    return 0;
}
