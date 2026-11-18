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

#define NCASES 2
#define SPIN_LIMIT 200000

// Read and written by debug_rom.S; see the layout there.
static volatile unsigned mb[8] __attribute__((aligned(16)));
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
    unsigned spins = 0;
    (void)argc;
    (void)argv;
    fails = 0;               // .bss is not zeroed by the startup code
    for (int i = 0; i < 8; ++i)
        mb[i] = 0;
    MMIO[1] = ADDR(mb);      // debug ROM mailbox (TB scratch_reg1)

    // Wait for a random debug request; the ROM runs the check on the first
    // entry and has restored DEPCC/dpc by the time we run again.
    while (mb[0] == 0 && spins < SPIN_LIMIT)
        ++spins;
    unsigned entries = mb[0], rdback = mb[1], tag = mb[2], wrote = mb[3];

    // R1: a DEPCC/dpc write with an odd address must be read back with
    // bit 0 clear (IALIGN = 16), as for MEPCC/mepc.
    prints("DEPCC ODD R1 dpc-bit0");
    kv("wrote", wrote);
    kv("read", rdback);
#ifdef CHERIOT
    kv("tag", tag);
#else
    (void)tag;
#endif
    verdict(entries == 0 || (rdback & 1) != 0);

    // R2 (control): the check ran, the written address was odd and the rest
    // of the address was kept.
    prints("DEPCC ODD R2 control");
    kv("entries", entries);
    kv("spins", spins);
    verdict(entries == 0 || (wrote & 1) == 0 || (rdback | 1) != wrote);

    prints(fails ? "DEPCC ODD FAIL failures=" : "DEPCC ODD PASS failures=");
    dec(fails);
    prints(" cases=");
    dec(NCASES);
    prints("\n");
    stop_sim();
    return fails != 0;
}
