// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

// Word 1 of the buffer starts as 0x11111111. Expected value after the store:
//   sw/csw 0xaabbccdd at +2 -> 0x1111aabb; sh/csh 0xccdd at +3 -> 0x111111cc;
//   sw/csw at +4 -> 0xaabbccdd; csc cnull at +0 -> 0x00000000.
#ifdef __CHERI_PURE_CAPABILITY__
#define NCASES 4
#define ST "csw"
#define SH "csh"
#define LW "clw"
extern void cheri_atest(unsigned *obs, unsigned *buf);
#define RUN(o, b) cheri_atest(o, b)
#else
#define NCASES 3
#define ST "sw"
#define SH "sh"
#define LW "lw"
extern void rv32_atest(unsigned *obs, unsigned *buf);
#define RUN(o, b) rv32_atest(o, b)
#endif

// Each case is observed 12 times: gaps 0..3 between store and load, 3 rounds.
#define NOBS 12
static unsigned obs[4 * NOBS * NCASES];
static unsigned buf[4] __attribute__((aligned(16)));

static void hex(unsigned value)
{
    const char *digits = "0123456789abcdef";
    prints("0x");
    for (int i = 7; i >= 0; --i)
        send_char(digits[(value >> (4 * i)) & 15]);
}

static void dec(unsigned v)
{
    char buf[11];
    int n = 0;
    do {
        buf[n++] = '0' + v % 10;
        v /= 10;
    } while (v);
    while (n)
        send_char(buf[--n]);
}

static unsigned check(int c, unsigned expected, const char *tag)
{
    unsigned bad = 0, first = 0;
    for (int i = NOBS - 1; i >= 0; --i) {
        const unsigned *o = &obs[4 * (NOBS * c + i)];
        if (o[0] != expected || o[1] != expected + 1 || o[2] != expected) {
            ++bad;
            first = i;
        }
    }
    const unsigned *o = &obs[4 * (NOBS * c + first)];
    prints(bad ? "FAIL " : "PASS ");
    prints((char *)tag);
    prints(" bad="); dec(bad);
    prints("/12 first_bad_gap="); dec(first % 4);
    prints(" load="); hex(o[0]);
    prints(" load+1="); hex(o[1]);
    prints(" reload="); hex(o[2]);
    prints(" expected="); hex(expected);
    prints("\n");
    return bad != 0;
}

int mymain(int argc, int argv)
{
    unsigned f = 0;
    (void)argc;
    (void)argv;
    // The assembly writes obs[4i .. 4i+2] for every case before it is read.
    RUN(obs, buf);
    f += check(0, 0x1111aabbu, "split-store " ST " X+2 then " LW " X+4 (gaps 0-3 x3):");
    f += check(1, 0x111111ccu, "split-store " SH " X+3 then " LW " X+4 (gaps 0-3 x3):");
    f += check(2, 0xaabbccddu, "ctrl aligned " ST " X+4 then " LW " X+4 (gaps 0-3 x3):");
#ifdef __CHERI_PURE_CAPABILITY__
    f += check(3, 0, "split-store csc cnull X then clw X+4 (gaps 0-3 x3):");
#endif
    prints(f ? "DCACHE SPLIT STORE FAIL failures=" : "DCACHE SPLIT STORE PASS failures=");
    dec(f);
    prints(" cases=");
    dec(NCASES);
    prints("\n");
    stop_sim();
    return f != 0;
}
