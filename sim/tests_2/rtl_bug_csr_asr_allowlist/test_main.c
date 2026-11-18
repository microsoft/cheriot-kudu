// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

#define NCASES 8
#define NO_TRAP 0xffffu
#define CHERI_FAULT 0x1cu
#define ILLEGAL 0x2u
#define ASR_PCC 0x418u  // PCC (0x20 << 5) | ASR violation (0x18)

extern void cheri_atest(unsigned *results);
static unsigned results[2 * NCASES];

// op: 0 = csrr, 1 = csrw. Expected values follow the CHERIoT Sail model.
static const struct {
    unsigned op, csr, mcause, mtval;
    const char *what;
} cases[NCASES] = {
    {1, 0xb00, CHERI_FAULT, ASR_PCC, "write mcycle (allow-list is read-only)"},
    {1, 0xb02, CHERI_FAULT, ASR_PCC, "write minstret (allow-list is read-only)"},
    {1, 0xb80, CHERI_FAULT, ASR_PCC, "write mcycleh (allow-list is read-only)"},
    {1, 0xb82, CHERI_FAULT, ASR_PCC, "write minstreth (allow-list is read-only)"},
    {0, 0x323, ILLEGAL, 0, "read unimplemented mhpmevent3 (illegal before ASR)"},
    {1, 0x323, ILLEGAL, 0, "write unimplemented mhpmevent3 (illegal before ASR)"},
    {0, 0xb00, NO_TRAP, 0, "control: read mcycle is allowed"},
    {0, 0x300, CHERI_FAULT, ASR_PCC, "control: read mstatus needs ASR"},
};

static void hex(unsigned value, int n)
{
    const char *digits = "0123456789abcdef";
    prints("0x");
    for (int i = n - 1; i >= 0; --i)
        send_char(digits[(value >> (4 * i)) & 15]);
}

static void dec(unsigned value)
{
    char buf[11];
    int n = 0;
    do {
        buf[n++] = '0' + value % 10;
        value /= 10;
    } while (value);
    while (n)
        send_char(buf[--n]);
}

int mymain(int argc, int argv)
{
    unsigned failures = 0;
    (void)argc;
    (void)argv;
    for (int i = 0; i < 2 * NCASES; ++i)
        results[i] = 0;
    cheri_atest(results);
    for (int i = 0; i < NCASES; ++i) {
        unsigned mcause = results[2 * i], mtval = results[2 * i + 1];
        unsigned failed = mcause != cases[i].mcause || mtval != cases[i].mtval;
        failures += failed;
        prints(failed ? "FAIL " : "PASS ");
        prints(cases[i].op ? "csrw " : "csrr ");
        hex(cases[i].csr, 4);
        prints(" mcause="); hex(mcause, 8);
        prints(" mtval="); hex(mtval, 8);
        prints(" expected="); hex(cases[i].mcause, 8);
        prints("/"); hex(cases[i].mtval, 8);
        prints(" "); prints((char *)cases[i].what);
        prints("\n");
    }
    prints(failures ? "CSR ASR FAIL failures=" : "CSR ASR PASS failures=");
    dec(failures);
    prints(" cases=");
    dec(NCASES);
    prints("\n");
    stop_sim();
    return failures != 0;
}
