// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

extern void cheri_atest(unsigned *results);
static unsigned results[3];

static void print_hex(unsigned value)
{
    static const char hex[] = "0123456789abcdef";
    prints("0x");
    for (int i = 7; i >= 0; --i) {
        send_char(hex[(value >> (i * 4)) & 0xf]);
    }
}

int mymain(int argc, int argv)
{
    (void)argc;
    (void)argv;
    cheri_atest(results);
    prints("MRET without PCC.ASR should report CHERI ASR violation in mtval\n");
    prints("observed mcause=");
    print_hex(results[0]);
    prints(" mtval=");
    print_hex(results[1]);
    prints(" traps=");
    print_hex(results[2]);
    prints("\n");
    if (results[2] == 1 && results[0] == 0x1c && results[1] == 0x418) {
        prints("MRET_ASR_MTVAL PASS failures=0x00000000 cases=0x00000001\n");
        stop_sim();
        return 0;
    }
    prints("MRET_ASR_MTVAL FAIL failures=0x00000001 cases=0x00000001\n");
    stop_sim();
    return 1;
}
