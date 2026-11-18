// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

extern void cheri_atest(unsigned *results);
static unsigned results[2];

static void print_bit(unsigned value)
{
    send_char((value & 1) ? '1' : '0');
}

int mymain(int argc, int argv)
{
    (void)argc;
    (void)argv;
    cheri_atest(results);
    prints("TRVK boundary: in-range tag should clear; one-past-covered heap tag should stay set\n");
    prints(results[0] == 0 ? "PASS in_range tag=" : "FAIL in_range tag=");
    print_bit(results[0]);
    prints("\n");
    prints(results[1] == 1 ? "PASS boundary tag=" : "FAIL boundary tag=");
    print_bit(results[1]);
    prints("\n");
    if (results[0] == 0 && results[1] == 1) {
        prints("TRVK_BOUNDARY PASS failures=0x00000000 cases=0x00000002\n");
        stop_sim();
        return 0;
    }
    prints("TRVK_BOUNDARY FAIL failures=0x00000001 cases=0x00000002\n");
    stop_sim();
    return 1;
}
