// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

extern int cheri_atest(int);

int mymain(int argc, int argv)
{
    (void)argc;
    (void)argv;

    prints("Debug-mode interrupt masking check\n");
    int result = cheri_atest(0);
    if (result == 0) {
        prints("DEBUG IRQ PASS cases=0x00000001\n");
    } else {
        prints("DEBUG IRQ FAIL cases=0x00000001\n");
    }
    stop_sim();
    return result != 0;
}
