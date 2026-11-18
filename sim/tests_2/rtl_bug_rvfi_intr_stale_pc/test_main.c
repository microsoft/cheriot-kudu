// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include <util.h>
extern void cheri_atest(void);
int mymain(int argc, int argv)
{
    (void)argc; (void)argv;
    prints("SIGSTART\n");
    cheri_atest();
    prints("SIGEND\n");
    stop_sim();
    return 0;
}
