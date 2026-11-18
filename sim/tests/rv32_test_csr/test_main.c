// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>
#include "../isa_test_csr/csr_patterns.h"

extern int rv32_atest(void);

int mymain(void)
{
    prints("rv32_test_csr: starting (PMODE=0)\n");
    unsigned int patterns = csr_patterns();
    prints("CSR trap/matrix checks starting (66 expected traps)\n");
    int traps = rv32_atest();
    if (traps == 0 && patterns == 0) {
        prints("rv32_test_csr: CSR test passed\n");
    } else {
        prints("rv32_test_csr: CSR test failed\n");
    }
    stop_sim();
    return 0;
}
