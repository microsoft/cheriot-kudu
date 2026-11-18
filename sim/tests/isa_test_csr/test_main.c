// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>
#include "csr_patterns.h"

extern int cheri_atest(int);

int mymain(void)
{
  prints("Running CHERIoT CSR test (PMODE=1)!\n");
  unsigned int patterns = csr_patterns();
  prints("CSR trap/matrix checks starting (77 expected traps)\n");
  unsigned int result = cheri_atest(0);
  if (result != 0 || patterns != 0) {
    prints("CSR test failed: patterns=");
    csr_dec(patterns);
    prints(" trap/matrix check=0x");
    for (int shift = 28; shift >= 0; shift -= 4)
      send_char("0123456789abcdef"[(result >> shift) & 15]);
    prints("\n");
    return -1;
  }
  prints("CSR test passed: CHERIoT patterns, matrix and 77 precise traps\n");
  return 0;
}
