// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include <util.h>
extern void cheri_atest(unsigned *r);
static void hex(unsigned v) { const char *d = "0123456789abcdef"; for (int i = 7; i >= 0; --i) send_char(d[(v >> (4*i)) & 15]); }
int mymain(int argc, int argv) {
  unsigned r[4];
  (void)argc; (void)argv;
  cheri_atest(r);
  prints("RA_ODD nodd="); hex(r[0]); prints(" nirq="); hex(r[1]); prints(" nexc="); hex(r[2]);
  prints(r[0] ? " FAIL\n" : " PASS\n");
  stop_sim();
  return 0;
}
