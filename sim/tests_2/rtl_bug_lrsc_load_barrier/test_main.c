// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

struct obs { unsigned rd, tag, mem, trapped, mcause, mtval, p0, p1; };
extern void cheri_atest(struct obs *results);
static struct obs r[22];

static void hex(unsigned value)
{
    const char *digits = "0123456789abcdef";
    prints("0x");
    for (int i = 7; i >= 0; --i)
        send_char(digits[(value >> (4 * i)) & 15]);
}

int mymain(int argc, int argv)
{
    unsigned fails = 0;
    static const char *nm[5] = {"lr.w ", "sc.w ", "clw  ", "csw  ", "amoadd"};
    (void)argc; (void)argv;
    for (unsigned i = 0; i < 22; ++i) { r[i].rd = 0; r[i].trapped = 0; }
    cheri_atest(r);
    for (unsigned i = 0; i < 22; ++i) {
        int f;
        unsigned op = i < 20 ? i / 4 : (i == 20 ? 0 : 2);
        if (i < 20) {
            // revoked: tag must be clear and the access must trap with a tag violation (rs1=1)
            f = r[i].tag != 0 || r[i].trapped != 1 || r[i].mcause != 0x1c ||
                r[i].mtval != ((1 << 5) | 2) || r[i].rd != 0xdeadbeef || r[i].mem != 0x12345678;
        } else {
            f = r[i].tag != 1 || r[i].trapped != 0 || r[i].rd != 0x12345678;
        }
        fails += f;
        prints(f ? "FAIL " : "PASS ");
        prints(i < 20 ? "revoked " : "control ");
        prints((char *)nm[op]);
        { static const unsigned nn[4]={0,2,4,8}; prints(" nops="); hex(nn[i & 3]); }
        prints(" tag="); hex(r[i].tag);
        prints(" trapped="); hex(r[i].trapped);
        prints(" mcause="); hex(r[i].mcause);
        prints(" mtval="); hex(r[i].mtval);
        prints(" rd="); hex(r[i].rd);
        prints(" mem="); hex(r[i].mem);
        prints("\n");
    }
    prints(fails ? "LSU RVK LRSC FAIL\n" : "LSU RVK LRSC PASS\n");
    stop_sim();
    return fails != 0;
}
