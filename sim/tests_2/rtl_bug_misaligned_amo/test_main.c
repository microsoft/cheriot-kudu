// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

struct observation {
    unsigned rd;
    unsigned word0;
    unsigned word1;
    unsigned trapped;
    unsigned mcause;
    unsigned mtval;
    unsigned mepc;
};

extern void rv32_atest(struct observation *results);

static struct observation results[2];
static const char *case_names[2] = {"amoswap.w", "sc.w"};

static void print_hex(unsigned value)
{
    char text[11] = "0x00000000";
    char *digits = "0123456789abcdef";
    for (unsigned i = 0; i < 8; ++i)
        text[9 - i] = digits[(value >> (4 * i)) & 15];
    prints(text);
}

int mymain(int argc, int argv)
{
    unsigned failures = 0;
    (void)argc;
    (void)argv;

    prints("Misaligned A-extension test: PMODE=0; AMO/SC must trap before memory update\n");
    rv32_atest(results);

    for (unsigned i = 0; i < 2; ++i) {
        struct observation *r = &results[i];
        unsigned cause_ok = (r->mcause == 6u) || (r->mcause == 7u);
        unsigned mem_ok = (r->word0 == 0x11223344u) && (r->word1 == 0x55667788u);
        unsigned rd_ok = (r->rd == 0xdeadbeefu);
        unsigned failed = (r->trapped != 1u) || !cause_ok || !mem_ok || !rd_ok;
        failures += failed;
        prints(failed ? "FAIL " : "PASS ");
        prints((char *)case_names[i]);
        prints(" trapped="); print_hex(r->trapped);
        prints(" mcause="); print_hex(r->mcause);
        prints(" mtval="); print_hex(r->mtval);
        prints(" rd="); print_hex(r->rd);
        prints(" word0="); print_hex(r->word0);
        prints(" word1="); print_hex(r->word1);
        prints("\n");
    }

    prints(failures ? "MISALIGNED AMO FAIL failures=" : "MISALIGNED AMO PASS failures=");
    print_hex(failures);
    prints(" cases=0x00000002\n");
    stop_sim();
    return failures != 0;
}
