// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

struct observation {
    unsigned rd;
    unsigned trapped;
    unsigned mcause;
    unsigned mtval;
    unsigned mepc;
};

extern void rv32_atest(struct observation *result);

static struct observation result;

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
    (void)argc;
    (void)argv;
    prints("AMO access-fault cause test: PMODE=0; AMO bus error must be store/AMO access fault\n");
    rv32_atest(&result);

    unsigned failed = (result.trapped != 1u) || (result.mcause != 7u) ||
                      (result.mtval != 0x90000000u) || (result.rd != 0xdeadbeefu);
    prints(failed ? "FAIL amoswap.w-invalid" : "PASS amoswap.w-invalid");
    prints(" trapped="); print_hex(result.trapped);
    prints(" mcause="); print_hex(result.mcause);
    prints(" mtval="); print_hex(result.mtval);
    prints(" rd="); print_hex(result.rd);
    prints("\n");
    prints(failed ? "AMO ACCESS FAULT FAIL failures=0x00000001 cases=0x00000001\n" :
                    "AMO ACCESS FAULT PASS failures=0x00000000 cases=0x00000001\n");
    stop_sim();
    return failed != 0;
}
