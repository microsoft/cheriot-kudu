// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

// Check lines: "<PASS|FAIL> <tag> c<n> <what> act=... exp=..."
//   tag MTVAL    -> KUDU-041 (illegal CSR access mtval at PMODE=0 / RV32)
//   tag MSTATUSH -> KUDU-042 (mstatush must exist on RV32 and read as 0)
//   tag CDBG     -> KUDU-043 (CDBG_CTRL.0 must escalate tag clearing to a fault)
//   tag CTRL     -> control, must always pass

#define NO_TRAP 0xffffu
#define ILLEGAL 0x2u
#define CHERI_FAULT 0x1cu
#define SENTINEL 0x5555aaaau

#define NCASES 8
#ifdef __CHERI_PURE_CAPABILITY__
#define MODE_STR "PMODE=1"
#else
#define MODE_STR "PMODE=0/RV32"
#endif

extern void csr_atest(unsigned *results);
static unsigned results[4 * NCASES];
static unsigned failures, checks;

static void hex(unsigned value)
{
    const char *digits = "0123456789abcdef";
    prints("0x");
    for (int i = 7; i >= 0; --i)
        send_char(digits[(value >> (4 * i)) & 15]);
}

static void dec(unsigned value)
{
    char buf[11];
    int n = 0;
    do {
        buf[n++] = '0' + value % 10;
        value /= 10;
    } while (value);
    while (n)
        send_char(buf[--n]);
}

static void check(const char *tag, int c, const char *name, const char *field,
                  unsigned act, unsigned exp)
{
    unsigned failed = act != exp;
    failures += failed;
    ++checks;
    prints(failed ? "FAIL " : "PASS ");
    prints((char *)tag);
    prints(" c");
    dec(c);
    prints(" ");
    prints((char *)name);
    prints(" ");
    prints((char *)field);
    prints(" act=");
    hex(act);
    prints(" exp=");
    hex(exp);
    prints("\n");
}

// One case: the mcause line (and the value line when no trap is expected)
// carry mtag, the mtval line carries vtag.
static void check_case(int c, const char *mtag, const char *vtag, const char *name,
                       unsigned mcause, unsigned mtval, unsigned value)
{
    unsigned *r = results + 4 * c;
    check(mtag, c, name, "mcause", r[0], mcause);
    if (mcause != NO_TRAP)
        check(vtag, c, name, "mtval", r[1], mtval);
    else
        check(mtag, c, name, "value", r[2], value);
}

int mymain(int argc, int argv)
{
    (void)argc;
    (void)argv;
    failures = 0;    // .bss is not cleared by the CHERIoT startup
    checks = 0;
    for (int i = 0; i < 4 * NCASES; ++i)
        results[i] = 0;
    csr_atest(results);
#ifdef __CHERI_PURE_CAPABILITY__
    check_case(0, "CTRL", "CTRL", "csrr-0x3ff", ILLEGAL, 0, 0);
    check_case(1, "CTRL", "CTRL", "csrw-mvendorid", ILLEGAL, 0, 0);
    check_case(2, "MSTATUSH", "MSTATUSH", "csrr-mstatush", NO_TRAP, 0, 0);
    check_case(3, "MSTATUSH", "MSTATUSH", "csrw-mstatush", NO_TRAP, 0, 0);
    check_case(4, "MSTATUSH", "MSTATUSH", "csrr-mstatush-after-write", NO_TRAP, 0, 0);
    check_case(5, "CTRL", "CTRL", "csrw-cdbg_ctrl", NO_TRAP, 0, 1);
    check("CDBG", 6, "tclr-csetboundsimm", "mcause", results[4 * 6], CHERI_FAULT);
    check("CDBG", 6, "tclr-csetboundsimm", "cd-tag", results[4 * 6 + 2], 1);
    check_case(7, "CTRL", "CTRL", "csetboundsimm-no-cdbg", NO_TRAP, 0, 0);
#else
    // Illegal instructions report the instruction bits in mtval (as the
    // custom-0 control and cheriot-ibex ibex_controller.sv:759-762 do).
    unsigned insn[NCASES];
    for (int i = 0; i < NCASES; ++i)
        insn[i] = *(volatile unsigned *)results[4 * i + 3];
    check_case(0, "CTRL", "MTVAL", "csrr-0x3ff", ILLEGAL, insn[0], 0);
    check_case(1, "CTRL", "MTVAL", "csrw-mvendorid", ILLEGAL, insn[1], 0);
    check_case(2, "CTRL", "MTVAL", "csrrwi-0x3ff", ILLEGAL, insn[2], 0);
    check_case(3, "CTRL", "CTRL", "custom0", ILLEGAL, 0x0000000bu, 0);
    check_case(4, "CTRL", "CTRL", "csrr-mscratch", NO_TRAP, 0, 0x1234);
    check_case(5, "MSTATUSH", "MSTATUSH", "csrr-mstatush", NO_TRAP, 0, 0);
    check_case(6, "MSTATUSH", "MSTATUSH", "csrw-mstatush", NO_TRAP, 0, 0);
    check_case(7, "MSTATUSH", "MSTATUSH", "csrr-mstatush-after-write", NO_TRAP, 0, 0);
#endif
    prints(failures ? "CSR MTVAL MSTATUSH " MODE_STR " FAIL failures="
                    : "CSR MTVAL MSTATUSH " MODE_STR " PASS failures=");
    dec(failures);
    prints(" cases=");
    dec(checks);
    prints("\n");
    stop_sim();
    return failures != 0;
}
