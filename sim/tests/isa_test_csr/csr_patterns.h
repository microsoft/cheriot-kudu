// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

typedef void (*csr_access)(unsigned, unsigned, unsigned, unsigned *, unsigned);

#define CSR_LIST(X) \
    X(status, 0x300, 0x00200088) \
    X(isa, 0x301, 0) \
    X(ie, 0x304, 0x7fff0888) \
    X(counteren, 0x306, 0) \
    X(inhibit, 0x320, 5) \
    X(scratch, 0x340, 0xffffffff) \
    X(cause, 0x342, 0x8000001f) \
    X(tval, 0x343, 0xffffffff) \
    X(ip, 0x344, 0) \
    X(tselect, 0x7a0, 0) \
    X(tdata1, 0x7a1, 0) \
    X(tdata2, 0x7a2, 0) \
    X(tdata3, 0x7a3, 0) \
    X(mcontext, 0x7a8, 0) \
    X(scontext, 0x7aa, 0) \
    X(control, 0x7c0, 0x10) \
    X(seed, 0x7c1, 0) \
    X(cycle, 0xb00, 0xffffffff) \
    X(cycleh, 0xb80, 0xffffffff) \
    X(instret, 0xb02, 0xffffffff) \
    X(instreth, 0xb82, 0xffffffff)

#ifdef CHERIOT
#define MODE_CSRS(X) \
    X(watermark, 0xbc1, 0xfffffff0) \
    X(watermarkbase, 0xbc2, 0xfffffff0) \
    X(watermarkcontrol, 0xbc4, 1)
#else
#define MODE_CSRS(X) \
    X(vector, 0x305, 0xfffffffc) \
    X(epc, 0x341, 0xfffffffe)
#endif

#define DECLARE(name, address, mask) \
    extern void csr_pattern_##name(unsigned, unsigned, unsigned, unsigned *, unsigned);
CSR_LIST(DECLARE)
MODE_CSRS(DECLARE)
#undef DECLARE

static void csr_hex_digits(unsigned value, int digits)
{
    for (int shift = 4 * digits - 4; shift >= 0; shift -= 4)
        send_char("0123456789abcdef"[(value >> shift) & 15]);
}

static void csr_hex(unsigned value)
{
    csr_hex_digits(value, 8);
}

static void csr_dec(unsigned value)
{
    char digits[10];
    unsigned count = 0;
    do {
        digits[count++] = '0' + value % 10;
        value /= 10;
    } while (value != 0);
    while (count != 0)
        send_char(digits[--count]);
}

static unsigned csr_patterns(void)
{
    static const struct {
        csr_access access;
        unsigned address, mask;
    } csrs[] = {
#define ENTRY(name, address, mask) {csr_pattern_##name, address, mask},
        CSR_LIST(ENTRY)
        MODE_CSRS(ENTRY)
#undef ENTRY
    };
    static const unsigned patterns[] = {
        0, 0xffffffff, 0xaaaaaaaa, 0x55555555, 0x80000100, 0x80000308
    };
    static const unsigned immediates[] = {0, 1, 8, 16, 21, 31};
    unsigned status, ie, inhibit, failures = 0, cases = 0;
    __asm__ volatile("csrrc %0, mstatus, %1" : "=r"(status) : "r"(8) : "memory");
    __asm__ volatile("csrrw %0, mie, zero" : "=r"(ie) :: "memory");
    __asm__ volatile("csrrs %0, mcountinhibit, %1" : "=r"(inhibit) : "r"(5) : "memory");
    for (unsigned c = 0; c < sizeof(csrs) / sizeof(csrs[0]); ++c) {
        for (unsigned p = 0; p < sizeof(patterns) / sizeof(patterns[0]); ++p) {
            for (unsigned op = 0; op < 16; ++op) {
                // Register SET starts with complementary bits; CLEAR starts
                // with populated bits. Also test an actual non-x0 zero source.
                unsigned operands[] = {~patterns[p], patterns[p], 0, 0x200};
                unsigned n = op < 2 ? 4 : 1;
                // Other CPUCTRL bits depend on CFG and control the cache and
                // predictors. Only zimm=0/16 isolate constant-fetch safely.
                if (csrs[c].address == 0x7c0 && op >= 4 && op < 14 &&
                    op != 8 && op != 9)
                    continue;
                for (unsigned m = 0; m < n; ++m) {
                    unsigned operand = op < 2 ? operands[m] :
                        op < 14 ? immediates[(op - 2) / 2] : 0;
                    unsigned result[5];
                    unsigned mask = csrs[c].mask;
                    // Do not toggle unrelated active controls or reserved bits.
                    // Ignored-write registers deliberately receive all patterns.
                    unsigned source = mask ? operand & mask : operand;
                    csrs[c].access(patterns[p], source, op, result, mask);
                    unsigned initial = (patterns[p] & mask) | (result[0] & ~mask);
                    unsigned expected = (op & 1) ? initial & ~(operand & mask) :
                                                        initial | (operand & mask);
                    ++cases;
                    if (result[1] != initial || result[2] != initial ||
                        result[3] != expected || result[4] != result[0]) {
                        ++failures;
                        prints("CSR pattern failed csr=0x"); csr_hex_digits(csrs[c].address, 4);
                        prints(" op="); csr_hex(op);
                        prints(" seed="); csr_hex(initial);
                        prints(" mask="); csr_hex(operand);
                        prints(" seeded="); csr_hex(result[1]);
                        prints(" old="); csr_hex(result[2]);
                        prints(" read="); csr_hex(result[3]);
                        prints(" expected="); csr_hex(expected);
                        prints(" saved="); csr_hex(result[0]);
                        prints(" restored="); csr_hex(result[4]);
                        prints("\n");
                    }
                }
            }
            prints("CSR patterns done csr=0x"); csr_hex_digits(csrs[c].address, 4);
            prints(" total_cases="); csr_dec(cases);
            prints(" total_failures="); csr_dec(failures);
            prints("\n");
        }
    }
    __asm__ volatile("csrw mcountinhibit, %0" :: "r"(inhibit) : "memory");
    __asm__ volatile("csrw mie, %0" :: "r"(ie) : "memory");
    __asm__ volatile("csrw mstatus, %0" :: "r"(status) : "memory");
    prints("CSR patterns cases="); csr_dec(cases);
    prints(" failures="); csr_dec(failures); prints("\n");
    return failures;
}
