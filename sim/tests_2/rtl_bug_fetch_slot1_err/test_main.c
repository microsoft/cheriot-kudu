// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>

// Buffers stay below 0x80020000: the TB instruction port aliases DRAM above it.
#define ERR_BUF   0x80010000u
#define ERR_IDX   24u                       // ERR_WORD = ERR_BUF + 0x60
#define ERR_WORD  (ERR_BUF + 4u * ERR_IDX)
#define OK_BUF    0x80011000u
#define BUF_WORDS 32u
#define MAGIC_A4  0xdead0004u

#define NOP       0x00000013u
#define DIV_T6    0x034fcfb3u               // div  t6, t6, s4
#define ADD_T6    0x01ff8fb3u               // add  t6, t6, t6 (waits for the divs)
#define ADDI_A4   0x04400713u               // addi a4, x0, 0x44
#define ADDI_A5   0x05500793u               // addi a5, x0, 0x55
#define JR_S3     0x00098067u               // jalr x0, 0(s3)

struct obs { unsigned trapped, mcause, mepc, mtval, a4, a3; };

extern void rv32_atest(struct obs *r, unsigned entry);

static struct obs r;
static unsigned failures, cases;

static void hex(unsigned value)
{
    char text[] = "0x00000000";
    const char *digits = "0123456789abcdef";
    for (unsigned i = 0; i < 8; ++i)
        text[9 - i] = digits[(value >> (4 * i)) & 15];
    prints(text);
}

static void detail(void)
{
    prints(" trapped="); hex(r.trapped);
    prints(" mcause="); hex(r.mcause);
    prints(" mepc="); hex(r.mepc);
    prints(" mtval="); hex(r.mtval);
    prints(" a4="); hex(r.a4);
    prints(" a3="); hex(r.a3);
    prints("\n");
}

static void verdict(const char *tag, unsigned failed, const char *note)
{
    ++cases;
    failures += failed;
    prints((char *)tag);
    prints(failed ? " FAIL " : " PASS ");
    prints((char *)note);
    prints("\n");
}

// Word N (just before ERR_WORD) ends with an instruction that fetch_fifo64
// hands out as slot 0 together with the first instruction of ERR_WORD:
//   type 0: [addi a6 (32b)][c.li a2][c.li a3]  -> c.li a3 at hw3 is compressed
//   type 1: [c.li a2][c.li a6][addi a3 (32b)]  -> addi a3 at hw2 is 32-bit
// pad < 0: entered at word N.  pad >= 0: entered at a DIV/DIV/ADD stall,
// followed by pad words of NOPs, so the IR stage fills up and ERR_WORD is
// already buffered when word N reaches the aligner, whatever the fetch latency.
static unsigned build(unsigned base, unsigned type, int pad)
{
    volatile unsigned *b = (volatile unsigned *)base;
    unsigned entry_idx = ERR_IDX - 2;
    for (unsigned i = 0; i < BUF_WORDS; ++i)
        b[i] = NOP;
    if (type == 0) {
        b[ERR_IDX - 2] = 0x01100813u;       // addi a6, x0, 0x11
        b[ERR_IDX - 1] = 0x46994615u;       // c.li a2, 5 ; c.li a3, 6
    } else {
        b[ERR_IDX - 2] = 0x481d4615u;       // c.li a2, 5 ; c.li a6, 7
        b[ERR_IDX - 1] = 0x00600693u;       // addi a3, x0, 6
    }
    b[ERR_IDX + 0] = ADDI_A4;
    b[ERR_IDX + 1] = ADDI_A5;
    b[ERR_IDX + 2] = JR_S3;
    if (pad >= 0) {
        entry_idx = ERR_IDX - 2 - 2 * (unsigned)pad - 4;
        b[entry_idx + 0] = DIV_T6;
        b[entry_idx + 1] = DIV_T6;
        b[entry_idx + 2] = ADD_T6;
    }
    return base + 4 * entry_idx;
}

static const int pads[] = { -1, 0, 2, 4, 6, 8 };
#define NPADS (sizeof(pads) / sizeof(pads[0]))

static void try_name(unsigned type, int pad)
{
    prints(type ? "B" : "A");
    if (pad < 0) {
        prints("_nostall");
    } else {
        prints("_pad");
        hex((unsigned)pad);
    }
}

int mymain(int argc, int argv)
{
    unsigned injecting, bad_noerr = 0, hits = 0, other = 0, tries = 0;
    (void)argc;
    (void)argv;
    failures = 0;   // .bss is not zeroed by csrc_rv32 startup
    cases = 0;

    // Controls: every sequence runs to completion where no fetch error is injected.
    for (unsigned t = 0; t < 2; ++t)
        for (unsigned p = 0; p < NPADS; ++p) {
            rv32_atest(&r, build(OK_BUF, t, pads[p]));
            unsigned bad = r.trapped != 0 || r.a4 != 0x44 || r.a3 != 6;
            bad_noerr += bad;
            prints("FSLOT1_INFO noerr ");
            try_name(t, pads[p]);
            prints(bad ? " wrong" : " ok");
            detail();
        }
    verdict("FSLOT1_CTRL_NOERR", bad_noerr != 0, "all sequences complete without a trap");

    // Control: ERR_WORD fetched as the first word after a jump faults correctly.
    build(ERR_BUF, 0, -1);
    rv32_atest(&r, ERR_WORD);
    injecting = r.trapped != 0;
    prints("FSLOT1_INFO firstword");
    detail();
    verdict("FSLOT1_CTRL_FIRSTWORD",
            !(r.trapped == 1 && r.mcause == 1 && r.mepc == ERR_WORD &&
              r.mtval == ERR_WORD && r.a4 == MAGIC_A4 && r.a3 == 0),
            injecting ? "fault at ERR_WORD" :
                        "no instruction-fetch error injected (needs +INSTR_ERR_ADDR=80010060)");

    // Bug: the instruction at ERR_WORD must take an instruction access fault
    // (mcause 1, mepc = mtval = ERR_WORD) before it writes a4.
    if (injecting) {
        for (unsigned t = 0; t < 2; ++t)
            for (unsigned p = 0; p < NPADS; ++p) {
                rv32_atest(&r, build(ERR_BUF, t, pads[p]));
                unsigned ok = r.trapped == 1 && r.mcause == 1 && r.mepc == ERR_WORD &&
                              r.mtval == ERR_WORD && r.a4 == MAGIC_A4 && r.a3 == 6;
                unsigned hit = r.trapped == 1 && r.mcause == 1 && r.a4 == 0x44 &&
                               r.mepc == ERR_WORD + 4;
                ++tries;
                hits += hit;
                other += !ok && !hit;
                prints("FSLOT1_INFO err ");
                try_name(t, pads[p]);
                prints(ok ? " ok" : (hit ? " slot1-err-lost" : " wrong"));
                detail();
            }
        prints("FSLOT1_KUDU013_SLOT1_ERR");
        prints(hits || other ? " FAIL" : " PASS");
        prints(" slot1-err-lost="); hex(hits);
        prints(" other-wrong="); hex(other);
        prints(" tries="); hex(tries);
        prints("\n");
        ++cases;
        failures += (hits || other);
    } else {
        prints("FSLOT1_KUDU013_SLOT1_ERR SKIP no instruction-fetch error injected\n");
    }

    prints(failures || !injecting ? "FSLOT1 FAIL failures=" : "FSLOT1 PASS failures=");
    hex(failures);
    prints(" cases=");
    hex(cases);
    prints("\n");
    stop_sim();
    return failures != 0;
}
