// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Mailbox (DRAM, address published in TB scratch1 0x8380_0004) shared by
// the debug ROM and the directed debug tests. Byte offsets.
#define MB_CNT          0x00
#define MB_SAVE13       0x04
#define MB_OR           0x08
#define MB_ANDN         0x0C
#define MB_NEWDPC       0x10
#define MB_STEP_STOP    0x14
#define MB_TRIG_APPLY   0x18
#define MB_T0_D1        0x1C
#define MB_T0_D2        0x20
#define MB_T1_D1        0x24
#define MB_T1_D2        0x28
#define MB_TRIG_RB0     0x2C
#define MB_TRIG_RB1     0x30
#define MB_DEXC_OP      0x34
#define MB_DEXC_CNT     0x38
#define MB_DEXC_DCSR    0x3C
#define MB_DEXC_DPC     0x40
#define MB_DEXC_MCAUSE  0x44
#define MB_DEXC_MEPC    0x48
#define MB_DEXC_MSTATUS 0x4C
#define MB_DEXC_MTVAL   0x50
#define MB_PRE_MCAUSE   0x54
#define MB_PRE_MEPC     0x58
#define MB_PRE_MSTATUS  0x5C
#define MB_PRE_MTVAL    0x60
#define MB_HALT_ON_EXIT 0x64
#define MB_EXIT_MODE    0x68
#define MB_EBRK_CNT     0x6C
#define MB_EBRK_DCSR    0x70
#define MB_EBRK_DPC     0x74
#define MB_MIP_DBG      0x78
#define MB_SPIN         0x7C
#define MB_TCNT         0x80
#define MB_TCAUSE       0x84
#define MB_TEPC         0x88
#define MB_TVAL         0x8C
#define MB_RESUME       0x90
#define MB_HSAVE12      0x94
#define MB_TMSTATUS     0x98
#define MB_NFAIL        0x9C
#define MB_FID          0xA0
#define MB_FGOT         0xA4
#define MB_FEXP         0xA8
#define MB_EXIT_VAL     0xAC
#define MB_DEPCC_TAG    0xB0
#define MB_DEPCC_BASE   0xB4
#define MB_DEPCC_LEN    0xB8
#define MB_DEPCC_PERM   0xBC
#define MB_SAVE_RA      0xC0
#define MB_SAVE_S0      0xC8
#define MB_SAVE_S1      0xD0
#define MB_EXIT_ANDN    0xD8
#define MB_TRIG_ONESHOT 0xDC
#define MB_MSTATUS_SET  0xE0
#define MB_SKIP_AT      0xE4
#define MB_SKIP_HIT     0xE8
#define MB_DEPCC_CLRTAG 0xEC
#define MB_W0           0xF0
#define MB_W1           0xF4
#define MB_W2           0xF8
#define MB_W3           0xFC
#define MB_LOG          0x100
// log entry k (k = 0..31) at MB_LOG + 16*k: dcsr, dpc, mcause, mepc
#define LOGOFF(k, f)    (MB_LOG + 16 * (k) + 4 * (f))
#define MB_SIZE         0x300

#define DCSR_STEP       0x4
#define DCSR_EBREAKU    0x1000
#define DCSR_EBREAKM    0x8000
#define TDATA1_EXEC     0x2800104C
