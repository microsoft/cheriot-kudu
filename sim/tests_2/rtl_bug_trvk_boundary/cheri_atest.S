// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.option norelax
.section .text
.globl cheri_atest

cheri_atest:
    cincoffset csp, csp, -48
    csc cra, 0(csp)
    csc c8, 8(csp)
    csc c9, 16(csp)
    csc c10, 24(csp)
    csc c15, 32(csp)
    csc c3, 40(csp)

    cmove c10, ca0
    cspecialrw c3, mtdc, c0

    // c6: data/cap root spanning DRAM and the TSMAP SRAM aperture.
    lui x11, 0x80000
    csetaddr c6, c3, x11
    lui x11, 0x4000
    csetbounds c6, c6, x11
    addi x11, x0, 0x7f
    candperm c6, c6, x11

    // Set TSMAP word 0 bit 0. This covers heap base 0x80000000 only.
    lui x11, 0x83000
    csetaddr c9, c6, x11
    addi x12, x0, 1
    csw x12, 0(c9)

    // Control: capability base 0x80000000 is in range and should be revoked.
    lui x11, 0x80010
    csetaddr c8, c6, x11
    csc c6, 0(c8)
    clc c15, 0(c8)
    cgettag x12, c15
    csw x12, 0(c10)

    // Boundary: TSMapSize=1024 words covers 1024*32*8 = 0x40000 bytes.
    // A capability with base 0x80040000 is one byte past the covered heap and
    // must not consult/wrap to TSMAP word 0.
    lui x11, 0x80040
    csetaddr c7, c6, x11
    lui x12, 0x1
    csetbounds c7, c7, x12
    csc c7, 0(c8)
    clc c15, 0(c8)
    cgettag x12, c15
    csw x12, 4(c10)

    clc cra, 0(csp)
    clc c8, 8(csp)
    clc c9, 16(csp)
    clc c10, 24(csp)
    clc c15, 32(csp)
    clc c3, 40(csp)
    cincoffset csp, csp, 48
    cret
