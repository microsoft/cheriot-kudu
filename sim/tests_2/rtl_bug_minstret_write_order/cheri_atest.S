// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.option norelax
.option norvc
.section .text
.globl cheri_atest

cheri_atest:
    li t0, 0
    csrw minstret, t0
    csrr t1, minstret
    csw t1, 0(ca0)
    li t0, 5
    csrw minstret, t0
    csrr t1, minstret
    csw t1, 4(ca0)
    csrr t1, minstret
    csw t1, 8(ca0)
    cret
