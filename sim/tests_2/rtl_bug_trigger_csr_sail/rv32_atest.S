// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.option norvc
.option norelax
.section .text
.globl rv32_atest

// a0 points at two words: reset tselect read, read after writing 1.
rv32_atest:
    csrr t0, tselect
    sw t0, 0(a0)
    li t1, 1
    csrw tselect, t1
    csrr t0, tselect
    sw t0, 4(a0)
    ret
