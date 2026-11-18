// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.option norelax
.section .text
.globl read_misa

read_misa:
    csrr a0, misa
    cret
