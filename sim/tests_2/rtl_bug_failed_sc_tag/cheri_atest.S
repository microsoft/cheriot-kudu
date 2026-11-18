// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Selects one of the two generated LR/SC/AMO sweeps (cmem review, gen_amo.py):
// cm_amo1.S (default) or cm_amo2.S (built with -DAMO_SWEEP=2).
#if defined(AMO_SWEEP) && AMO_SWEEP == 2
#include "cm_amo2.S"
#else
#include "cm_amo1.S"
#endif
