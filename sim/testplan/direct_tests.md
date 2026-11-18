# CHERIoT-Kudu directed RTL-bug tests (sim/tests_2)

[sim/tests_2](../tests_2) holds one self-checking directed test for every RTL
bug in [bug_logs.md](bug_logs.md), [bug_logs_2.md](bug_logs_2.md) and
[bug_logs_3.md](bug_logs_3.md) that can be reproduced by simulation, lint or
a flow check (59 tests, 152 runs). Each test lives in its own directory,
**sim/tests_2/rtl_bug_&lt;name&gt;/**, which contains only its **run.py** and the
sources it needs: program sources, a local linker script or debug ROM,
checker modules, testbench patches and post-processing checkers. Everything
they share lives in **sim/tests_2/common/**.

A test checks the architecturally required behaviour, so on a fixed RTL it
prints its pass line. On a buggy RTL the failing check lines are mapped to
the KUDU id they reproduce. The runner then compares that bug's status in the
bug logs with the result, so a test of an open bug is an expected failure
(XFAIL), not a regression.

## 1. Running the tests

```
cd sim/tests_2/rtl_bug_csr_rmw
./run.py                                   # one test, compiles a fresh stock build
./run.py --build <stock build dir>         # reuse an existing stock build
../common/run_all.py --build <stock build dir>                  # every test
../common/run_all.py --tests rtl_bug_csr_rmw,rtl_bug_irq_withdraw
../common/run_all.py --list                # runs that would be executed
```

**run.py** and **run_all.py** work from any directory and take the same options:

| Option | Meaning |
|---|---|
| **--build DIR** | Existing stock build (simv and simv32 from **./vcscomp -nowave -outdir=DIR**, run in **sim/run**) used by every test that runs on the stock testbench. Without it the runner compiles one into the work directory. Shadow-testbench and **--conf** builds are always compiled. |
| **--work DIR** | New output directory. It must not exist. Default: a fresh **/home/scratch/fortress/$USER/kudu_temp/tests_2_&lt;timestamp&gt;** (the root can be changed with **$KUDU_SCRATCH**). |
| **--conf 0-3** | Pipeline configuration of the stock build (default 1). A test that fixes its own configuration (rtl_bug_ra_pred_conf2) ignores it. |
| **--only REGEX** | Run only the runs whose label **&lt;test&gt;.&lt;variant&gt;** matches. |
| **--jobs N** | Number of farm batches (default 10). |
| **--keep_traces** | Keep trace_kudu_core.log / rvfi_kudu_core.log of passing runs (deleted by default to save space). |
| **--list** | Print the runs and exit. |
| **--tests a,b** | (run_all.py only) Comma-separated test directory names; default all. |

Flow:

1. Every RTL build is compiled with **submit -i ./vcscomp -nowave -outdir=...**,
   from **sim/run** for the stock testbench, or from a shadow tree for tests
   that patch the testbench or bind a checker. Tests with the same patches
   share one shadow build.
2. Test programs are built locally into the work directory by
   **common/build_prog.sh**. Nothing is written to **sim/run/bin**,
   **sim/tests/work** or anywhere else in the repository.
3. Simulations are packed into at most **--jobs** batches of similar estimated
   run time. Each batch is one **submit -i** job, and all batches run
   concurrently.
4. A run's verdict comes from its sim.log, plus the output of the test's
   post-processing hook if it has one.

Work-directory layout: **builds/** (stock or shadow builds), **programs/&lt;test&gt;.&lt;flavour&gt;/**
(.elf, .vhx, .dis, build.log), **batches/** (batch scripts and farm logs),
**runs/&lt;test&gt;.&lt;variant&gt;/** (sim.log, sim.exit, post-hook output, traces of
failing runs) and **results.txt** (one verdict line per run).

### 1.1 Verdicts and exit status

| Verdict | Meaning |
|---|---|
| **PASS** | The test's pass line was printed and no check failed. |
| **XFAIL** | Every failing check maps to a bug listed as **Open**. The bug reproduces. |
| **DEFER** | Every failing check maps to a **Deferred** or **Waived** bug, or to a waived Sail divergence. |
| **FAIL** | Anything else: wrong result, timeout, crash, an unmapped failing line, or a failing check of a bug listed as **Fixed** (a regression). |

Bug status is read from the summary tables of the three bug logs, so updating a
bug's status there changes the expected verdict without touching the test.
Exit status: 0 when every run passes, 1 when the only failures are XFAIL/DEFER,
2 otherwise.

### 1.2 Relation to the full regression

**sim/run/run_full_regression.py --suite bug** loads the tests from
**sim/tests_2** and runs every one that needs only the stock testbench and a
test program, together with **sim/tests/step_exec**. These are the tests marked
**regr** in the index below. Shadow-testbench, block-level, script and
post-processed tests run only through **run.py** / **run_all.py**.

## 2. Harness and directory layout

| Path | Contents |
|---|---|
| **common/kudu_test.py** | Runner: test description classes, builds, batching, verdicts. |
| **common/run_all.py** | Runs every test (or **--tests**) in one work directory. |
| **common/build_prog.sh** | Builds one program: **build_prog.sh &lt;flavour&gt;[+DEF=V...] &lt;src dir&gt; &lt;out dir&gt;**. |
| **common/csrc_cheri**, **common/csrc_rv32**, **common/link_*.ld** | Startup code, libraries and linker scripts (copies of the ones in **sim/tests**). |
| **common/patches/collide_sched.patch** | Collide testbench: event scheduler for interrupt and debug-request pulses plus the COLMON issuer monitor. |
| **common/colmon.py** | Post hook that turns COLMON errors into FAIL lines. |

Program flavours of **build_prog.sh** (the program name is the test directory name):

| Flavour | Build |
|---|---|
| **cheri** | CHERIoT clang (-mcpu=cheriot), like **sim/scripts/build_test.sh** |
| **rv32** | riscv-gnu gcc, like **sim/scripts/build_test_rv32.sh** |
| **dbg** | CHERIoT clang with the debug-test options, like **sim/scripts/build_dbg_test.sh** |
| **asm** | Bare assembly **test.S** with gcc -march=rv32imac_zicsr -nostdlib |

A **+DEF=V** suffix adds a preprocessor define (e.g. **cheri+AMO_SWEEP=2**).
A test-local **link_test.ld** overrides the common one. If the directory holds
**debug_rom.S**, it is built as **debug_rom.vhx** for **+DBGROM=debug_rom**.

A **run.py** declares one **Test**:

```
TEST = Test("rtl_bug_x", ["KUDU-0xx"],
            [Run("default", "simv", "cheri", ["+PMODE=1"]), ...],   # runs
            r"^X PASS",                                              # pass regex
            [(r"^FAIL x ", "KUDU-0xx")],                             # check -> bug
            shadow=Shadow(patches=[...], extra=[...]),               # optional
            conf=None, post=None)                                    # optional
sys.exit(main([TEST]))
```

**Run(variant, simv, flavour, plusargs, script=None, est=5)**: **simv** is
**simv** or **simv32**. **+TEST=&lt;test&gt;** and **+ntb_random_seed=1** are added
unless the plusargs set them. A **script** run executes a script from the test
directory instead of a simulation (block-level testbenches, lint and flow
checks). **est** is the expected CPU time in seconds, used for batching.
**Shadow** copies **rtl/** and **sim/tb/**, applies the patches and appends the
extra checker files to the file lists. **post(run_dir)** is a Python hook that
checks traces or logs after the simulation and prints its own PASS/FAIL lines.

To add a test, create **sim/tests_2/rtl_bug_&lt;name&gt;/** with the sources and a
**run.py** following an existing one. Start its docstring with the title and
the reproduced bug(s), and end it with an "Expected on HEAD" line. Then add it
to this document.

## 3. Test index

Build: **stock** = stock testbench (**--build** can be reused); **shadow** =
patched testbench or bound checker compiled by the runner; **script** = the
test compiles or lints its own design. **regr** = also run by
**run_full_regression.py --suite bug**. Expected verdicts are for HEAD at the
time of writing; the authoritative status is in the bug logs.

| Test | Bugs | Runs | Build | Expected |
|---|---|---|---|---|
| rtl_bug_csr_rmw | 001 | 4 | stock, regr | PASS |
| rtl_bug_store_access_fault | 002 | 1 | script (LSU block TB) | PASS |
| rtl_bug_wfi_debug_halt_blk | 003 | 1 | script (issuer block TB) | PASS |
| rtl_bug_issuer_debug | 003, 026–030 | 2 | stock, regr | PASS |
| rtl_bug_trap_csr_values | 004, 005 | 1 | stock, regr | PASS |
| rtl_bug_rtype_rev8_reserved | 006 | 1 | stock, regr | PASS |
| rtl_bug_misaligned_amo | 007 | 2 | stock, regr | PASS |
| rtl_bug_amo_access_fault | 008 | 2 | stock, regr | PASS |
| rtl_bug_trvk_boundary | 009 | 1 | stock, regr | PASS |
| rtl_bug_mret_asr_mtval | 010 | 1 | stock, regr | PASS |
| rtl_bug_jal_pdt_off | 011 | 1 | stock, regr | PASS |
| rtl_bug_debug_irq_not_ignored | 012 | 1 | stock, regr | PASS |
| rtl_bug_fetch_slot1_err | 013 | 4 | stock, regr | PASS |
| rtl_bug_alt_err | 013 | 4 | stock, regr | PASS |
| rtl_bug_fetch_straddle_layouts | 013 | 4 | stock, regr | PASS |
| rtl_bug_sc_forwarding | 014 | 3 | stock, regr | PASS |
| rtl_bug_cap_misaligned_mtval | 015 | 2 | stock, regr | PASS |
| rtl_bug_mshwm_csr_store_order | 016 | 2 | stock, regr | PASS |
| rtl_bug_csr_asr_allowlist | 017, 018 | 2 | stock, regr | PASS |
| rtl_bug_minstret_write_order | 019 | 2 | stock, regr | XFAIL (019 Open) |
| rtl_bug_misa_value | 020 | 3 | stock, regr | PASS |
| rtl_bug_debug_mode | 021–025 | 2 | stock, regr | PASS |
| rtl_bug_misaligned_sc_rv32 | 031 | 4 | stock, regr | PASS |
| rtl_bug_amo_cheri_fault | 032, 036 | 2 | stock, regr | PASS |
| rtl_bug_dcache_split_store | 033 | 6 | stock, regr | PASS |
| rtl_bug_umode_priv | 034, 038 | 4 | stock, regr | PASS |
| rtl_bug_debug_ecall | 035 | 2 | stock, regr | PASS |
| rtl_bug_sc_mshwm | 037 | 2 | stock, regr | PASS |
| rtl_bug_jalr_odd_epc | 039 | 4 | stock, regr | PASS |
| rtl_bug_halt_step_cause | 040 | 2 | stock, regr | PASS |
| rtl_bug_csr_mtval_mstatush | 041, 042, 043 | 5 | stock, regr | XFAIL (042 Open; 043 Deferred) |
| rtl_bug_alt_tag_x | 044 | 3 | shadow (alt_chk.sv) | PASS |
| rtl_bug_ra_pred_conf2 | 048 | 3 | shadow, conf2 (ra_chk.sv) | PASS |
| rtl_bug_ra_reset_range | 049 | 3 | shadow (ra_rst_chk.sv) | PASS |
| rtl_bug_dcache_stale_fwd_rv32 | 050 | 4 | stock, regr | PASS |
| rtl_bug_dcache_stale_fwd_cheri | 050 | 2 | stock, regr | PASS |
| rtl_bug_lrsc_load_barrier | 051 | 2 | stock, regr | PASS |
| rtl_bug_split_mtval_rv32 | 052 | 4 | stock, regr | PASS |
| rtl_bug_split_mtval_cheri | 052 | 3 | stock, regr | PASS |
| rtl_bug_split_store_err | 052 | 4 | stock, regr | PASS |
| rtl_bug_mult_latch_lint | 053 | 1 | script (Verilator lint) | PASS |
| rtl_bug_tracer_amo | 055, 057 | 4 | stock, post hook | PASS |
| rtl_bug_tracer_clc_irq | 056 | 2 | stock, post hook | PASS |
| rtl_bug_tracer_cebreak | 058 | 3 | stock, post hook | PASS |
| rtl_bug_amo_sd_perm | 061 | 2 | stock, regr | PASS |
| rtl_bug_mepcc_high_exp | 062 | 1 | stock, post hook | DEFER (062 Waived) |
| rtl_bug_failed_sc_tag | 063, 061 | 4 | stock, post hook | DEFER (063 Deferred) |
| rtl_bug_tracer_disasm | 057, 058, 064–068 | 1 | script (tracer TB) | PASS |
| rtl_bug_vcscomp_trace_dpi | 069 | 1 | script (fake vcs) | PASS |
| rtl_bug_fetch_err_pcc_top | 070 | 13 | stock, regr | PASS (070 Fixed) |
| rtl_bug_step_ebreak_cause | 071 | 3 | stock, regr | PASS (071 Fixed) |
| rtl_bug_irq_withdraw | 072 | 2 | shadow (collide TB), post hook | DEFER (072 Waived) |
| rtl_bug_dbg_req_withdraw | 073 | 2 | shadow (collide TB), post hook | DEFER (073 Waived) |
| rtl_bug_rvfi_intr_stale_pc | 074 | 2 | shadow (RVFI dump), post hook | PASS (074 Fixed) |
| rtl_bug_ra_pred_odd_epc | 075 | 6 | stock, regr | PASS (075 Fixed) |
| rtl_bug_csr_stale_bus_err | 076 | 4 | stock, regr | PASS (076 Fixed) |
| rtl_bug_depcc_odd | 077 | 4 | stock, regr | PASS (077 Fixed) |
| rtl_bug_sail_zbkb_zbkx_missing | Sail divergence | 1 | stock | DEFER (waived) |
| rtl_bug_trigger_csr_sail | Sail divergence | 1 | stock | DEFER (waived) |

Common run variants: **rv32** = rv32 program on simv32; **cheriot** /
**pmode0** = the same program on simv with **+PMODE=0**; **pmode1** / cheri
program = simv with **+PMODE=1**; **delayed** = random instruction and/or data
bus wait states (**+INSTR_GNT_WMAX**, **+INSTR_RESP_WMAX**, **+DATA_GNT_WMAX**,
**+DATA_RESP_WMAX**); **irq** = random interrupts (**+INTR_RATE**). The exact
plusargs of every run are in its **run.py** (or **--list**).

## 4. Test descriptions

The **run.py** docstring of each test gives the full details: cases, expected
output lines and the pre-fix symptom.

### 4.1 CSR, trap and privilege

- **rtl_bug_csr_rmw** (KUDU-001): csrrs/csrrc/csrrsi/csrrci on MTVEC and MEPC
  must update only the selected bits.
- **rtl_bug_trap_csr_values** (KUDU-004, 005): DRET outside debug mode must
  raise an illegal-instruction trap (not a CHERI fault); ECALL must write
  mtval = 0.
- **rtl_bug_rtype_rev8_reserved** (KUDU-006): reserved R-type encodings near
  rev8 must be illegal.
- **rtl_bug_mret_asr_mtval** (KUDU-010): MRET without PCC.ASR must report the
  ASR-violation CHERI mtval.
- **rtl_bug_csr_asr_allowlist** (KUDU-017, 018): counter CSR writes need
  PCC.ASR; an unimplemented CSR without ASR must be an illegal instruction, not
  a CHERI fault.
- **rtl_bug_minstret_write_order** (KUDU-019, Open): minstret must increment
  as instructions retire (its retire inputs are tied to 0 on HEAD).
- **rtl_bug_misa_value** (KUDU-020): misa must read back the implemented
  extensions only, on rv32, PMODE=0 and PMODE=1.
- **rtl_bug_umode_priv** (KUDU-034, 038): MRET and WFI must trap in U-mode;
  M-mode interrupts must be taken in U-mode even with mstatus.MIE = 0.
- **rtl_bug_csr_mtval_mstatush** (KUDU-041, 042 Open, 043 Deferred): illegal
  CSR accesses must report the instruction in mtval; mstatush must exist;
  CDBG_CTRL must take effect.
- **rtl_bug_csr_stale_bus_err** (KUDU-076, Fixed): an illegal CSR access after
  a misaligned load/store whose first half took a bus error (address
  0x7ffffffd) must trap with mcause 2 and mtval = instruction. The trap handler
  makes no memory access, so it cannot clear the stale error. Cases C1–C3
  (lw, sw, then csrr; lw, then csrw mvendorid) fail on HEAD with mcause 7 and
  mtval 0x7ffffffd. C0 (CSR only) and C4 (a good lw in between) are controls
  that pass on HEAD. Runs: simv32 and simv (PMODE=0), each with and without
  data wait states.

### 4.2 Debug and single step

- **rtl_bug_issuer_debug** (KUDU-003, 026–030): halt requests during WFI and
  with an empty IR, dpc/MEPC on debug entry, stepping trapping instructions,
  interrupts while stepping, stepped ebreak cause.
- **rtl_bug_wfi_debug_halt_blk** (KUDU-003): block-level TB of the real
  ir_decoder and issuer; a debug halt request must wake a core sleeping in WFI
  with no interrupt pending.
- **rtl_bug_debug_irq_not_ignored** (KUDU-012): interrupts must not be taken in
  debug mode.
- **rtl_bug_debug_mode** (KUDU-021–025): ebreak re-entry, exceptions, illegal
  CSRs, CLC permission stripping and dpc/dscratch writes in debug mode.
- **rtl_bug_debug_ecall** (KUDU-035): ECALL in debug mode must not go to mtvec.
- **rtl_bug_halt_step_cause** (KUDU-040): a halt request during a single step
  must report cause HALTREQ.
- **rtl_bug_step_ebreak_cause** (KUDU-071, Fixed): a completed step whose next
  instruction is an ebreak (case 33) or an execute-trigger match (case 34) must
  halt with dcsr.cause = STEP first, then EBREAK/TRIGGER on the next resume.
  Uses its own register-transparent debug ROM that logs every debug entry. Runs
  on simv32, simv PMODE=0 and simv PMODE=1.
- **rtl_bug_dbg_req_withdraw** (KUDU-073, Waived): on the collide testbench, a
  debug_req pulse of 1–4 cycles fired 1–12 cycles after an arming store
  (48 combinations). Any halt taken must report cause HALTREQ; on HEAD every
  2-cycle pulse halts with dcsr.cause = 0. Waived: debug_req must stay
  asserted until the hart halts (integration requirement INT-2,
  [integration_issues.md](integration_issues.md)).
- **rtl_bug_depcc_odd** (KUDU-077, Fixed): on the first random debug entry
  after the test sets up its mailbox, the debug ROM writes DEPCC (dpc in
  RV32) with the saved address | 1, reads it back and restores the original
  before dret. R1: the read-back value must have bit 0 clear. R2 (control):
  the check ran and the rest of the address was kept. The CHERIoT runs (simv
  PMODE=1, with and without wait states) fail R1 on HEAD; the RV32 runs
  (simv32, simv PMODE=0) are controls that pass.

### 4.3 Interrupts

- **rtl_bug_irq_withdraw** (KUDU-072, Waived): on the collide testbench, a pulse
  of 1–4 cycles on fast interrupt 0 fired 1–12 cycles after an arming store
  (48 combinations). Every interrupt taken must report mcause 0x80000010; on
  HEAD pulses that drop between the issuer's decision and the trap are taken
  with mcause 0x80000007 (machine timer). Waived: interrupt lines must stay
  asserted until acknowledged (integration requirement INT-1,
  [integration_issues.md](integration_issues.md)).

### 4.4 Fetch, branch prediction and ALT

- **rtl_bug_jal_pdt_off** (KUDU-011): JAL must redirect with the branch
  predictor disabled.
- **rtl_bug_fetch_slot1_err**, **rtl_bug_alt_err** (KUDU-013): a fetch bus
  error on the second (slot-1) fetch word must be precise and must not be lost,
  with and without ALT.
- **rtl_bug_fetch_straddle_layouts** (KUDU-013): a 32-bit instruction
  straddling into an errored fetch word, in 8 code layouts and many entry
  points (94 tries), must trap with mcause 1, mepc = pc and mtval = pc + 2.
- **rtl_bug_jalr_odd_epc** (KUDU-039): a JALR to an odd target must not leave
  an odd mepc/dpc.
- **rtl_bug_alt_tag_x** (KUDU-044): with the predictor off, the ALT tag fields
  and the ALT cancel/apply controls must never be X. A checker bound into
  fetch_fifo64 counts X cycles during a 32 KB cpuctrl-toggling stress program.
- **rtl_bug_ra_pred_conf2** (KUDU-048): on pipeline configuration 2 the
  RA-prediction outputs of ir_stage must not be X while 6000 cret returns to an
  odd sealed sentry run, with and without interrupts (checker ra_chk.sv).
- **rtl_bug_ra_reset_range** (KUDU-049): a return predicted right after reset
  (and with x1 out of the RA range) must not fetch from unpopulated memory
  (checker ra_rst_chk.sv).
- **rtl_bug_fetch_err_pcc_top** (KUDU-070, Fixed): 54 PCC fetch-bounds cases.
  A fetch bus error on an in-bounds parcel near the PCC top must be an
  instruction access fault (mcause 1, MEPCC tagged, mtval = errored parcel);
  an errored word at or after the top must still give the PCC bounds fault.
  Runs: noerr (bounds faults without bus errors); err1/err5/err9/err37/err38
  (access fault: 32-bit and 16-bit at T-2, second parcel of a 32-bit at T-4
  with mtval pc+2, direct entry at T-2); bnd0/bnd37 (32-bit at T-2 whose
  second parcel's word errors) and bnd32/34/35/36/39 (jal, branch, cjr, cjal
  and direct entry to an errored word at T..T+4). HEAD failed err1 and err37.
- **rtl_bug_ra_pred_odd_epc** (KUDU-075, Fixed): 4000 iterations of a return
  through an ra (cra sentry in CHERIoT) whose address is target + 1, under
  random interrupts (R1, mepc) or random debug requests (R2, dpc), with
  instruction and data wait states 0–3. Every saved mepc/dpc must be even.
  The handler and the debug ROM count odd values and clear bit 0 before
  returning. R3 checks the iteration count, no synchronous exceptions and at
  least 50 interrupt or debug entries. Runs: simv32, simv PMODE=0 and simv
  PMODE=1, each with interrupts and with debug requests; all failed R1/R2
  before the fix and pass after it. rtl_bug_jalr_odd_epc (KUDU-039) covers the computed jalr target only,
  and rtl_bug_ra_pred_conf2 runs conf2, which has no RA prediction.

### 4.5 Load/store unit, atomics and data cache

- **rtl_bug_store_access_fault** (KUDU-002): block-level TB of the real
  load_store_unit; a store bus error must report mcause 7 (not 5), with
  immediate and delayed grant/response.
- **rtl_bug_misaligned_amo** (KUDU-007): misaligned AMO and SC must trap.
- **rtl_bug_amo_access_fault** (KUDU-008): an AMO bus error must report a
  store/AMO access fault.
- **rtl_bug_sc_forwarding** (KUDU-014): a failed SC must not forward its store
  data to later loads.
- **rtl_bug_misaligned_sc_rv32** (KUDU-031): misaligned LR/SC/AMO must not reach
  the bus on the RV32 build.
- **rtl_bug_amo_cheri_fault** (KUDU-032, 036): a trapping AMO must not
  overwrite rd and must save mstatus.MPIE correctly.
- **rtl_bug_dcache_split_store** (KUDU-033): a load after a store spanning two
  words must not return stale data.
- **rtl_bug_dcache_stale_fwd_rv32**, **rtl_bug_dcache_stale_fwd_cheri**
  (KUDU-050): 48 / 60 generated cases. After a misaligned or capability store
  that writes word A+4 of a cached line, a load of A+4 and the value forwarded
  to the next instruction must both be the new data.
- **rtl_bug_split_mtval_rv32**, **rtl_bug_split_mtval_cheri** (KUDU-052):
  misaligned loads and stores straddling the end of DRAM. A bus error on the
  second half must report mtval = 0x80080000 or the original address, under
  random wait states.
- **rtl_bug_split_store_err** (KUDU-052): split accesses where exactly one half
  is unmapped. Checks mcause, mtval and rd, and that the mapped half is
  untouched or holds exactly the non-faulting bytes.

### 4.6 CHERIoT capabilities, MSHWM and revocation

- **rtl_bug_trvk_boundary** (KUDU-009): the load-barrier revocation-map (TSMAP)
  range check must not be off by one at its upper boundary.
- **rtl_bug_cap_misaligned_mtval** (KUDU-015): misaligned capability accesses
  must report the current mtval.
- **rtl_bug_mshwm_csr_store_order** (KUDU-016): a store after an MSHWM CSR
  write must be checked against the new value.
- **rtl_bug_sc_mshwm** (KUDU-037): a successful SC.W must update MSHWM.
- **rtl_bug_lrsc_load_barrier** (KUDU-051): LR.W/SC.W (and clw/csw/amoadd) on a
  revoked capability loaded by CLC 0/2/4/8 instructions earlier must take the
  tag violation.
- **rtl_bug_amo_sd_perm** (KUDU-061): an AMO through a capability without SD
  must report the SD violation (mcause 0x1c, mtval 0xb3) before bounds or
  alignment faults, and leave rd, memory and tag unchanged.
- **rtl_bug_mepcc_high_exp** (KUDU-062, Waived): 186 trapping PCCs with many
  exponents and bounds encodings; the post hook compares cgethigh(MEPCC) with
  the embedded Sail values. On HEAD the 39 cases with exponent >= 24 differ
  (always untagged, malformed capabilities).
- **rtl_bug_failed_sc_tag** (KUDU-063 Deferred, 061): two generated LR/SC/AMO
  sweeps through capabilities (330 and 270 cases), checked by a reference model
  of the Sail checks. On HEAD the testbench memory model clears the tag on a
  failed SC.W (KUDU-063); about 4 minutes per run.

### 4.7 Tracer and RVFI

- **rtl_bug_tracer_amo** (KUDU-055, 057): random AMO/LR/SC stream; the trace
  must name every AMO correctly (amoand.w not INVALID) and report its rd write
  and load value. Checked by replaying a shadow register file.
- **rtl_bug_tracer_clc_irq** (KUDU-056): random CLC/CSC stream under
  interrupts; after an interrupt that displaces a CLC, every traced CLC must
  carry its own tag result, and the tracer FIFO must not overflow.
- **rtl_bug_tracer_cebreak** (KUDU-058): every c.ebreak trace line must carry
  its PC and encoding.
- **rtl_bug_tracer_disasm** (KUDU-064–068, plus 057 and 058): standalone TB
  that feeds directed encodings from the bug reports and an exhaustive or
  random encoding sweep to both the SV and the DPI-C tracer formatters, and
  compares them with each other and with golden text. No -trace_dpi core build
  is needed.
- **rtl_bug_rvfi_intr_stale_pc** (KUDU-074, Fixed): random CHERIoT load/store
  stream under random interrupts, with and without bus errors, on a build with
  the RVFI dump enabled. The pc of every interrupt RVFI record must equal the
  mepc its handler returns to; before the rtl/tracer.sv fix many records
  carried a stale pc. Only pc_rdata is checked; insn, pc_wdata and the mem
  masks of an interrupt record are don't-care.

### 4.8 Build flow and lint

- **rtl_bug_mult_latch_lint** (KUDU-053): Verilator -Wall lint of
  mult_pipeline.sv must report no LATCH; a deliberate-latch control module must.
- **rtl_bug_vcscomp_trace_dpi** (KUDU-069): **sim/run/vcscomp** is run with a
  fake vcs over 6 flag combinations; every flag must reach both vcs calls with
  the right defines, file list, coverage arguments and output directory.

### 4.9 Sail divergences (not KUDU bugs)

- **rtl_bug_sail_zbkb_zbkx_missing**: Zbkb/Zbkx encodings trap as illegal on
  Kudu (which implements B, not scalar crypto) but are legal in Sail.
- **rtl_bug_trigger_csr_sail**: Kudu implements the Debug-spec trigger CSRs;
  Sail reads tselect as all ones.

Both always report DEFER. To compare with Sail, run the built ELF
(**programs/&lt;test&gt;.&lt;flavour&gt;/&lt;test&gt;.elf** in the work directory) on the
Sail emulator.

## 5. Bugs without a runnable test

| Bug | Status | Why there is no test |
|---|---|---|
| KUDU-045 | Deferred | alt_err_event is computed but unused; found by code review, has no observable effect. |
| KUDU-046 | Fixed | flush_alt / apply_cause had no default with AltEnable = 0 (conf2); a lint (latch/X) issue found by code review. |
| KUDU-047 | Fixed | alt_seq is never driven or used; code review (dead code). |
| KUDU-054 | Fixed | ALT save path drops the align64 bit; found by VCS lint, no simulation symptom. |
| KUDU-059 | Fixed | +CAP_ERR_RATE was parsed but drove nothing; a testbench issue found by code review, not RTL. |
| KUDU-060 | Not a bug | CLC revocation lookup can observe a younger bitmap store; accepted CHERIoT behaviour. |

## 6. Results on HEAD

Verified on the stock conf1 build of HEAD (c708e3c):

| Flow | Runs | PASS | XFAIL | DEFER | FAIL |
|---|---|---|---|---|---|
| **sim/tests_2/common/run_all.py** (all tests) | 138 | 114 | 17 | 7 | 0 |
| **run_full_regression.py --suite bug** (regr tests plus step_exec) | 104 | 93 | 11 | 0 | 0 |

XFAIL runs: KUDU-019 (2), 042 (5), 070 (1), 071 (3), 072 (2), 073 (2) and 074 (2).
DEFER runs: KUDU-062 (1), 063 (4) and the two Sail divergences.

KUDU-074 has since been fixed in **rtl/tracer.sv**; with that change both
rtl_bug_rvfi_intr_stale_pc runs PASS, so the expected totals become 116 PASS
and 15 XFAIL for run_all. The test is not in the bug regression, so that row
is unchanged.

KUDU-072 and KUDU-073 have since been waived. Their four runs move from XFAIL
to DEFER, so the expected run_all totals become 116 PASS, 11 XFAIL and 11
DEFER. Neither test is in the bug regression.

rtl_bug_ra_pred_odd_epc (KUDU-075, 6 runs) and rtl_bug_csr_stale_bus_err
(KUDU-076, 4 runs) were added later, after the FPV of the fcov SVAs found
both bugs. All 10 runs are XFAIL on HEAD, so the expected run_all totals
become 148 runs: 116 PASS, 21 XFAIL and 11 DEFER. Both tests are in the bug
regression, which grows by the same 10 XFAIL runs.

KUDU-075 was then fixed (2026-11-15). Its 6 runs move from XFAIL to PASS
(verified: 122 PASS, 15 XFAIL, 11 DEFER, 0 FAIL on conf1). The FPV run on
the fixed RTL found KUDU-077, and rtl_bug_depcc_odd (4 runs: 2 XFAIL, 2 PASS)
was added. The expected run_all totals are now 152 runs: 124 PASS, 17 XFAIL
and 11 DEFER. The bug regression grows by the same 4 runs.

KUDU-077 was then fixed (2026-11-15). Its 2 XFAIL runs move to PASS
(verified: 126 PASS, 15 XFAIL, 11 DEFER, 0 FAIL on conf1), so the expected
run_all totals are now 152 runs: 126 PASS, 15 XFAIL and 11 DEFER.

KUDU-070, KUDU-071 and KUDU-076 were then fixed (2026-11-15).
rtl_bug_fetch_err_pcc_top was extended from 3 to 13 runs (KUDU-070 corner
cases: second-parcel errors, direct entry at T-2, errored words at or after
the PCC top). The 1 KUDU-070, 3 KUDU-071 and 4 KUDU-076 XFAIL runs move to
PASS (verified: 144 PASS, 7 XFAIL, 11 DEFER, 0 FAIL on conf1), so the
expected run_all totals are now 162 runs: 144 PASS, 7 XFAIL and 11 DEFER.
The bug regression grows by the same 10 runs (verified: 310 PASS, 7 XFAIL).
