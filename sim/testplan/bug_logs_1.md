# CHERIoT-Kudu RTL bug log

Bugs found by RTL review between **2026-10-12** and **2026-10-26**. Each was
confirmed against the RISC-V/CHERIoT specifications (and cheriot-ibex where
relevant) and demonstrated by a reproducer that fails on the affected RTL.

From KUDU-010 onwards the authoritative reference is the CHERIoT Sail model
(github.com/CHERIoT-Platform/cheriot-sail, branch `dii-read-from-file`, commit
`1765879`); cheriot-ibex is secondary evidence. Sail file references are
relative to that repository (`src/` = CHERIoT, `sail-riscv/model/` = base).
The Sail model runs only in CHERIoT mode, so PMODE=0 behaviour is judged
against the base `sail-riscv/model/` sources.

## Summary

| ID | Status | Area | Location | Summary | Reproducer |
|---|---|---|---|---|---|
| KUDU-001 | **Fixed** (`dd4543c`) | CSR | `rtl/cs_registers.sv` | MTVEC/MEPC CSRRS/CSRRC use raw operand instead of merged value | `sim/tests_2/rtl_bug_csr_rmw/` |
| KUDU-002 | **Fixed** (`cd63cce`) | LSU | `rtl/load_store_unit.sv` | Store bus error reports load access fault | local TB (/home/scratch/fortress/kunyanliu/kudu_temp) |
| KUDU-003 | **Fixed** (`802d481`) | Issue/debug | `rtl/issuer.sv:597-600` | WFI sleep is not woken by a debug halt request, and a stepped WFI hangs | local TB (/home/scratch/fortress/kunyanliu/kudu_temp); `sim/tests_2/rtl_bug_issuer_debug/` (I5) |
| KUDU-004 | **Fixed** (`46179c1`) | Trap | `rtl/issuer.sv:783, 973-974` | DRET outside debug mode raises CHERI fault, not illegal instruction | `sim/tests_2/rtl_bug_trap_csr_values/` |
| KUDU-005 | **Fixed** (`46179c1`) | Trap | `rtl/issuer.sv:1004` | ECALL writes mtval = PC instead of 0 | `sim/tests_2/rtl_bug_trap_csr_values/` |
| KUDU-006 | **Fixed** (`c32075d`) | Decode | `rtl/ir_decoder.sv:397-400` (removed) | Reserved R-type encoding accepted as `rev8` | `sim/tests_2/rtl_bug_rtype_rev8_reserved/` |
| KUDU-007 | **Fixed** (`7028fb3`) | Atomics | `rtl/load_store_unit.sv:357-359`, `rtl/cmplx_unit.sv` | Misaligned AMO/SC do not trap; AMO split non-atomically | `sim/tests_2/rtl_bug_misaligned_amo/` |
| KUDU-008 | **Fixed** (`7028fb3`) | Atomics | `rtl/cmplx_unit.sv:162` | AMO bus error reports load access fault | `sim/tests_2/rtl_bug_amo_access_fault/` |
| KUDU-009 | **Fixed** (`d687956`) | CHERI load barrier | `rtl/cheri_trvk_stage.sv:50` | TSMAP range check off by one (`<=`) | `sim/tests_2/rtl_bug_trvk_boundary/` |
| KUDU-010 | **Fixed** (`c32075d`) | CHERI trap | `rtl/ir_decoder.sv:89,579`, `rtl/issuer.sv:978-980` | MRET without PCC.ASR reports tag violation mtval, not ASR violation | `sim/tests_2/rtl_bug_mret_asr_mtval/` |
| KUDU-011 | **Fixed** (`6378440`) | Branch | `rtl/branch_unit.sv:88` | JAL does not redirect when the branch predictor is disabled | `sim/tests_2/rtl_bug_jal_pdt_off/` |
| KUDU-012 | **Fixed** (`0e68d2e`) | Issue/debug | `rtl/issuer.sv:726` | Interrupts are taken while in debug mode | `sim/tests_2/rtl_bug_debug_irq_not_ignored/` |
| KUDU-013 | **Fixed** (`e79286b`) | Fetch/trap | `rtl/fetch_fifo64.sv:241-252`, `rtl/issuer.sv:966-968` | Fetch bus error on the second fetch word: a straddling instruction reports mtval = PC, not PC+2; a slot-1 instruction in that word gets no fault at all and retires the error data; also reached through an ALT (fall-through) restore | local TB (/home/scratch/fortress/kunyanliu/kudu_temp); `sim/tests_2/rtl_bug_fetch_slot1_err/` (slot 1); `sim/tests_2/rtl_bug_alt_err/` (slot 1 via ALT) |
| KUDU-014 | **Fixed** (`991dba4`) | LSU/forwarding | `rtl/dcache.sv:133-139,163-184` | Failed SC forwards its uncommitted store data to consumers of a following load | `sim/tests_2/rtl_bug_sc_forwarding/` |
| KUDU-015 | **Fixed** (`85bbd3f`) | CHERI LSU/trap | `rtl/load_store_unit.sv:372,397-399,628-630` | Misaligned CLC/CSC (and, since `7028fb3`, misaligned LR/SC/AMO) report a previous access's address in mtval | `sim/tests_2/rtl_bug_cap_misaligned_mtval/` |
| KUDU-016 | **Fixed** (`1663deb`) | CHERI CSR/LSU | `rtl/cs_registers.sv:983-986`, `rtl/load_store_unit.sv:578` | Store issued in the cycle a `csrw mshwm/mshwmb` commits is checked against stale MSHWM/MSHWMB | `sim/tests_2/rtl_bug_mshwm_csr_store_order/` |
| KUDU-017 | **Fixed** (`0e68d2e`) | CHERI CSR | `rtl/load_store_unit.sv:588-590` | Writes to mcycle/minstret(h) are allowed without PCC.ASR | `sim/tests_2/rtl_bug_csr_asr_allowlist/` |
| KUDU-018 | **Fixed** (`85bbd3f`) | CHERI CSR/trap | `rtl/load_store_unit.sv:579,596` | Unimplemented CSR without PCC.ASR raises a CHERI fault instead of illegal instruction | `sim/tests_2/rtl_bug_csr_asr_allowlist/` |
| KUDU-019 | Open | CSR/counters | `rtl/kudu_top.sv:660-672` | minstret never increments (retire/event inputs of `cs_registers` tied to 0) | `sim/tests_2/rtl_bug_minstret_write_order/` |
| KUDU-020 | **Fixed** (`d88c674`) | CSR | `rtl/cs_registers.sv:133,148` | `RV32IEnabled = ~CHERIoTEn` is 32 bits wide, so misa bits 31:9 read as 1 (MXL=3); X differs between PMODE=0 and RV32 builds | `sim/tests_2/rtl_bug_misa_value/` |
| KUDU-021 | **Fixed** (`802d481`) | Debug | `rtl/issuer.sv:775`, `rtl/cs_registers.sv:768-773,1744-1749` | `ebreak` in debug mode overwrites dpc/dcsr.cause (ebreakm=1) or traps to mtvec (ebreakm=0) instead of halting again | `sim/tests_2/rtl_bug_debug_mode/` |
| KUDU-022 | **Fixed** (`d88c674`) | Debug/trap | `rtl/issuer.sv:807,820` | Exceptions in debug mode run the M-mode handler at mtvec (no debug exception address) | `sim/tests_2/rtl_bug_debug_mode/` |
| KUDU-023 | **Fixed** (`38d1ad3`) | Debug/CSR | `rtl/load_store_unit.sv:598` | Illegal CSR accesses do not trap in debug mode (both PMODEs) | `sim/tests_2/rtl_bug_debug_mode/` |
| KUDU-024 | **Fixed** (`d88c674`) | Debug/CHERI LSU | `rtl/ls_pipeline.sv:217` | CLC skips load-permission stripping (MC/LM/LG) in debug mode | `sim/tests_2/rtl_bug_debug_mode/` |
| KUDU-025 | **Fixed** (`38d1ad3`) | Debug/CHERI CSR | `rtl/cs_registers.sv:1651,1755,1766` | At PMODE=1, `csrw dpc/dscratch0/dscratch1` is silently dropped (no write, no trap) | `sim/tests_2/rtl_bug_debug_mode/` |
| KUDU-026 | **Fixed** (`802d481`) | Issue/debug | `rtl/issuer.sv:727,943` | Halt request while the IR is empty (after a redirect) saves a stale dpc; `dret` resumes on the wrong path | `sim/tests_2/rtl_bug_issuer_debug/` |
| KUDU-027 | **Fixed** (`802d481`) | Debug/CSR | `rtl/cs_registers.sv:1674,1677` | Every debug-mode entry overwrites MEPC/MEPCC with the dpc | `sim/tests_2/rtl_bug_issuer_debug/` |
| KUDU-028 | **Fixed** (`d290cd0`) | Debug/step | `rtl/issuer.sv:898` | Stepping an instruction that traps at decode runs the handler's first instruction before halting | `sim/tests_2/rtl_bug_issuer_debug/` |
| KUDU-029 | **Fixed** (`d290cd0`) | Debug/step | `rtl/issuer.sv:726` | Interrupts are taken while single-stepping although `dcsr.stepie` is hardwired to 0 | `sim/tests_2/rtl_bug_issuer_debug/` |
| KUDU-030 | **Fixed** (`d290cd0`) | Debug | `rtl/issuer.sv:945-952` | Stepped `ebreak` with `ebreakm=1` reports `dcsr.cause` STEP instead of EBREAK | `sim/tests_2/rtl_bug_issuer_debug/` |
| KUDU-031 | **Fixed** (`85bbd3f`) | Atomics (RV32 build) | `rtl/lsu_if.sv:66-74` | On the RV32-only build, misaligned LR/SC/AMO are not blocked before the bus; a misaligned SC writes memory and a trapping LR still sets the reservation | `sim/tests_2/rtl_bug_misaligned_sc_rv32/` |
| KUDU-032 | **Fixed** (`1567152`) | Atomics/CHERI | `rtl/cmplx_unit.sv:162-166`, `rtl/cheri_pkg.sv:1048-1049` | AMO writes rd from its read phase before the write-phase check; an AMO with LD-only authority (or a write-phase bus error) traps with rd clobbered | `sim/tests_2/rtl_bug_amo_cheri_fault/` |
| KUDU-033 | **Fixed** (`f61f89d`, `6e157c3`) | LSU/forwarding | `rtl/dcache.sv:133-134,163,272-277` | After a store that spans two words (misaligned `sw`/`sh`, `csc`), consumers of a following load of the second word get stale data | `sim/tests_2/rtl_bug_dcache_split_store/` |
| KUDU-034 | **Fixed** (`546cc56`) | Trap/privilege | `rtl/ir_decoder.sv:443-451`, `rtl/issuer.sv:575,914`, `rtl/kudu_top.sv:634` | U-mode MRET is not illegal (privilege escalation through MPP); U-mode WFI ignores `mstatus.TW` | `sim/tests_2/rtl_bug_umode_priv/` |
| KUDU-035 | **Fixed** (`d290cd0`) | Debug/trap | `rtl/issuer.sv:834` | ECALL in debug mode jumps to mtvec instead of the debug exception address (KUDU-022 fix misses ECALL) | `sim/tests_2/rtl_bug_debug_ecall/` |
| KUDU-036 | **Fixed** (`1567152`) | Atomics/trap | `rtl/cmplx_unit.sv:161`, `rtl/ls_pipeline.sv:196`, `rtl/cs_registers.sv:782` | A trapping AMO at PMODE=1 saves `mstatus.MPIE = 0`, so `mret` returns with interrupts disabled | `sim/tests_2/rtl_bug_amo_cheri_fault/` |
| KUDU-037 | **Fixed** (`1663deb`) | CHERI CSR/LSU | `rtl/ls_pipeline.sv:258` | A successful `sc.w` never updates MSHWM | `sim/tests_2/rtl_bug_sc_mshwm/` |
| KUDU-038 | **Fixed** (`546cc56`) | Interrupt/privilege | `rtl/issuer.sv:727` | M-mode interrupts are not taken in U-mode when `mstatus.MIE = 0` | `sim/tests_2/rtl_bug_umode_priv/` |
| KUDU-039 | **Fixed** (`546cc56`) | Branch/trap | `rtl/branch_unit.sv:65-72`, `rtl/issuer.sv:875-876` | A JALR to an odd target leaves bit 0 set in the saved next PC; an interrupt then writes an odd mepc (or dpc) | `sim/tests_2/rtl_bug_jalr_odd_epc/` |
| KUDU-040 | **Fixed** (`d290cd0`) | Debug | `rtl/issuer.sv:951-954` | Halt request while `dcsr.step = 1` reports `dcsr.cause` STEP instead of HALTREQ | `sim/tests_2/rtl_bug_halt_step_cause/` |
| KUDU-041 | **Fixed** (`85bbd3f`) | CSR/trap | `rtl/load_store_unit.sv:628-630` | Illegal CSR access reports mtval = 0; every other illegal instruction (and cheriot-ibex) reports the instruction bits | `sim/tests_2/rtl_bug_csr_mtval_mstatush/` |
| KUDU-042 | Open (low) | CSR | `rtl/cs_registers.sv` | `mstatush` (0x310) is not implemented and raises illegal instruction | `sim/tests_2/rtl_bug_csr_mtval_mstatush/` |
| KUDU-043 | **Deferred** (low) | CHERI CSR | `rtl/cs_registers.sv:1029`, `rtl/kudu_top.sv:684` | CDBG_CTRL (0xBC4) is writable but `csr_dbg_tclr_fault_o` is unconnected, so it has no effect | `sim/tests_2/rtl_bug_csr_mtval_mstatush/` |
| KUDU-044 | **Fixed** (`f6dddaa`) | Fetch/ALT | `rtl/fetch_fifo64.sv:156-174`, `rtl/branch_predict.sv:309-310`, `rtl/issuer.sv:701-705` | ALT tag fields (`alt_valid`, `alt_id`, `alt_seq`) of the fetch output are never driven; with the predictor off they reach the IR stage as X and make `ex_alt_ctrl_o.cancel`/`id0`/`id1` X | review checker (/home/scratch/fortress/kunyanliu/kudu_temp) |
| KUDU-045 | **Deferred** (low) | Fetch/ALT | `rtl/fetch_fifo64.sv:459,476` | `alt_err_event` (apply of a free ALT entry) is computed but unused; no assertion | code review |
| KUDU-046 | **Fixed** (`f6dddaa`) | Issue/ALT | `rtl/issuer.sv:681-705` | `flush_alt` and `apply_cause` have no default in `always_comb` when `AltEnable = 0` (conf2): latch/X lint | code review |
| KUDU-047 | **Fixed** (`f6dddaa`) | Fetch/ALT | `rtl/super_pkg.sv:60,140`, `rtl/ir_decoder.sv:119` | `alt_seq` is declared and passed through but never driven or used | code review |
| KUDU-048 | **Fixed** (`f210f63`, `82f67d8`) | RA prediction (conf2) | `rtl/ir_stage.sv:373-421`, `rtl/kudu_cfg_pkg.sv:126` | conf2 (`IrStageBypass[1]=1`) with `PredictRA=1`: `cjalr_pcc_set_o`/`cjalr_rcap_o` undriven (X) and every CJALR return mispredicts | RA checker + `ra_odd` (/home/scratch/fortress/kunyanliu/kudu_temp) |
| KUDU-049 | **Fixed** (`8e3b20b`) | RA prediction | `rtl/ir_stage.sv:598` | `cur_ra32_q` resets to unshifted `RALimitLo` (0x00080000, not 0x80000000), so a return predicted before x1 is written fetches outside the RA limit range | RA checker + `ra_rst` (/home/scratch/fortress/kunyanliu/kudu_temp) |
| KUDU-050 | **Fixed** (`f61f89d`, `6e157c3`) | LSU / dcache forwarding | `rtl/dcache.sv:133-160` | A load that issues while a `csc` or misaligned store to the neighbouring word is still awaiting its response hits a stale line; the stale value is forwarded to a dependent instruction (the RF later gets the correct value) | `dcs_c`/`dcs_r` (/home/scratch/fortress/kunyanliu/kudu_temp) |

Line numbers refer to the RTL at the time of review.

Status is judged on the code in `rtl/`. The `802d481` fixes were checked
by building `rtl/` (a snapshot identical to `802d481`) and running the
reproducers plus `rv32_test_csr`, `isa_test_csr` and `dbg_test1`, default
and delayed memory (`/home/scratch/fortress/kunyanliu/kudu_temp/user_rtl_review_20261020_180424/runs2/`, `run2.sh`).
On `802d481`, KUDU-022..025 (`D2`, `D3`, `D4`, `P1`) and KUDU-028/030
(`I2`, `I4`) still fail, and the issuer test still hangs at `I3` (KUDU-012).
The `46179c1` fixes (KUDU-004/005) were checked on a snapshot that
differs from `46179c1` only in comments: `rtl_bug_trap_csr_values` passes
6/6 on the RV32-only and CHERIoT builds (PMODE=0), and `rv32_test_csr` and
`isa_test_csr` traces are identical to `802d481`
(`/home/scratch/fortress/kunyanliu/kudu_temp/kudu004_20261021_161307/runs2/`).
The `c32075d` fixes (KUDU-006/010) were checked on a snapshot that differs
from `c32075d` only in an equivalent `fetch_fifo64.sv` cast width:
`rtl_bug_rtype_rev8_reserved` and `rtl_bug_mret_asr_mtval` pass, and
`rv32_test_csr`/`isa_test_csr` traces are identical to `46179c1`
(`/home/scratch/fortress/kunyanliu/kudu_temp/kudu006_010_20261022_151618/`, buildD/runsD).
The `d88c674` fixes (KUDU-020/022/024) were checked on a snapshot identical to
`d88c674` (`/home/scratch/fortress/kunyanliu/kudu_temp/kudu022_20261022_180431/`, buildB; `/home/scratch/fortress/kunyanliu/kudu_temp/kudu020_20261022_175126/`;
`/home/scratch/fortress/kunyanliu/kudu_temp/kudu024_20261022_175505/`). On that RTL, `D3` and `P1`
(KUDU-023/025) still fail, and the issuer test still fails `I2`/`I4` and
hangs at `I3`.
The `0e68d2e` fixes (KUDU-012/017) and the `38d1ad3` fixes for
KUDU-023/025 (checked as uncommitted `rtl/`, identical to `38d1ad3`) were checked with `sim/run/run_full_regression.py --suite mini bug`
(`sim/run/temp_full_regression/run_20261023_125432/`): all mini-regression
tests and all reproducers of fixed bugs pass; reproducers of open bugs fail
only on their own checks. KUDU-025 was fixed by making the RV32 dpc/dscratch
CSRs illegal at PMODE=1, so `rtl_bug_debug_mode` (D1, P1),
`rtl_bug_issuer_debug` and `dbg_test1` were changed to stop using RV32
dpc/mepc accesses at PMODE=1 (see KUDU-025). `dbg_test1` was then rerun with
the rebuilt `debug_rom.vhx` (`/home/scratch/fortress/kunyanliu/kudu_temp/dbgrom_20261023_130147/run/`) and passes.
The `7028fb3` fixes (KUDU-007/008) were checked on a snapshot identical to
`7028fb3` (`/home/scratch/fortress/kunyanliu/kudu_temp/kudu007_008_atomics/snap4`, build `build4`):
`run_full_regression.py --suite all` gives 209 PASS, 12 XFAIL (open bugs),
0 FAIL (`/home/scratch/fortress/kunyanliu/kudu_temp/kudu007_008_atomics/regr4/results.txt`). A wider scratch
test, `atomics_chk` (`/home/scratch/fortress/kunyanliu/kudu_temp/kudu007_008_atomics/rerun.sh <build_dir>`, RV32
and CHERIoT builds at PMODE=0), passes every cause/rd/memory check; only the
misaligned mtval check fails (now tracked under KUDU-015).
The `1567152` fixes (KUDU-032/036) were checked on `rtl/` identical to
`1567152`: `run_full_regression.py` gives 239 PASS, 19 XFAIL (open bugs) and
2 FAIL, both the deferred KUDU-043 check
(`/home/scratch/fortress/kunyanliu/kudu_temp/full_regr_k032_20261029_155012/results.txt`). A random AMO stress
test (see KUDU-032) passes 144/144 runs and fails 36/36 on `85bbd3f`.
The `546cc56` fixes (KUDU-034/038/039) were checked on `rtl/` identical to
`546cc56`: `run_full_regression.py` gives 247 PASS, 11 XFAIL (open bugs) and
2 FAIL, both the deferred KUDU-043 check
(`/home/scratch/fortress/kunyanliu/kudu_temp/full_regr_k034_20261029_190359/results.txt`). A first version of
the KUDU-034 fix also trapped M-mode WFI when TW = 1 (case D of
`rtl_bug_umode_priv`); it was corrected before the commit.
The `d290cd0` single-step rework (KUDU-028/029/030/035/040) was checked on
`rtl/` that differs from `d290cd0` only in comments. With the dcsr.step tests
included (`--skip ''`), `run_full_regression.py` gives 253 PASS, 7 XFAIL
(KUDU-019, KUDU-042/043) and 0 FAIL on each of conf1, conf2 and conf3
(`/home/scratch/fortress/kunyanliu/kudu_temp/step_rework5_20261110_165929/regr_c{1,2,3}/results.txt`).
The scratch test `step_exec`, which single-steps three mixed workloads
(ALU, mul/div, loads/stores, branches, CHERI, AMO/LR/SC, traps) and compares
them with unstepped reference runs, passes on conf1-3 with default and
delayed memory (same directory, `se_c*`).
KUDU-031..043 and the slot-1 part of KUDU-013 come from a full RTL review of
`7028fb3` (2026-10-25; LSU, issuer, CSR, frontend and execution units reviewed
separately, evidence under `/home/scratch/fortress/kunyanliu/kudu_temp/fullreview_20261024_234209/<area>/`).
The execution-unit review (ALU, multdiv, `cheri_pkg` capability helpers)
found no bugs: 168k random multiply/divide operations matched, and the
`cheri_pkg` bounds/representability functions match cheriot-ibex and Sail.
`rtl_bug_fetch_slot1_err` needs the `+INSTR_ERR_ADDR=<hex>` option added to
`sim/tb/data_mem_model.sv` on 2026-10-25; rebuild `simv`/`simv32` before running it.
All new reproducers were run with `run_full_regression.py --suite bug` on a
fresh no-coverage build of `7028fb3` plus that TB change
(`/home/scratch/fortress/kunyanliu/kudu_temp/newbugs_regr_20261025_180531/` and `..._issuer/`): 67 jobs,
22 PASS, 45 XFAIL, 0 FAIL. Every new test fails only on its own bug checks.
Shadow-RTL builds under `/home/scratch/fortress/kunyanliu/kudu_temp/` only demonstrate suggested fixes;
they do not change a bug's status.
KUDU-044..047 come from a review of the ALT (branch fall-through) fetch
buffer on 2026-10-26. That review and a fetch-integrity checker found no
functional ALT bug; all four are low-severity robustness or lint issues.
- **Review evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/alt_review_20261026_102059/`. Its checker
  saw 0 errors over 137 simulations: 1.44M allocations, 201k restores and
  28k flushes of live entries. The simulations included 25 random
  branch-heavy programs, with interrupts and with random `cpuctrl`
  toggling of `pdt_en`/`alt_en`.
- **Fetch-integrity checker:** `/home/scratch/fortress/kunyanliu/kudu_temp/altchk_20261026_102135/`. It
  compares every fetch FIFO output with the instruction bus.
  `run_full_regression.py --suite all` gave 211 PASS, 45 XFAIL and 0 FAIL
  on both conf1 and conf3, with 0 checker errors over 13.7M instructions
  (473k ALT restores).
- **KUDU-013 via ALT:** the review also showed that KUDU-013 is reached
  through an ALT restore (`rtl_bug_alt_err`). With only the KUDU-013 fix
  that test passes, so the ALT path adds no error-handling bug of its own.

## Running the reproducers

> **Moved:** the reproducers now live in `sim/tests_2/rtl_bug_*/`, each with a
> `run.py` that builds its program, runs every variant on the farm and gives
> a verdict (`./run.py --build <stock build dir>`; all of them with
> `sim/tests_2/common/run_all.py`). See [direct_tests.md](direct_tests.md).
> The manual flow below is kept for reference; to use it, copy the test
> directory into `sim/tests/` first.

All commands run from `sim/run`. Build the simulators once for the current
RTL, then build each test program and run it. The build scripts compile in
`sim/tests/work/` and copy `<test>.vhx`/`<test>.elf` into `sim/run/bin/`.

```sh
cd sim/run
source /etc/profile.d/modules.sh
source ../run_dii/load_module_vcs
submit -i ./vcscomp -nowave          # ./simv; +PMODE=0 gives plain RV32
```

Generic form (`<test>` is the directory name under `sim/tests/`; the
build script and PMODE come from the table below):

```sh
(cd ../tests && ../scripts/<build script> <test>)
submit -i ./simv +TEST=<test> +PMODE=<0|1> +TIMEOUT=1000000 +ntb_random_seed=1 > <test>.log
```

CHERIoT tests (`cheri_atest.S`) use `build_test.sh` and `+PMODE=1`; RV32
tests (`rv32_atest.S`) use `build_test_rv32.sh` and `+PMODE=0`. `vcscomp`
also builds `./simv32` (CHERIoT compiled out); an RV32 test behaves the same
there as on `./simv +PMODE=0` (see "PMODE=0 vs RV32 equivalence" below), so
`./simv` alone is enough.

Delayed-memory variant: append
`+DATA_GNT_WMAX=3 +DATA_RESP_WMAX=5` (KUDU-001 also used
`+INSTR_GNT_WMAX=3 +INSTR_RESP_WMAX=3 +DATA_GNT_WMAX=3 +DATA_RESP_WMAX=3`).
Other pipeline configurations: build with `-conf2`/`-conf3` (they replace
`./simv`, so build them into another directory with `-outdir=<dir>` if the
default build must be kept).

The verdict is the UART line printed by the test (`grep "<verdict prefix>"
<test>.log`); `FAIL` lines above it give each failing case. Each run
overwrites `trace_kudu_core.log` and `rvfi_kudu_core.log` in `sim/run`;
rename them first if they are needed.

| ID | Test (`sim/tests_2/`) | Build script | PMODE | Verdict prefix |
|---|---|---|---|---|
| KUDU-001 (fixed) | `rtl_bug_csr_rmw` | `build_test_rv32.sh` | 0 | `CSR RMW` |
| KUDU-004/005 | `rtl_bug_trap_csr_values` | `build_test_rv32.sh` | 0 | `TRAP CSR VALUES` |
| KUDU-006 | `rtl_bug_rtype_rev8_reserved` | `build_test_rv32.sh` | 0 | `RTYPE REV8 RESERVED` |
| KUDU-007 | `rtl_bug_misaligned_amo` | `build_test_rv32.sh` | 0 | `MISALIGNED AMO` |
| KUDU-008 | `rtl_bug_amo_access_fault` | `build_test_rv32.sh` | 0 | `AMO ACCESS FAULT` |
| KUDU-009 (fixed) | `rtl_bug_trvk_boundary` | `build_test.sh` | 1 | `TRVK_BOUNDARY` |
| KUDU-010 | `rtl_bug_mret_asr_mtval` | `build_test.sh` | 1 | `MRET_ASR_MTVAL` |
| KUDU-011 (fixed) | `rtl_bug_jal_pdt_off` | `build_test_rv32.sh` | 0 | `JAL PDT OFF` (verdict at end of line) |
| KUDU-012 | `rtl_bug_debug_irq_not_ignored` | `build_dbg_test.sh` (see below) | 1 | `DEBUG IRQ`; a timeout is also a failure |
| KUDU-014 | `rtl_bug_sc_forwarding` | `build_test_rv32.sh` | 0, default and delayed | `SC FORWARDING` |
| KUDU-015 | `rtl_bug_cap_misaligned_mtval` | `build_test.sh` | 1, default and delayed | `CAP ALIGN MTVAL` |
| KUDU-016 | `rtl_bug_mshwm_csr_store_order` | `build_test.sh` | 1, default and delayed | `MSHWM ORDER` |
| KUDU-017, KUDU-018 | `rtl_bug_csr_asr_allowlist` | `build_test.sh` | 1, default and delayed | `CSR ASR` |
| KUDU-019 | `rtl_bug_minstret_write_order` | `build_test.sh` | 1, default and delayed | `MINSTRET INCREMENT` |
| KUDU-020 | `rtl_bug_misa_value` | `build_test_rv32.sh` (PMODE=0) or `build_test.sh` (PMODE=1) | 0 or 1 (see below) | `MISA VALUE` |
| KUDU-021..025 | `rtl_bug_debug_mode` | `build_dbg_test.sh` (see below) | 1 | `DEBUG MODE` (one line per case; D5 is INFO) |
| KUDU-026..030, KUDU-003 | `rtl_bug_issuer_debug` | `build_dbg_test.sh` (see below) | 1, default and delayed | `ISSUER DBG` (one line per case); a timeout is also a failure |
| KUDU-013 (slot 1) | `rtl_bug_fetch_slot1_err` | `build_test_rv32.sh` | 0 on `simv32` and `simv`; needs `+INSTR_ERR_ADDR=80010060 +TIMEOUT=300000` (see below) | `FSLOT1` |
| KUDU-013 (slot 1 via ALT) | `rtl_bug_alt_err` | `build_test_rv32.sh` | 0 on `simv32` and `simv`; needs `+INSTR_ERR_ADDR=80010100 +TIMEOUT=3000000` | `ALTERR` (`ALTERR FAIL KUDU013` per failing try) |
| KUDU-031 | `rtl_bug_misaligned_sc_rv32` | `build_test_rv32.sh` | 0, run on `simv32` (passes on `simv` at PMODE=0) | `MISALIGNED SC RV32` |
| KUDU-032, KUDU-036 | `rtl_bug_amo_cheri_fault` | `build_test.sh` | 1, default and delayed | `AMO CHERI FAULT` |
| KUDU-033 | `rtl_bug_dcache_split_store` | `build_test_rv32.sh` (PMODE=0) or `build_test.sh` (PMODE=1) | 0 (`simv32`, `simv`) or 1 | `DCACHE SPLIT STORE` |
| KUDU-034, KUDU-038 | `rtl_bug_umode_priv` | `build_test_rv32.sh` | 0 on `simv32` and `simv`; needs `+INTR_RATE=3` | `UPRIV` |
| KUDU-035 | `rtl_bug_debug_ecall` | `build_dbg_test.sh` (see below) | 1, default and delayed | `DEBUG ECALL` |
| KUDU-039 | `rtl_bug_jalr_odd_epc` | `build_test_rv32.sh` | 0 on `simv32` and `simv`; needs `+INTR_RATE=4` | `JALR ODD EPC` |
| KUDU-040 | `rtl_bug_halt_step_cause` | `build_dbg_test.sh` (see below) | 1, default and delayed | `HALT STEP CAUSE` |
| KUDU-037 | `rtl_bug_sc_mshwm` | `build_test.sh` | 1, default and delayed | `SC MSHWM` |
| KUDU-041..043 | `rtl_bug_csr_mtval_mstatush` | `build_test_rv32.sh` (PMODE=0) or `build_test.sh` (PMODE=1) | 0 (`simv32`, `simv`) or 1 | `CSR MTVAL MSTATUSH PMODE=` |
| Sail divergence | `rtl_bug_sail_zbkb_zbkx_missing` | `build_test.sh` | 1 | `SAIL ZBKB ZBKX` |
| Sail divergence | `rtl_bug_trigger_csr_sail` | `build_test_rv32.sh` | 0 | `SAIL TRIGGER CSR` |

Example (KUDU-016):

```sh
(cd ../tests && ../scripts/build_test.sh rtl_bug_mshwm_csr_store_order)
submit -i ./simv +TEST=rtl_bug_mshwm_csr_store_order +PMODE=1 +TIMEOUT=1000000 +ntb_random_seed=1 > rtl_bug_mshwm_csr_store_order.log
grep "MSHWM ORDER" rtl_bug_mshwm_csr_store_order.log
```

KUDU-020 has one source tree for both modes. Both build scripts write
`bin/rtl_bug_misa_value.*`, so build and run one mode at a time:

```sh
(cd ../tests && ../scripts/build_test_rv32.sh rtl_bug_misa_value)
submit -i ./simv +TEST=rtl_bug_misa_value +PMODE=0 +TIMEOUT=1000000 +ntb_random_seed=1 > rtl_bug_misa_value.pmode0.log
(cd ../tests && ../scripts/build_test.sh rtl_bug_misa_value)
submit -i ./simv +TEST=rtl_bug_misa_value +PMODE=1 +TIMEOUT=1000000 +ntb_random_seed=1 > rtl_bug_misa_value.pmode1.log
grep "MISA VALUE" rtl_bug_misa_value.pmode*.log
```

KUDU-021..025 also use a debug ROM. As for KUDU-012 (next paragraph), the
build overwrites `run/bin/debug_rom.vhx`, so save it and rename the new ROM:

```sh
t=rtl_bug_debug_mode
cp bin/debug_rom.vhx bin/debug_rom.vhx.save
(cd ../tests && ../scripts/build_dbg_test.sh $t)
cp bin/debug_rom.vhx bin/${t}_rom.vhx
mv bin/debug_rom.vhx.save bin/debug_rom.vhx
submit -i ./simv +TEST=$t +PMODE=1 +DBGROM=${t}_rom +TIMEOUT=400000 +ntb_random_seed=1 > $t.log
grep "DEBUG MODE" $t.log
```

KUDU-026..030 (and the stepped-WFI part of KUDU-003) use the same flow;
case I3 needs the TB interrupt generator (`+INTR_RATE=6`):

```sh
t=rtl_bug_issuer_debug
cp bin/debug_rom.vhx bin/debug_rom.vhx.save
(cd ../tests && ../scripts/build_dbg_test.sh $t)
cp bin/debug_rom.vhx bin/${t}_rom.vhx
mv bin/debug_rom.vhx.save bin/debug_rom.vhx
submit -i ./simv +TEST=$t +PMODE=1 +DBGROM=${t}_rom +INTR_RATE=6 +TIMEOUT=400000 +ntb_random_seed=1 > $t.log
grep "ISSUER DBG\|timed out" $t.log
```

On the current RTL this run times out in case I3 (KUDU-012 makes the
stepped IRQ case hang), so I3 and I5 are only reported by a build with
KUDU-012 fixed. The shadow builds under
`temp/issuer_dbg_20261020_122123/` show every case separately (see
KUDU-026).

KUDU-012 also builds a debug ROM. `build_dbg_test.sh` always writes
`run/bin/debug_rom.vhx`, which `dbg_test1` uses, so save it and give the new
ROM its own name:

```sh
t=rtl_bug_debug_irq_not_ignored
cp bin/debug_rom.vhx bin/debug_rom.vhx.save
(cd ../tests && ../scripts/build_dbg_test.sh $t)
cp bin/debug_rom.vhx bin/${t}_rom.vhx
mv bin/debug_rom.vhx.save bin/debug_rom.vhx
submit -i ./simv +TEST=$t +PMODE=1 +DBGROM=${t}_rom +INTR_RATE=6 +TIMEOUT=300000 +ntb_random_seed=1 > $t.log
grep "DEBUG IRQ\|timed out" $t.log
```

The same CHERIoT ELF can be run on Sail from `sim/run`; the UART output is
rebuilt from the trace's stores to `0x83800200`:

```sh
../temp/cheriot_sail_dii_20261013_155851/c_emulator/cheriot_sim --trace -l 200000 bin/<test>.elf \
  | perl -ne 'print chr(hex($1) & 0xff) if /^mem\[0x83800200\] <- 0x([0-9A-Fa-f]+)$/'
```

Sail runs CHERIoT ELFs only (built with `build_test.sh`).

KUDU-013 (slot-1 case) uses the testbench option `+INSTR_ERR_ADDR=<hex>`,
which returns a bus error for every fetch of that 64-bit-aligned word; it
needs a `simv`/`simv32` built after it was added to `sim/tb/data_mem_model.sv`:

```sh
(cd ../tests && ../scripts/build_test_rv32.sh rtl_bug_fetch_slot1_err)
submit -i ./simv32 +TEST=rtl_bug_fetch_slot1_err +PMODE=0 +INSTR_ERR_ADDR=80010060 +TIMEOUT=300000 +ntb_random_seed=1 > rtl_bug_fetch_slot1_err.log
grep "FSLOT1" rtl_bug_fetch_slot1_err.log
```

Without the plusarg the test reports the KUDU-013 check as SKIP and
`FSLOT1_CTRL_FIRSTWORD` as FAIL.

KUDU-002 and KUDU-003 need block-level stimulus, and the straddling part of
KUDU-013 uses a local memory model, so they have no `sim/tests/` program.
Their local testbenches are run with
`bash temp/rtl_local_testbenches_N4M41zU8/rtl_bug_store_access_fault/run.sh`
(KUDU-002), `bash temp/rtl_local_testbenches_N4M41zU8/rtl_bug_wfi_debug_halt/run.sh`
(KUDU-003) and `bash temp/rtl_review3_lsu_20261013_155807/run_fetch_straddle_mtval.sh`
(KUDU-013), from `sim/`.

---

## KUDU-001: MTVEC/MEPC CSR set/clear corruption

- **Status:** Fixed in `dd4543c`.
- **Location:** `rtl/cs_registers.sv` (address legalization, formerly line 1656).
- **Description:** `cs_registers.sv` correctly computes the merged
  read-modify-write value `csr_wdata32` for CSRRS/CSRRC, but the shared
  MTVEC/MEPC (and DPC) address legalizer used the raw operand
  `csr_wdata_i`. CSRRS/CSRRC, their immediate forms with nonzero zimm, and
  register forms with a non-x0 zero source wrote the operand itself.
- **Expected:** SET writes `old | operand`; CLEAR writes `old & ~operand`.
- **Observed:** MTVEC = `0x80000100`, `csrrs mtvec, 0x200` → `0x00000200`
  (expected `0x80000300`).
- **Fix:** `new_addr_tmp = csr_wdata32[31:0]`.
- **Reproducer:** `sim/tests_2/rtl_bug_csr_rmw/` (27 checks, 12 MTVEC/MEPC
  failures before the fix; PMODE=0 on both elaborations, default and delayed
  memory). Also covered by the patterned checks in `sim/tests/rv32_test_csr/`.
- **Note:** DPC shares the path but was not separately reproduced in debug mode.

## KUDU-002: Store bus error reported as load access fault

- **Status:** Fixed in `cd63cce`.
- **Location:** `rtl/load_store_unit.sv` (formerly lines 642-644).
- **Description:** On a data bus error the LSU unconditionally set
  `lsu_err_mcause = EXC_CAUSE_LOAD_ACCESS_FAULT`. Committer and issuer
  forward the cause unchanged to the CSRs.
- **Expected:** Store access fault, mcause **7**.
- **Observed:** Aligned SW with bus error → mcause **5**.
- **Fix:** select load or store cause from `lsu_req_info_q.is_load`.
- **Reproducer:** block-level LSU testbench
  `/home/scratch/fortress/kunyanliu/kudu_temp/rtl_local_testbenches_N4M41zU8/rtl_bug_store_access_fault/`.
  Successful LW/SW and faulting LW controls pass; immediate and delayed SW
  error cases failed before the fix.
- **Related:** KUDU-008 (the AMO path still marks its read phase as a load).

## KUDU-003: WFI is not woken by a debug halt request

- **Status:** Fixed in `802d481`. `rtl/issuer.sv:598-599` now leaves
  `CSM_SLEEP` on `irq_pending_i | debug_req_i | debug_mode_q |
  debug_single_step_i`. The local TB passes on `802d481`
  (`/home/scratch/fortress/kunyanliu/kudu_temp/rtl_pipeline_review_wfi_debug_20261020_230736_1965395/reproduce.log`:
  `PASS: sleeping core honors debug halt`). The stepped-WFI case (`I5`)
  is not reached in the full-system test on `802d481`, which hangs earlier
  at `I3` (KUDU-012).
- **Location:** `rtl/issuer.sv:597-600` (`CSM_SLEEP`).
- **Description:** The sleep state exits only on `irq_pending_i`. A held
  debug request leaves the core asleep with `debug_mode=0` and no fetch.
- **Spec:** RISC-V Debug Spec 0.13.2: a halt request must wake a hart
  stalled in WFI.
- **Expected:** Core enters debug mode while the halt request is held.
- **Observed:** Debug request held for 32 cycles; core stays in sleep, no
  fetch request, `debug_mode` stays 0. Ordinary halt and interrupt wake
  controls pass.
- **Suggested fix:** also exit `CSM_SLEEP` when a debug request (or
  single-step condition) is pending.
- **Reproducer:** real decoder + issuer with legal WFI stimulus, no forced
  internal state:
  `/home/scratch/fortress/kunyanliu/kudu_temp/rtl_local_testbenches_N4M41zU8/rtl_bug_wfi_debug_halt/`.
- **Single-step variant (2026-10-20):** a `wfi` executed with `dcsr.step=1`
  and no interrupt enabled also sleeps forever, because the step halt is
  never taken from `CSM_SLEEP`. cheriot-ibex `ibex_controller.sv:514-516`
  leaves SLEEP on `debug_req_i | debug_mode_q | debug_single_step_i`
  ("in debug mode or single step mode we leave immediately (wfi=nop)").
  Full-system reproducer: `sim/tests_2/rtl_bug_issuer_debug/`, case `I5`
  (prints `I5 step-wfi start`, then times out on `6378440`).

## KUDU-004: DRET outside debug mode raises CHERI fault

- **Status:** Fixed in `46179c1`.
- **Location:** `rtl/issuer.sv:783` (special-case selection),
  `rtl/issuer.sv:957-981` (EXEC exception info).
- **Description:** `dret & ~debug_mode_q` is routed to the generic EXEC
  special case. No error flag matches, so the default
  `EXC_CAUSE_CHERI_FAULT` with mtval 0 is used.
- **Spec/reference:** Debug Spec 0.13.2, DRET is illegal outside debug
  mode. cheriot-ibex `ibex_controller.sv:238,254` folds `illegal_dret` into
  illegal instruction.
- **Expected:** mcause **2**, mtval **0x7b200073** (PMODE=0).
- **Observed:** mcause **0x1c**, mtval **0**; mepc correct.
- **Fix (`46179c1`, `rtl/issuer.sv:973-974`):** the EXEC illegal-instruction
  branch also matches `~debug_mode_q & ir0_dec.sysctl.dret`, giving mcause 2
  and mtval = the instruction (PMODE=0) or 0 (PMODE=1).
- **Verification on `46179c1`:** the `dret_mcause`, `dret_mtval` and
  `dret_mepc` checks pass on the RV32-only build and on the CHERIoT build at
  PMODE=0. PMODE=1 is not covered by the reproducer.
- **Reproducer:** `sim/tests_2/rtl_bug_trap_csr_values/` (RV32, PMODE=0).

## KUDU-005: ECALL writes mtval = PC

- **Status:** Fixed in `46179c1`.
- **Location:** `rtl/issuer.sv:997-1005`.
- **Description:** The SYSCTL trap path sets `mtval = ir0_dec.pc` for both
  EBREAK and ECALL.
- **Spec/reference:** Privileged spec: mtval is zero for traps that do not
  define it, including ECALL. cheriot-ibex leaves mtval 0 for ECALL. Writing
  the PC for EBREAK is permitted.
- **Expected:** ECALL mtval **0**.
- **Observed:** ECALL mtval **0x800003d4** (the ECALL PC). mcause and mepc
  correct.
- **Fix (`46179c1`, `rtl/issuer.sv:1004`):**
  `mtval = sysctl_q.ebrk ? ir0_dec.pc : 32'h0`.
- **Verification on `46179c1`:** `rtl_bug_trap_csr_values` passes 6/6
  (ECALL mtval 0); `rv32_test_csr` and `isa_test_csr` traces are unchanged
  from `802d481`.
- **Reproducer:** `sim/tests_2/rtl_bug_trap_csr_values/`.

## KUDU-006: Reserved R-type encoding accepted as `rev8`

- **Status:** Fixed in `c32075d`.
- **Location:** `rtl/ir_decoder.sv:397-400` (R-type OP decoder, case at line
  336); `rtl/alu_decoder.sv` falls through to the default `ALU_SLTU`.
- **Description:** `{funct7=0x34, funct3=5, opcode=OP, rs2=24}` (draft
  `grev`) is decoded as legal `rev8`. Ratified Zbb defines `rev8` only as
  OP-IMM (`0x69805013` on RV32).
- **Expected:** Illegal-instruction trap, mcause **2**.
- **Observed:** No trap; instruction retires (tracer shows
  `grev x6,x5,x24`) and writes **0** to rd.
- **Fix (`c32075d`):** the R-type `rev8` case was removed, so the encoding
  falls to `default` (illegal). The OP-IMM `rev8` is unchanged.
- **Verification:** `rtl_bug_rtype_rev8_reserved` passes on the RV32-only
  build (trap, mcause 2, rd not written).
- **Reproducer:** `sim/tests_2/rtl_bug_rtype_rev8_reserved/` (fails on both
  elaborations at PMODE=0).

## KUDU-007: Misaligned AMO and SC do not trap

- **Status:** Fixed in `7028fb3`: `check_ls_err` (`rtl/cheri_pkg.sv:1050,1052`)
  flags misaligned LR/SC/AMO in every mode, the request is blocked before the
  bus, and `rtl/load_store_unit.sv:621` selects the cause by instruction type
  (LR 4; SC/AMO 6). Checked on RV32 and CHERIoT (PMODE=0) builds: misaligned
  `lr.w` -> 4, `sc.w`/`amoswap.w`/`amoadd.w`/`amoor.w` -> 6, rd and memory
  unchanged. mtval is still the previous access's address; that part is
  tracked under KUDU-015. Intermediate RTL found two issues that `7028fb3`
  fixes: AMO misalignment reported cause 4, and at PMODE=0 the CHERIoT build
  hung (`all_resp` required `cheri_pmode & req_err_q`).
- **Location:** `rtl/load_store_unit.sv:357-359` (misaligned word split);
  `rtl/ls_pipeline.sv:209-219` (LR/SC), `rtl/cmplx_unit.sv:165-167` (AMO)
  issue through that path.
- **Description:** Misaligned word accesses are split into two aligned
  accesses for all requests, including atomics.
- **Spec:** RV32A: a misaligned LR/SC/AMO address raises an
  address-misaligned or access-fault exception (no misaligned atomicity
  granule is implemented); memory must not be updated.
- **Expected:** Trap with mcause 6 (or 7) for SC/AMO and 4 (or 5) for LR,
  mtval = the misaligned address, rd and memory unchanged.
- **Observed:** `amoswap.w` at `addr+1` completes without trapping, returns
  `0x88112233` and modifies two words non-atomically (`0xbbccdd44`,
  `0x556677aa`); misaligned `sc.w` returns failure (rd=1) without trapping.
- **Suggested fix:** detect misalignment for LR/SC/AMO requests and raise an
  exception instead of splitting.
- **Reproducer:** `sim/tests_2/rtl_bug_misaligned_amo/` (fails on both
  elaborations at PMODE=0).

## KUDU-008: AMO bus error reports load access fault

- **Status:** Fixed in `7028fb3` (`rtl/load_store_unit.sv:636`: load access
  fault only for loads that are not AMOs). AMO bus error -> mcause 7; LR bus
  error stays mcause 5 (an intermediate version reported 7 for LR).
- **Location:** `rtl/cmplx_unit.sv:162` (`is_load = ~(cmplx_fsm_cs == AMO_WRITE)`),
  `rtl/load_store_unit.sv:643` (cause selection).
- **Description:** The AMO read phase is issued as a load, so a bus error on
  it maps to load access fault even after the KUDU-002 fix.
- **Spec:** Privileged spec: AMOs raise store/AMO access fault, never load
  access fault.
- **Expected:** mcause **7**.
- **Observed:** `amoswap.w` to invalid address `0x90000000` → mcause **5**,
  mtval `0x90000000`, rd preserved.
- **Suggested fix:** use store/AMO cause when `amo_flag` indicates an AMO
  phase (LR may keep load fault).
- **Reproducer:** `sim/tests_2/rtl_bug_amo_access_fault/` (fails on both
  elaborations at PMODE=0).

## KUDU-009: Load-barrier TSMAP range check off by one

- **Status:** Fixed in `d687956`.
- **Location:** `rtl/cheri_trvk_stage.sv:50`.
- **Description:** `range_ok = (tsmap_ptr[31:5] <= TSMapSize) && ...`.
  `TSMapSize` is the TSMAP size in 32-bit words (1024 → 256 KiB of heap), so
  valid word indices are `0 .. TSMapSize-1`. Index 1024 is accepted; the
  testbench TSMAP SRAM aliases it to word 0 (`tb/data_mem_model.sv`).
- **Expected:** A capability whose base lies just past the covered heap
  (`HeapBase + 256 KiB`, e.g. `0x80040000`) is out of range and keeps its tag.
- **Observed:** Its tag is cleared using revocation bits of word 0; the
  in-range control behaves correctly.
- **Suggested fix:** use `<` instead of `<=`.
- **Note:** cheriot-ibex `cheri_trvk_stage.sv:64` has the same expression,
  so trace comparison against cheriot-ibex does not detect this.
- **Reproducer:** `sim/tests_2/rtl_bug_trvk_boundary/` (CHERIoT, PMODE=1).

## KUDU-010: MRET without PCC.ASR reports the wrong CHERI mtval

- **Status:** Fixed in `c32075d`.
- **Location:** `rtl/ir_decoder.sv:580-582` (MRET ASR check folded into
  `cheri_perm_vio`), `rtl/issuer.sv:959-961` (perm_vio mtval encoding).
- **Description:** A missing PCC system-register permission on MRET is
  merged with the generic PCC permission/validity checks; the issuer then
  encodes every `perm_vio` as cause **0x02** (tag violation).
- **Reference:** Sail `src/cheri_addr_checks.sail:246-250` raises
  `CapEx_AccessSystemRegsViolation` (**0x18**) on PCC, capability index 0
  (S=1). cheriot-ibex agrees with Sail.
- **Expected:** mcause **0x1c**, mtval **0x418**.
- **Observed:** mcause **0x1c**, mtval **0x402**. Running the same ELF on
  Sail differs only in mtval.
- **Fix (`c32075d`):** new `ir_errs_t.asr_vio` flag (`rtl/super_pkg.sv:39`),
  set by `cheri_asr_vio` (`rtl/ir_decoder.sv:579`) and included in `any_err`
  (`:89`); the issuer encodes it as mtval `{S=1, idx=0, 0x18}`
  (`rtl/issuer.sv:978-980`).
- **Verification:** `rtl_bug_mret_asr_mtval` passes (mcause 0x1c, mtval
  0x418). Without the `any_err` term the MRET retired without trapping.
- **Reproducer:** `sim/tests_2/rtl_bug_mret_asr_mtval/` (CHERIoT, PMODE=1).

## KUDU-011: JAL does not redirect with the predictor disabled

- **Status:** Fixed in `6378440`.
- **Location:** `rtl/branch_unit.sv:88`
  (`result[2] = is_jal && ChkBranchJALAddr && ptarget != btarget`);
  `ChkBranchJALAddr` = `CFG.PredictUseBtb` (`rtl/kudu_top.sv:407`).
- **Description:** With CPUCTRL `pdt_en=0` a JAL is not predicted taken, so
  only the execute-stage mispredict can redirect it. That mispredict is
  gated by `ChkBranchJALAddr`, which is false in the default configuration,
  so execution falls through to PC+4 (rd is still written).
- **Reference:** Sail `sail-riscv/model/riscv_insts_base.sail:60-76` (JAL
  always jumps).
- **Expected:** Jump target executes (`0x11111111` marker).
- **Observed:** Fall-through executes (`0xdead0001` marker).
- **Suggested fix:** also flag a mispredict when the JAL was not predicted
  taken (`~ir_dec.ptaken`), independent of `ChkBranchJALAddr`.
- **Reproducer:** `sim/tests_2/rtl_bug_jal_pdt_off/` (RV32, PMODE=0).

## KUDU-012: Interrupts are taken in debug mode

- **Status:** Fixed in `0e68d2e` (`handle_irq` gated by `~debug_mode_q`);
  still present in `802d481`.
- **Location:** `rtl/issuer.sv:726`
  (`handle_irq = irq_pending_i & csr_mstatus_mie_i`); `irq_pending_o` in
  `rtl/cs_registers.sv:857` is not masked either.
- **Description:** Nothing masks interrupts while `debug_mode_q` is set.
- **Spec/reference:** Debug Spec 0.13.2 §4.1: interrupts (including NMI) are
  ignored in debug mode. cheriot-ibex `ibex_controller.sv:418` gates with
  `~debug_mode_q`.
- **Expected:** Debug ROM with MIE set and an interrupt pending finishes and
  returns with DRET.
- **Observed:** The interrupt is taken from inside debug mode; the run never
  returns and times out at 300k cycles.
- **Suggested fix:** `handle_irq = irq_pending_i & csr_mstatus_mie_i & ~debug_mode_q`.
- **Reproducer:** `sim/tests_2/rtl_bug_debug_irq_not_ignored/`
  (`+DBGROM=debug_rom +INTR_INTVL=1`, CHERIoT).

## KUDU-013: Fetch bus error on the second fetch word is imprecise or lost

- **Status:** Fixed in `e79286b`. `fetch_fifo64` sets `fetch_err[1]` from
  the word the slot-1 instruction comes from and adds a per-slot
  `fetch_err2w` flag (instruction straddles into an error word), carried
  through `ir_reg_t`/`ir_dec_t` as `ferr2w`; `issuer` reports
  `mtval = ferr2w ? pc + 2 : pc`. Widened on 2026-10-25 (full review of
  `7028fb3`) to include the slot-1 case below, which shares the same root
  cause and is more severe.
- **Fix verification (2026-10-27):**
  - Directed: `rtl_bug_fetch_straddle_mtval`, `rtl_bug_fetch_slot1_err`,
    `rtl_bug_alt_err` and a new straddle test (32-bit instruction at
    `0x8001005e` straddling into error word `0x80010060`, 8 layouts) pass
    80/80 (5 seeds, conf1/conf3, default/delayed memory). Two intermediate
    fix attempts failed here: a wrong `instr_addr16 == 1` condition gave
    a false fault, and a 1-bit `fetch_err2w` assignment put the flag on
    slot 0 (`/home/scratch/fortress/kunyanliu/kudu_temp/k013fix_20261027_151222/`).
  - Random stress: a generator builds 24 programs × 64 code blobs placed
    around error word `0x80010060` (straddling, all four halfword
    positions, entry via jumps/branches, loops, compressed and 32-bit
    mixes, loads/stores, mul/div). Each blob runs once at a good address
    (no-trap control) and once over the error word, checking trap/no-trap,
    mcause, mepc, mtval and register state. 432 runs (conf1-3, `simv32`
    and `simv` at PMODE=0, three memory-delay variants) all pass on
    `e79286b`; the pre-fix RTL fails 20 of 48 cases on seed 1 with both
    symptoms (`/home/scratch/fortress/kunyanliu/kudu_temp/fetcherr_stress_20261027_163514/`).
  - Full regression on `e79286b` (mini regression with trace diff against
    `run_ibex`, plus riscv-tests on `simv32` and `simv` at PMODE=0,
    conf0-3, 732 runs) is clean (`/home/scratch/fortress/kunyanliu/kudu_temp/fullregr_20261027_165328/`).
- **Location:** `rtl/fetch_fifo64.sv:241-252` (`fetch_err` per output slot;
  `fetch_err = 2'b01` for a 32-bit instruction straddling a fetch word, and
  `fetch_err[1]` is never set when only the second fetch word has an error),
  `rtl/issuer.sv:966-968` (`mtval = ir0_dec.pc`).
- **Description:** The fetch FIFO keeps one error bit per 64-bit fetch word
  and does not record which output slot or halfword faulted.
  - *Straddling instruction:* the issuer always reports the instruction
    start as mtval.
  - *Slot 1 in the error word:* when the slot-0 instruction comes from a
    good word and the slot-1 instruction from the following error word, slot
    1 gets no fault. It issues and retires using the bus error data, and the
    fetch fault is taken one instruction later.
- **Spec/reference:** Privileged spec: for variable-length instructions
  mtval holds the address of the faulting portion while mepc holds the
  instruction start, and a fetch access fault must be precise. Sail
  `sail-riscv/model/riscv_fetch.sail:40-46` returns `F_Error(e, PC_hi)` for
  an upper-half fault.
- **Expected:** straddling instruction at `0x80000506`, upper half
  `0x80000508` faults: mepc **0x80000506**, mtval **0x80000508**.
  Slot 1: the fetch of word `0x80010060` errors, so the instruction at
  `0x80010060` traps with mcause 1, mepc = mtval = **0x80010060**, and
  `a4` keeps its preset value `0xdead0004`.
- **Observed:** straddling: mtval **0x80000506**. Slot 1: in 7-10 of 12 tries
  the `addi a4` at `0x80010060` retires (`a4 = 0x44`) and the trap is taken
  at the next instruction (mepc = mtval = **0x80010064**). Seen on `simv32`
  and on `simv` at PMODE=0, with default and delayed memory.
- **Suggested fix:** keep a per-halfword (or per-slot) error flag in
  `fetch_fifo64`, set `fetch_err[1]` from the word the slot-1 instruction
  comes from, carry an upper-half-fault flag through IF/IR, and use `pc + 2`
  for mtval in the straddling case.
- **Reproducer:** straddling case:
  `/home/scratch/fortress/kunyanliu/kudu_temp/rtl_review3_lsu_20261013_155807/run_fetch_straddle_mtval.sh`
  (full TB with a local instruction-error memory model). Slot-1 case:
  `sim/tests_2/rtl_bug_fetch_slot1_err/` (needs `+INSTR_ERR_ADDR=80010060`).
  Slot-1 case via an ALT restore: `sim/tests_2/rtl_bug_alt_err/` (needs
  `+INSTR_ERR_ADDR=80010100`).
- **ALT path (2026-10-26):** a mispredicted-not-taken branch refills the
  fetch FIFO from the ALT buffer, error bits included, and the refilled
  words go through the same output logic, so the slot-1 case also occurs
  after an ALT restore. `rtl_bug_alt_err` fails in 24-50 of 368 tries on
  conf1 and conf3: mepc = mtval = **0x80010102** instead of `0x80010100`,
  because the first instruction of the error word retired. With a shadow
  RTL that only adds the slot-1 `fetch_err[1]` fix, every try passes. The
  checker there showed 174 allocations and 70 restores of entries holding
  error words, so the suggested fix also covers the restore path
  (`/home/scratch/fortress/kunyanliu/kudu_temp/alt_review_20261026_102059/runs/k13*_alterr*`).
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/fullreview_20261024_234209/frontend/` (`run_fs1_*`).

## KUDU-014: Failed SC forwards uncommitted store data

- **Status:** Fixed in `991dba4`. `byp_data_good` now excludes SC
  (`amo_flag[1]`), and an SC response always invalidates the matching
  line (`resp_invalidate`). Reproduced on `6378440` on 2026-10-19.
- **Fix verification (2026-10-28):**
  - Random stress: SC/AMO forwarding generator (failed and successful SC,
    SC followed by loads of the same word, AMOSWAP/AMOADD) plus
    `rtl_bug_sc_forwarding`: 264/264 PASS on conf0-3, `simv32` and `simv`
    (PMODE=0/1), default and delayed memory. The pre-fix RTL fails
    40/56 runs of one scenario.
  - Full regression (conf0-3, mini regression with trace diff and
    riscv-tests): 732/732 OK.
  - Rerun on `6e157c3` (KUDU-033/050 fix): SC stress 264/264 PASS.
  - Artefacts: `/home/scratch/fortress/kunyanliu/kudu_temp/k014chk_20261028_083849/`,
    `/home/scratch/fortress/kunyanliu/kudu_temp/fullregr_k014_20261028_085233/`.
- **Location:** `rtl/dcache.sv:133-139,163-184` (store-to-load bypass);
  `rtl/ls_pipeline.sv:227` disables SC caching but not this bypass.
- **Description:** The bypass treats a preceding full-word SC as an
  unconditional store. It forwards the SC operand without excluding SC or
  waiting for its success. A following load can retire the correct memory
  value while its dependent instructions have already consumed the wrong
  bypass value.
- **Spec/reference:** A failed SC must not write memory. Base Sail
  `sail-riscv/model/riscv_insts_aext.sail:145-147` returns failure without
  performing the write. The configured CHERIoT Sail model and cheriot-ibex
  do not implement A, so this is a specification/base-source comparison,
  not an executable atomic comparison against either reference.
- **Expected:** With memory holding `0x11223344`, a failed SC returns **1**
  and a subsequent LW supplies `0x11223344` to its consumers; adding one
  yields `0x11223345`.
- **Observed:** SC returns **1**. The LW retirement trace shows
  `0x11223344`, but its dependent ADD receives `0xaabbccdd` (the failed SC
  operand) and produces `0xaabbccde`. A dependent store also captures the
  wrong value. A later, spaced reload confirms memory stayed `0x11223344`.
- **Controls:** The immediate-load case fails on both RV32-only and
  CHERIoT-capable builds at PMODE=0 with default memory timing. The
  spaced-load control passes. The delayed-memory variant also passes,
  demonstrating that this is timing-dependent forwarding corruption, not
  an unconditional memory write by failed SC.
- **Suggested fix:** Do not make SC data available through ordinary store
  bypass unless successful completion is established; alternatively
  exclude SC from this bypass and interlock following accesses.
- **Reproducer:** `sim/tests_2/rtl_bug_sc_forwarding/`.
- **Evidence:** Independent rerun:
  `/home/scratch/fortress/kunyanliu/kudu_temp/rtl_review4_vANt6851/memory/rtl_sc_forwarding_s5mweqgo/`.
  Each variant retains its simulation log and instruction trace.
  Launcher exits **1** with `SC FORWARDING FAIL` for the affected cases.

## KUDU-015: Misaligned capability accesses report stale mtval

- **Status:** Fixed in `85bbd3f`; reproduced on `6378440` on 2026-10-19.
  Fix: the misaligned-access branch now reports
  `lsu_req_info_q.addr` for capability and atomic requests
  (`addr_last_q` otherwise).
- **Fix verification (2026-10-28, RTL identical to `85bbd3f`):**
  - `rtl_bug_cap_misaligned_mtval` (PMODE=1), conf0-3 × d/ws/wb memory
    modes: 12/12 PASS.
  - `atomics_chk` (misaligned AMO/LR/SC mtval) on `simv32` and on `simv` at
    PMODE=0: 24/24 PASS.
  - Full regressions 732/732 OK (`/home/scratch/fortress/kunyanliu/kudu_temp/fullregr_k015_20261028_172513`,
    `/home/scratch/fortress/kunyanliu/kudu_temp/fullregr_k041v2_20261028_181557`).
- **Original report:** Since `7028fb3`
  the same defect also affects misaligned LR/SC/AMO (KUDU-007 fix), on both
  the RV32 and CHERIoT builds: e.g. misaligned `amoswap.w` at **`0x800042b9`**
  reports mtval **`0x800042bc`** (the preceding store's address). Not covered
  by `rtl_bug_cap_misaligned_mtval`; see `atomics_chk` in
  `/home/scratch/fortress/kunyanliu/kudu_temp/kudu007_008_atomics/`. In `7028fb3` both cases come from
  `rtl/load_store_unit.sv:623` (`lsu_err_mtval = addr_last_q`) after the
  request is blocked at `:399`.
- **Location:** `rtl/load_store_unit.sv:372,397-399` (rejected CHERI
  request path), `rtl/load_store_unit.sv:628-630` (alignment exception).
- **Description:** A capability access rejected by the prechecks does not
  update `addr_last_q`. Alignment exception generation nevertheless uses
  that register for mtval, exposing the preceding access's address.
- **Reference:** Sail `src/cheri_insts.sail:873-874,971-972` supplies the
  faulting effective address for capability store/load misalignment.
  cheriot-ibex `rtl/ibex_load_store_unit.sv:489-499` explicitly captures
  the address of a rejected CHERI request; its
  `rtl/ibex_controller.sv:803-820` uses it for alignment mtval.
- **Expected:** Misaligned CSC and CLC at **`0x80004024`** raise causes
  **6** and **4**, respectively, both with mtval **`0x80004024`**.
- **Observed:** Both causes are correct, but both mtval values are
  **`0x80004030`**, the preceding store's address.
- **Controls:** Both CSC and buffered CLC cases fail with default and
  delayed memory timing. The **same CHERIoT ELF passes both cases on
  Sail**, reporting the expected fault address.
- **Suggested fix:** Capture the faulting effective address when accepting
  a precheck-rejected request, independently of issuing a bus request.
  Preserve the existing address tracking for subsequent split bus faults.
- **Reproducer:** `sim/tests_2/rtl_bug_cap_misaligned_mtval/` (PMODE=1).
- **Evidence:** Independent Kudu/Sail rerun:
  `/home/scratch/fortress/kunyanliu/kudu_temp/rtl_review4_vANt6851/memory/rtl_cap_align_mtval_p4sjt6jk/`.
  `default/` and `delayed/` contain `CAP ALIGN MTVAL FAIL`; `sail/`
  contains the Sail trace and reconstructed UART output with
  `CAP ALIGN MTVAL PASS`. Launcher exits **1** while Kudu fails.

## KUDU-016: Store checked against stale MSHWM after a CSR write

- **Status:** Fixed in `1663deb`; reproduced on `6378440` on 2026-10-19
  (conf1, conf2, conf3). The MSHWM update request moved from the request
  side (`rtl/ls_pipeline.sv`) to the store response in the LSU
  (`rtl/load_store_unit.sv:699-701`, `csr_lsu_wr_req_o`/`csr_lsu_addr_o`),
  so it reaches the CSR unit only after any older CSR write has committed.
- **Fix verification (2026-10-28, RTL identical to `1663deb`):**
  - Random stress: a new generator (`gen_mshwm.py`) builds 30 CHERIoT
    programs (`msw_s1..30`), each with 60 bursts of stores, `csrw
    mshwm`/`mshwmb` and MSHWM read-backs, biased to place stores right after
    a CSR write and behind an older store; about 4,300 MSHWM values checked.
    360/360 PASS on conf0-3, PMODE=1, default and two delayed-memory
    settings. Pre-fix RTL (`6e157c3`): 112/120 fail.
  - `rtl_bug_mshwm_csr_store_order`: 12/12 PASS (pre-fix 4/4 fail).
  - Full regression 732/732 OK.
  - Artefacts: `/home/scratch/fortress/kunyanliu/kudu_temp/k016chk_20261028_121848/gen/` (generator),
    `/home/scratch/fortress/kunyanliu/kudu_temp/k037v3_20261028_125919/`,
    `/home/scratch/fortress/kunyanliu/kudu_temp/fullregr_k037v3_20261028_130355/`.
- **Location:** `rtl/cs_registers.sv:983-986` (`csr_mshwm_set`/`mshwm_d`),
  `rtl/ls_pipeline.sv:259` (`csr_lsu_wr_req_o`),
  `rtl/load_store_unit.sv:388,529,578` (CSR executes at `csr_go_q`).
- **Description:** A CSR write to MSHWM/MSHWMB commits one cycle after
  `csr_go`. When an older store is in flight, a younger store can reach
  `lsu_req_done` in that same cycle. Its stack high-water-mark check then
  uses the pre-write `mshwm_q`/`mshwmb_q`, and an LSU update overrides the
  CSR write. Program order is violated in both directions: a required
  update is lost, or an update that should be suppressed happens.
- **Reference:** Sail `src/cheri_addr_checks.sail:234-239` updates MSHWM at
  each store against the current MSHWMB/MSHWM, after all older CSR writes.
- **Expected:** `csw` → `csrw mshwm, base+256` → `csw zero, 100(base)`
  leaves MSHWM = **base+96**. With MSHWMB raised to base+128 instead,
  MSHWM stays **base+256**.
- **Observed:** MSHWM = **base+256** (store update lost) and **base+96**
  (store wrongly recorded below MSHWMB), respectively. Kudu fails cases
  0-3 with default memory and cases 0, 1 and 3 with delayed memory. In the
  trace the younger store retires one cycle after the `csrw`.
- **Controls:** Without the older store, or with a gap before the younger
  store, Kudu passes. The **same CHERIoT ELF passes all 6 cases on Sail**.
- **Suggested fix:** Stall a store that follows an MSHWM/MSHWMB CSR write
  until the write commits. Alternatively, forward the CSR write data into
  the `csr_mshwm_set` compare and give the later store's update priority
  over the earlier CSR write.
- **Reproducer:** `sim/tests_2/rtl_bug_mshwm_csr_store_order/` (PMODE=1).
- **Evidence:**
  `/home/scratch/fortress/kunyanliu/kudu_temp/rtl_review5_z93jS7Dl/mshwm/rtl_mshwm_order_ojqhd9jj/`
  (`build{0,1,2}_{default,delayed}` = conf1/2/3, `sail/`). Found by a
  Kudu-vs-Sail MSHWM differential test
  (`/home/scratch/fortress/kunyanliu/kudu_temp/rtl_review5_z93jS7Dl/mshwm/run1/`).

## KUDU-017: Counter writes allowed without PCC.ASR

- **Status:** Fixed in `0e68d2e` (`csr_cheri_always_ok` now requires
  `csr_op_o == CSR_OP_READ`); reproduced on `6378440` on 2026-10-19 (conf1,
  conf2, conf3). Cases 0-3 pass; cases 4-5 belong to KUDU-018 (open).
- **Location:** `rtl/load_store_unit.sv:588-590` (`csr_cheri_always_ok`).
- **Description:** The ASR exemption covers every CSR in
  `0xB00-0xB1F`, `0xB80-0xB9F`, `0xC00-0xC1F` and `0xC80-0xC9F`, regardless
  of access direction. Code without ASR can therefore reset or forge
  `mcycle`, `minstret`, `mcycleh` and `minstreth`.
- **Reference:** Sail `src/cheri_addr_checks.sail:252-268` (`ext_check_CSR`)
  allows only `not(isWrite)` accesses to 0xB00, 0xB02, 0xB80, 0xB82 and
  0xC00-0xC02/0xC80-0xC82. cheriot-ibex has the same exemption
  (`rtl/ibex_decoder.sv:780`), so ibex is not a valid golden here.
- **Expected:** `csrw` to **`0x0b00`**, **`0x0b02`**, **`0x0b80`** and
  **`0x0b82`** without ASR raise mcause **`0x1c`**, mtval **`0x418`** (PCC,
  ASR violation).
- **Observed:** No trap; the write is performed.
- **Controls:** `csrr 0x0b00` (no trap) and `csrr 0x0300` (ASR fault) match
  Sail. The **same ELF passes all 8 cases on Sail**.
- **Suggested fix:** Qualify `csr_cheri_always_ok` with a read-only access
  (CSRRS/CSRRC with rs1 = x0, or their immediate forms with uimm = 0). Limit
  the allowed addresses to the Sail list.
- **Reproducer:** `sim/tests_2/rtl_bug_csr_asr_allowlist/` cases 0-3.
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/rtl_review5_z93jS7Dl/asr/rtl_csr_asr_xde901rz/`
  (`build{0,1,2}_{default,delayed}`, `sail/`). Found by the CSR allow-list
  differential test `/home/scratch/fortress/kunyanliu/kudu_temp/rtl_review5_z93jS7Dl/asr/run2/`.

## KUDU-018: Unimplemented CSR without ASR reports a CHERI fault

- **Status:** Fixed in `85bbd3f`; reproduced on `6378440` on 2026-10-19
  (conf1, conf2, conf3). Fix: `csr_access_o` is no longer masked by the ASR
  error, and the exception priority is misalignment > CHERI fault > bus/PMP
  error > illegal CSR > ASR fault. `illegal_csr_insn_o` covers existence,
  read-only writes and privilege; SCRs have no privilege check, as in Sail.
- **Fix verification (2026-10-28, RTL identical to `85bbd3f`):**
  - `rtl_bug_csr_asr_allowlist` (PMODE=1), conf0-3 × d/ws/wb: 12/12 PASS.
  - New scope test `asr_scope` (14 cases, scratch, in
    `/home/scratch/fortress/kunyanliu/kudu_temp/rawwaw_20261026_222811/mirror/tests/`): 12/12 PASS. Cases:
    unimplemented SCRs 27 and 5, DEPCC/DSCRATCH0C/DSCRATCH1C outside debug
    mode, write to read-only `mvendorid`, U-mode privileged CSRs and SCR,
    plus ASR controls. Expected values follow Sail (SCR existence before ASR;
    `check_CSR` before ASR).
  - Pre-fix build: `asr_scope` fails 10 of 14 cases; the allowlist
    reproducer fails cases 4-5.
  - Full regression 732/732 OK (`/home/scratch/fortress/kunyanliu/kudu_temp/fullregr_k041v2_20261028_181557`).
- **Location:** `rtl/load_store_unit.sv:579` (`csr_access_o` masked by
  `csr_cheri_asr_err`), `rtl/load_store_unit.sv:596`,
  `rtl/cs_registers.sv:309` (`illegal_csr_insn_o` gated by `csr_access_i`).
- **Description:** When PCC lacks ASR, the ASR error suppresses
  `csr_access_o`, so `cs_registers` never flags a non-existent CSR as
  illegal, and the ASR fault wins. The priority is inverted with respect to
  the reference.
- **Reference:** Sail `sail-riscv/model/riscv_insts_zicsr.sail:205-208`
  checks `check_CSR` (existence/privilege) before `ext_check_CSR`.
  cheriot-ibex `rtl/ibex_controller.sv:246-247,257` also gates the ASR
  error with `~illegal_insn_i`.
- **Expected:** `csrr`/`csrw` **`0x0323`** (mhpmevent3, not implemented)
  without ASR raise illegal instruction, mcause **`0x2`**, mtval **0**.
- **Observed:** mcause **`0x1c`**, mtval **`0x418`**. With ASR, Kudu
  correctly raises illegal instruction.
- **Suggested fix:** Compute `illegal_csr_insn` independently of the ASR
  check and give it priority, or gate `csr_cheri_asr_err` with
  `~illegal_csr_insn_i` as ibex does.
- **Reproducer:** `sim/tests_2/rtl_bug_csr_asr_allowlist/` cases 4-5.
- **Evidence:** as KUDU-017.
- **Scope (2026-10-25 review):** the same inverted priority also applies to
  other accesses that should be illegal for reasons other than ASR:
  unimplemented SCRs, DEPCC/DSCRATCH0C/DSCRATCH1C outside debug mode, and
  CSRs that are illegal from U-mode. Each reports a CHERI ASR fault instead
  of an illegal instruction when PCC lacks ASR. Only the unimplemented-CSR
  case has a reproducer.

## KUDU-019: minstret never increments

- **Status:** Open; reproduced on `6378440` on 2026-10-19 (conf1, conf2,
  conf3).
- **Location:** `rtl/kudu_top.sv:660-672` ties `instr_ret_i`,
  `instr_ret_compressed_i`, `mem_load_i`, `mem_store_i`, `jump_i`,
  `branch_i`, `iside_wait_i`, `mul_wait_i`, `div_wait_i` and related
  inputs of `cs_registers` to `1'b0`. `rtl/cs_registers.sv:1255` drives the
  minstret increment from `instr_ret_i`.
- **Description:** `minstret`/`minstreth` are readable and writable but
  never count. Any event-driven `mhpmcounter` would be frozen for the same
  reason. Only `mcycle` counts.
- **Reference:** Sail `sail-riscv/model/riscv_step.sail:26-33` increments
  minstret for every retired instruction (except one that writes minstret)
  unless `mcountinhibit.IR` is set.
- **Expected:** `minstret = 0`, read, `minstret = 5`, read, `csw`, read
  gives **0, 5, 7**.
- **Observed:** **0, 5, 5** with default and delayed memory.
- **Suggested fix:** Drive `instr_ret_i` (and the compressed/spec variants)
  from the commit stage's retire count. Kudu is dual-issue, so the counter
  must also accept an increment of 2 per cycle. Drive the other event
  inputs, or make the corresponding counters read-only zero.
- **Reproducer:** `sim/tests_2/rtl_bug_minstret_write_order/` (PMODE=1).
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/rtl_review5_z93jS7Dl/csr/rtl_minstret_write_order_20261019_124955_1688594/`
  (conf1), `..._125030_1689884/` (conf2), `..._125056_1691131/` (conf3).
  Each has `default/` and `delayed/` failing and `sail/` passing.

---

## KUDU-020: misa reads back with bits 31:9 set

- **Status:** Fixed in `d88c674`; found on `6378440` on 2026-10-19 (conf1,
  conf2, conf3) while checking PMODE=0 against the RV32 build.
- **Location:** `rtl/cs_registers.sv:133`
  `localparam int unsigned RV32IEnabled = ~CHERIoTEn;` and its use at line
  148, `(RV32IEnabled << 8)`.
- **Description:** `CHERIoTEn` is a 1-bit parameter, but the assignment
  context is 32 bits, so it is zero-extended *before* the `~`.
  `RV32IEnabled` is therefore `0xFFFFFFFF` (RV32 build) or `0xFFFFFFFE`
  (CHERIoT build). After `<< 8`, every misa bit from 31 down to 9 is set,
  including MXL (reads 3, i.e. RV128) and a long list of unimplemented
  extensions. The PMODE mask at lines 287-293 then rewrites only bits 23, 8
  and 4. As a result, X (bit 23) is 1 on the RV32 build but 0 on the
  CHERIoT build at PMODE=0. This is the only architectural difference found
  between those two configurations (see the equivalence section below).
- **Reference:** cheriot-ibex `rtl/ibex_cs_registers.sv:172` uses
  `(32'(!RV32E) << 8)`. Sail sets MXL=1 (RV32) and only the implemented
  extension bits (cheriot-sail `sail-riscv/model/riscv_sys_control.sail:485-505`,
  `init_sys`).
- **Expected** (every KuduCfg: RV32A = RV32B = RV32M = 1, U-mode present):
  RV32 build or PMODE=0 **0x40101107**; PMODE=1 **0x40901017**.
- **Observed:** RV32 build **0xffffff07**; CHERIoT build PMODE=0
  **0xff7fff07**; PMODE=1 **0xfffffe17**. Sail reads **0x40a0103e** for the
  PMODE=1 ELF. Its MXL and reserved bits are correct; its A/U/D/F/V bits
  follow Sail's own configuration.
- **Fix (`d88c674`, `rtl/cs_registers.sv:133`):**
  `RV32IEnabled = {31'h0, ~CHERIoTEn}` (`CHERIoTEn` is a `parameter bit`,
  so the inversion is 1 bit wide).
- **Verification on `d88c674`:** `rtl_bug_misa_value` reads **0x40101107** on the
  RV32 build and at PMODE=0, and **0x40901017** at PMODE=1 (conf1 only).
- **Reproducer:** `sim/tests_2/rtl_bug_misa_value/` (`MISA VALUE ... FAIL`
  while the bug is present; builds as RV32 or CHERIoT, see above).
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/pmode0_equiv_20261019_143106/runs/c{1,2,3}/rtl_bug_misa_value.*`
  (RV32 build and PMODE=0) and `.../p1/sim.log` (PMODE=1).

---

## KUDU-021: ebreak in debug mode does not re-enter debug cleanly

- **Status:** Fixed in `802d481`; reproduced on `6378440` on 2026-10-20.
- **Location:** `rtl/issuer.sv:775` selects the `DEBUG` special case for
  `ebreak & dcsr.ebreakm` without checking `debug_mode_q`, and `DEBUG` sets
  `debug_csr_save_o`. `rtl/cs_registers.sv:768-773` then rewrites
  `dcsr.cause`/`dcsr.prv` and `:1744-1749` rewrites DEPC. With
  `ebreakm = 0` the same `ebreak` goes down the `SYSCTL` path to mtvec.
- **Reference:** Debug Spec v0.13.2 p.39: an EBREAK executed in Debug Mode
  "halts the hart again but without updating dpc or dcsr"
  cheriot-ibex `ibex_controller.sv:768-783` re-enters (`DBG_TAKEN_ID`)
  with `csr_save_cause_o = 0` whenever `debug_mode_q`, regardless of
  ebreakm.
- **Expected:** both cases re-enter the ROM at `DmHaltAddr`; dpc stays at the
  halted PC and `dcsr.cause` stays 3 (haltreq).
- **Observed:** `ebreakm = 1`: dpc becomes **0x84000070** (the ROM's own
  `ebreak`), `dcsr.cause` becomes 1. A debugger that resumes after a
  program buffer (which ends in `ebreak`) would `dret` back into the ROM.
  `ebreakm = 0`: no re-entry; the M-mode handler at mtvec runs in debug
  mode (`mtvec_hits = 1`).
- **Fix (`802d481`):** `rtl/issuer.sv:773-775` adds
  `ebreak_enter_debug = ~debug_mode_q & ... & ebrk & debug_ebreak`, so the
  `DEBUG` special case (and `debug_csr_save_o`) is used only to enter debug
  mode. In debug mode an `ebreak` takes the `SYSCTL` path, whose target is
  now `debug_mode_q ? DmHaltAddr : mtvec` (`:835`). The debug cause uses
  `ebreak_enter_debug` (`:957`).
- **Verification on `802d481`:** D1a and D1b pass, default and delayed
  memory: dpc stays **0x800006ee**, cause stays 3, no mtvec entry
  (`/home/scratch/fortress/kunyanliu/kudu_temp/user_rtl_review_20261020_180424/runs2/user_dbgmode*/sim.log`). Ordinary `ebreak` traps
  outside debug mode are unchanged: `rv32_test_csr` (PMODE=0) and
  `isa_test_csr` (PMODE=1) produce traces identical to `6378440`.
- **Remaining behaviour (not a bug):** in debug mode the `SYSCTL` `ebreak`
  still asserts `csr_save_cause_o`. mcause, mepc, mtval and mstatus are
  skipped (`debug_mode_i`). PCC is reloaded from MTCC
  (`rtl/cs_registers.sv:1860`), as on first entry, and an invalid MTCC
  sets `cheri_fatal_err_q` (`:1959`).
- **Reproducer:** `sim/tests_2/rtl_bug_debug_mode/`, cases `D1a`, `D1b`.
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/dbg_mode_20261020_112923/runs/{c1,c2,c3,c1_memdly}/sim.log` (conf1/2/3 default, conf1 delayed memory; identical verdicts; `run_all.sh` reruns them).

---

## KUDU-022: exceptions in debug mode jump to mtvec

- **Status:** Fixed in `d88c674`; reproduced on `6378440` on 2026-10-20.
- **Location:** `rtl/issuer.sv:813-817` (`EXEC` case) always sets
  `special_pc_q` to mtvec. `csr_save_cause_o` also loads PCC from MTCC
  (`rtl/cs_registers.sv:1860-1868`). Kudu has no debug-exception address:
  `CFG` has only `DmHaltAddr`; `DmExceptionAddr` in `rtl/if_stage.sv:19`
  is unused.
- **Reference:** cheriot-ibex `ibex_controller.sv:730` selects
  `EXC_PC_DBG_EXC` (`dm_exception_addr`) in debug mode, so control returns
  to the debug module rather than to M-mode software.
- **Observed:** an illegal instruction (`0xffffffff`) in the debug ROM runs
  the test's M-mode handler, still in debug mode (it can `dret`). mcause,
  mepc, mtval and mstatus are correctly left unchanged.
- **Fix (`d88c674`):** `kudu_cfg_t.DmExcAddr` (0x84000008) is passed to the
  issuer, and both the issue-time `EXEC` case (`rtl/issuer.sv:820`) and the
  commit-error `CMT_FLUSH` path (`:807`) select
  `debug_mode_q ? DmExcAddr : mtvec`. The KUDU-021 ebreak case already
  re-enters `DmHaltAddr`.
- **Verification on `d88c674`:** `D2` passes (one DmExcAddr entry, no mtvec
  handler). Exceptions outside debug mode are unchanged:
  `rtl_bug_trap_csr_values`, `rtl_bug_rtype_rev8_reserved`,
  `rtl_bug_mret_asr_mtval`, `dbg_test1` and the issuer test give the same
  results as before, and `rv32_test_csr`/`isa_test_csr` traces are
  identical. The test ROM gained an exception entry at `+8` for this
  (`sim/tests_2/rtl_bug_debug_mode/debug_rom.S`; `D2` also checks `mb[12]`).
- **Reproducer:** `sim/tests_2/rtl_bug_debug_mode/`, case `D2`.
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/dbg_mode_20261020_112923/runs/{c1,c2,c3,c1_memdly}/sim.log` (conf1/2/3 default, conf1 delayed memory; identical verdicts; `run_all.sh` reruns them).

---

## KUDU-023: illegal CSR accesses do not trap in debug mode

- **Status:** Fixed in `38d1ad3` (`rtl/load_store_unit.sv:598`:
  `csr_err = is_csr & (illegal_csr_insn_i | csr_cheri_asr_err)`); `D3`
  passes. Reproduced on `6378440` on 2026-10-20 (PMODE=1). The same gate
  applied at PMODE=0 and on the RV32 build (static review).
- **Location:** `rtl/load_store_unit.sv:598`
  `csr_err = ~debug_mode_i & is_csr & (illegal_csr_insn_i | csr_cheri_asr_err)`
  masks the illegal-CSR error together with the ASR error.
- **Reference:** cheriot-ibex `ibex_controller.sv:257` masks only the ASR
  error in debug mode; illegal CSR accesses still raise an
  illegal-instruction exception.
- **Observed:** `csrr x7, mtvec` (illegal at PMODE=1) returns the mtvec
  address **0x80000758**; `csrr x7, 0x3ff` (unimplemented) returns 0; no
  exception in either case.
- **Suggested fix:** `csr_err = is_csr & (illegal_csr_insn_i | (~debug_mode_i & csr_cheri_asr_err))`
  (the ASR term already includes `~debug_mode_i`).
- **Reproducer:** `sim/tests_2/rtl_bug_debug_mode/`, case `D3`.
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/dbg_mode_20261020_112923/runs/{c1,c2,c3,c1_memdly}/sim.log` (conf1/2/3 default, conf1 delayed memory; identical verdicts; `run_all.sh` reruns them).

---

## KUDU-024: CLC skips load-permission stripping in debug mode

- **Status:** Fixed in `d88c674` (was a spec deviation). cheriot-ibex behaves the same
  (`cheri_ex.sv:254`), but the Kudu debug-mode requirement is that only
  CHERI trap generation is disabled and data processing is unchanged.
- **Location:** `rtl/ls_pipeline.sv:217`
  `clrperm = debug_mode_i ? 4'h0 : {lc_ctag, 1'b0, lc_csdlm, lc_cglg}`.
- **Observed:** with a valid stored capability, CLC through an authority
  without MC returns tag **1** (normal mode: 0); CLC through an authority
  without LM returns perms **0x7f** (normal mode: **0x63**, SD and LM
  stripped).
- **Fix (`d88c674`):** `clrperm = {lc_ctag, 1'b0, lc_csdlm, lc_cglg}`
  unconditionally (`rtl/ls_pipeline.sv:217`). Kudu now differs from
  cheriot-ibex here, by design.
- **Verification on `d88c674`:** `D4` passes (no MC: tag 0; no LM: perms 0x63),
  default and delayed memory.
- **Related observation (not logged as a bug):** debug entry is a
  `csr_save_cause`, so PCC in debug mode is MTCC (`rtl/cs_registers.sv:1860`).
  Case `D5` with a 256-byte MTCC shows `auipcc` in the ROM yielding base
  0x83ffff58, length 0x100, tag 0, rather than the halted PCC (root). This
  matches cheriot-ibex (`ibex_cs_registers.sv:1871-1889`).
- **Reproducer:** `sim/tests_2/rtl_bug_debug_mode/`, cases `D4`, `D5` (INFO).
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/dbg_mode_20261020_112923/runs/{c1,c2,c3,c1_memdly}/sim.log` (conf1/2/3 default, conf1 delayed memory; identical verdicts; `run_all.sh` reruns them).

---

## KUDU-025: csrw dpc/dscratch0/dscratch1 is silently dropped at PMODE=1

- **Status:** Fixed in `38d1ad3` (`rtl/cs_registers.sv:511-522`)
  (second suggested option): at PMODE=1 the RV32 dpc/dscratch0/dscratch1
  encodings are illegal and, with the KUDU-023 fix, trap to `DmExcAddr`.
  Debug code must use DEPCC/DSCRATCHC0/DSCRATCHC1 (SCR 24/25/26). `P1` now
  checks that `csrr`/`csrw` of dpc and dscratch1 each trap (4 `DmExcAddr`
  entries) and leave DEPCC/DSCRATCHC1 unchanged; it passes. Reproduced on
  `6378440` on 2026-10-20.
- **Location:** `rtl/cs_registers.sv:1651` (`rv32_depc_wr`), `:1755`,
  `:1766` require `~cheri_pmode`; the read side (`:512-522`) and
  `illegal_csr` only check `debug_mode_i`. MTVEC/MEPC, by contrast, are
  illegal at PMODE=1 (`:363,369`).
- **Reference:** cheriot-ibex `ibex_cs_registers.sv:710-713` writes
  depc/dscratch0/dscratch1 from RV32 CSR instructions in either mode.
- **Observed:** in debug mode, `csrw dpc, dpc+4` leaves dpc unchanged
  (**0x800006ee**); `csrw dscratch1, 0x1234` leaves dscratch1 unchanged.
  Neither traps. A debugger that sets dpc with `csrw` (abstract command or
  program buffer) silently fails.
- **Suggested fix:** either update the address with `legalize_scr`/
  `set_address` as at PMODE=0, or mark the RV32 encodings illegal at
  PMODE=1 like MTVEC/MEPC.
- **Reproducer:** `sim/tests_2/rtl_bug_debug_mode/`, case `P1`.
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/dbg_mode_20261020_112923/runs/{c1,c2,c3,c1_memdly}/sim.log` (conf1/2/3 default, conf1 delayed memory; identical verdicts; `run_all.sh` reruns them).

---

## KUDU-026: halt request with an empty IR saves a stale dpc

- **Status:** Fixed in `802d481`; reproduced on `6378440` on 2026-10-20.
- **Location:** `rtl/issuer.sv:727` raises `handle_debug` on `debug_req_i`
  without requiring `ir_valid_i[0]`. The `DEBUG` branch at `:943` then
  saves `csr_exc_info_o.pc = ir0_dec.pc` unconditionally. After a redirect
  (taken branch, `cjalr`) the IR is flushed, so `ir0_dec.pc` is the stale PC
  of a wrong-path slot. The interrupt path at `:979` already uses
  `ir_valid_i[0] ? ir0_dec.pc : ir0_nxt_pc_q`.
- **Reference:** Debug Spec v0.13.2 (`dpc`): on a halt request, dpc is the
  address of the next instruction to execute. cheriot-ibex
  `ibex_controller.sv:656-666` (`DBG_TAKEN_IF`) saves the PC in IF
  (`csr_save_if_o`), which is always the architectural next PC.
- **Observed:** the request lands just after `cjalr c14, c12` / taken
  `bnez`. dpc is the first wrong-path instruction (**base + 8**) instead
  of the target (**+16**) or the branch (**+4**). After `dret` both
  wrong-path `addi x15, 0x400` execute and then fall into the target, so the
  function returns **0x8f0** instead of 0xf0. With memory delays, the same
  window also hits `n=1` (dpc = second wrong-path instruction, return
  0x4f1).
- **Fix (`802d481`, `rtl/issuer.sv:949`):**
  `csr_exc_info_o.pc = ir_valid_i[0] ? ir0_dec.pc : ir0_nxt_pc_q;`
  All 24 `I1` variants pass on `802d481`, default and delayed memory
  (`/home/scratch/fortress/kunyanliu/kudu_temp/user_rtl_review_20261020_180424/runs2/user_issuer*/sim.log`).
- **Reproducer:** `sim/tests_2/rtl_bug_issuer_debug/`, case `I1` (24
  variants: `n` = 0..11 counted instructions before a `cjalr` or a branch).
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/issuer_dbg_20261020_122123/runs3/*/sim.log`
  (`run_all2.sh` reruns them). Three shadow RTL trees were built (conf1)
  with production RTL untouched:
  - `shadow0`: unmodified copy of `rtl/` (identical to `6378440`).
  - `shadowA`: KUDU-012 only (`handle_irq` gated by `~debug_mode_q`).
  - `shadowB`: all suggested fixes for KUDU-003 (stepped WFI),
    KUDU-012, and KUDU-026..030 (`shadowB/rtl/issuer.sv`,
    `shadowB/rtl/cs_registers.sv`; built as `build_shadowB2`). The
    KUDU-021 fix was added later (`build_shadowB3`, `run_b3.sh`).

  | Case | shadow0 (`6378440`) | shadowA | shadowB | `rtl/` at `802d481` |
  |---|---|---|---|---|
  | I1 (default / delayed) | 2 FAIL / 1 FAIL | 2 FAIL / 1 FAIL | PASS | PASS |
  | I6 | FAIL | FAIL | PASS | PASS |
  | I2 | FAIL | FAIL | PASS | FAIL |
  | I4 | FAIL | FAIL | PASS | FAIL |
  | I3 | hangs (KUDU-012) | FAIL (IRQ taken) | PASS | hangs (KUDU-012) |
  | I5 | not reached | hangs | PASS | not reached |
  | Summary | timeout | timeout | `SUMMARY PASS` | timeout |

---

## KUDU-027: debug-mode entry overwrites MEPC

- **Status:** Fixed in `802d481`; reproduced on `6378440` on 2026-10-20
  (PMODE=1). The PMODE=0 branch had the same condition and is fixed by the
  same change.
- **Location:** `rtl/cs_registers.sv:1674,1677` write MEPC on
  `csr_save_cause_i & ~debug_mode_i`. Debug entry asserts `csr_save_cause_i`
  (with `debug_csr_save_i`) while `debug_mode_i` is still 0, so every halt
  (halt request, step, trigger, `ebreak`) copies the dpc into MEPC/MEPCC.
  The mcause/mtval/mstatus updates (`:763-787`) are correctly skipped for
  `debug_csr_save_i`.
- **Reference:** Debug Spec v0.13.2 (Debug Mode entry): only dpc and dcsr
  are updated. cheriot-ibex `ibex_cs_registers.sv:777-785` updates
  depc/dcsr only when `debug_csr_save_i`, and `:1913` writes `mepc_cap` only
  on `csr_save_cause_i & ~debug_csr_save_i & ~debug_mode_i`.
- **Observed:** MEPCC is set to **0x80001478**, then a halt request is
  taken in a delay loop at 0x80001464. After `dret`, MEPCC reads
  **0x80001464** (the dpc). A debugger halt inside a trap handler, before
  `mret`, sends the handler back to the halt point instead of the
  interrupted code.
- **Fix (`802d481`):** `& ~debug_csr_save_i` added to both MEPC write
  conditions (`rtl/cs_registers.sv:1674,1677`). `I6` passes on `802d481`.
  In `dbg_test1`, the debug ROM's `csrr mepc` now reads the unchanged MEPC
  (0) instead of the dpc; the test still passes.
- **Reproducer:** `sim/tests_2/rtl_bug_issuer_debug/`, case `I6`.
- **Evidence:** as KUDU-026.

---

## KUDU-028: stepping a trapping instruction runs the handler's first instruction

- **Status:** Fixed in `d290cd0`: a stepped instruction is always handled as a
  special case (`STEP`), and `step_req_q` is set when it is issued or traps
  (`CMT_FLUSH`/`ISSUE_SPECIAL`), so debug entry happens before the handler
  executes. Reproduced on `6378440` and `802d481` on 2026-10-20.
- **Fix verification (2026-11-10):** checked on `rtl/` identical to `d290cd0`
  (only comments differed). See the `d290cd0` note at the top of this file.
- **Location:** `rtl/issuer.sv:898` arms `single_step_trap_q` only on
  `ir0_issued`. An instruction that traps at decode (illegal instruction,
  fetch fault, PCC fault, CJALR error) goes through `ISSUE_SPECIAL` with
  `special_case_q == EXEC` and is never issued. The step halt therefore
  happens after the first handler instruction.
- **Reference:** Debug Spec v0.13.2 (`dcsr.step`): "If the instruction does
  not complete due to an exception, the hart will immediately enter Debug
  Mode before executing the trap handler". cheriot-ibex flushes the pipeline (`FLUSH`), then goes to
  `DBG_TAKEN_IF` (`ibex_controller.sv:880-888`) before the handler fetches.
- **Observed:** stepping `.word 0xffffffff`: one trap (mcause 2), then the
  second halt has dpc = handler + 4 (**0x800015bc**, handler at
  **0x800015b8**). The first handler instruction ran with the step still
  pending.
- **Suggested fix (shadow B):** also set `single_step_trap_q` when
  `ctrl_fsm_cs[CSM_ISSUE_SPECIAL] & (special_case_q == EXEC)`.
- **Reproducer:** `sim/tests_2/rtl_bug_issuer_debug/`, case `I2`.
- **Evidence:** as KUDU-026.

---

## KUDU-029: interrupts are taken while single-stepping

- **Status:** Fixed in `d290cd0` (`handle_irq` masked by `~debug_step_i`).
- **Fix verification (2026-11-10):** checked on `rtl/` identical to `d290cd0`
  (only comments differed). See the `d290cd0` note at the top of this file.
  Reproduced on shadow build A (KUDU-012 fixed) on 2026-10-20. On
  `6378440` and `802d481` the same case first hits KUDU-012 (the interrupt
  is taken inside the debug ROM) and hangs.
- **Location:** `rtl/issuer.sv:726`
  `handle_irq = irq_pending_i & csr_mstatus_mie_i` is not masked by
  `debug_single_step_i`, and `rtl/cs_registers.sv:703` hardwires
  `dcsr.stepie = 0`.
- **Reference:** Debug Spec v0.13.2 (`dcsr.stepie = 0`): "Interrupts are
  disabled during single stepping". cheriot-ibex gives debug entry priority
  over `handle_irq` (`ibex_controller.sv:599-610`), so a stepped instruction
  is never preempted by an interrupt.
- **Observed (shadow A):** the step target is entered with MEIP pending
  and `mstatus.MIE = 1`. The interrupt is taken (`irqs = 1`) and the second
  halt is in the handler (dpc **0x800015bc**) instead of target + 4
  (**0x80001518**).
- **Suggested fix (shadow B):** `handle_irq = ~debug_mode_q &
  ~debug_single_step_i & irq_pending_i & csr_mstatus_mie_i` (the
  `~debug_mode_q` term is the KUDU-012 fix).
- **Reproducer:** `sim/tests_2/rtl_bug_issuer_debug/`, case `I3` (needs
  `+INTR_INTVL=1`).
- **Evidence:** as KUDU-026.

---

## KUDU-030: stepped ebreak reports cause STEP instead of EBREAK

- **Status:** Fixed in `d290cd0` (cause order is now trigger > EBREAK >
  HALTREQ > STEP).
- **Fix verification (2026-11-10):** checked on `rtl/` identical to `d290cd0`
  (only comments differed). See the `d290cd0` note at the top of this file.
- **History:** reproduced on `6378440` and `802d481` on
  2026-10-20. `802d481` changed the last cause test to
  `ebreak_enter_debug`, but STEP is still checked first.
- **Location:** `rtl/issuer.sv:945-952` checks `debug_single_step_i`
  before `debug_ebreak`, so an `ebreak` with `dcsr.ebreakm = 1` executed
  under `dcsr.step = 1` sets `dcsr.cause = 4`. dpc is correct (the
  `ebreak`).
- **Reference:** Debug Spec v0.13.2 (`dcsr.cause`): cause priority is trigger
  (2) > EBREAK (1) > haltreq (3) > step (4). cheriot-ibex
  (`ibex_controller.sv:695-706`, `DBG_TAKEN_ID`) reports
  `DBG_CAUSE_EBREAK` for an `ebreak` with forced entry.
- **Observed:** `cause2 = 4` with dpc = the `ebreak`.
- **Suggested fix (shadow B):** test
  `ir_valid_i[0] & ir0_dec.sysctl.ebrk & debug_ebreak` before the step
  check.
- **Reproducer:** `sim/tests_2/rtl_bug_issuer_debug/`, case `I4`.
- **Evidence:** as KUDU-026.

**Issuer review notes (2026-10-20, not bugs).** The register hazard and
forwarding logic was reviewed and no defects were found:
- `reg_wrsv_q` gives set priority over clear and is cleared on flush.
- With AllowWaW, a newer writer cancels the older forward entry.
- Commit is in order.
- The dcache forwards only integer hits.
- A trvk tag clear in the same cycle as a register write is harmless,
  because CHERI writers stall on the trsv hazard.

Benign or dead items:
- `csr_mispredict_o` operator precedence is harmless.
- `special_pc_q <= ir0_jalr_target_i` on DECODE -> WAIT_CMT0 is dead.
- ir1 duplicates the trsv/RaW checks.
- If `irqs_i` drops one cycle before ISSUE_SPECIAL, mcause defaults to
  the timer interrupt.
- IRQ takes priority over SYSCTL, which is architecturally legal.

## KUDU-031: misaligned LR/SC/AMO reach the bus on the RV32 build

- **Status:** Fixed in `85bbd3f`; found in the full review of `7028fb3`
  (2026-10-25). Affected only the RV32-only build (`simv32`); the CHERIoT
  build at PMODE=0 was correct. Fix: `lsu_if.sv` copies `lschk_err` into
  `req_dly_tmp` in both builds; the SLC tag clear (`wdata[MEM_TAG]`) stays
  CHERIoT-only.
- **Fix verification (2026-10-28, RTL identical to `85bbd3f`):**
  - `rtl_bug_misaligned_sc_rv32` on `simv32` and on `simv` at PMODE=0,
    conf0-3 × d/ws/wb: 24/24 PASS. Pre-fix `simv32`: 8/8 FAIL.
  - A first version applied the SLC tag clear on RV32 too, where `MemW` is
    32; VCS warned "Select index out of bounds". The committed version has
    no warning.
  - Full regressions 732/732 OK (`/home/scratch/fortress/kunyanliu/kudu_temp/fullregr_k031v2_20261028_175745`,
    `/home/scratch/fortress/kunyanliu/kudu_temp/fullregr_k041v2_20261028_181557`).
- **Location:** `rtl/lsu_if.sv:66-74`. Only the `CHERIoTEn` branch copies
  `lschk_err` (which carries the atomic misalignment check added in
  `7028fb3`) into `req_dly_tmp`; the RV32 branch passes `req_dly_q` through
  unchanged.
- **Description:** On `simv32` a misaligned `lr.w`/`sc.w`/AMO is not
  blocked: the access is split and sent to memory. A misaligned `sc.w`
  after a matching `lr.w` writes memory, and a trapping misaligned `lr.w`
  still sets the reservation, so a following aligned `sc.w` succeeds.
- **Reference:** RV32A: misaligned LR/SC/AMO raise an address-misaligned
  (or access) exception and have no memory effect. KUDU-007 (fixed in
  `7028fb3`) for the CHERIoT build.
- **Expected:** `sc.w` to `X+2`: mcause **6**, rd and memory unchanged
  (`X = 0x11223344`). `lr.w X+2` (trap) then `sc.w X`: SC fails, rd = 1.
- **Observed:** `X = 0xccdd3344` after `sc.w X+2`; `lr.w X+2; sc.w X` gives
  rd = 0 and `X = 0xaabbccdd`.
- **Suggested fix:** apply the `lschk_err` assignment in both branches (keep
  the SLC tag clear CHERIoT-only).
- **Reproducer:** `sim/tests_2/rtl_bug_misaligned_sc_rv32/` (4 failing cases on
  `simv32`; passes on `simv` at PMODE=0).
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/fullreview_20261024_234209/lsu/run_lsu_rv32/`.

## KUDU-032: trapping AMO overwrites rd

- **Status:** Fixed in `1567152`; found 2026-10-25. The AMO read phase no
  longer writes rd (`cmplx_unit.sv:163`, `rf_we` only in `AMO_WRITE`); the
  LSU holds the read data in `amo_rdata_q` (`load_store_unit.sv:656-668`)
  and returns it as the write-phase response (`:691-692`), so rd is written
  only when the whole AMO completes without a fault.
- **Fix verification (2026-10-29):** `rtl_bug_amo_cheri_fault` passes 8/8
  (default and delayed memory), including the write-phase bus-error case.
  A random self-checking AMO stress generator (all nine AMO ops, aq/rl,
  rd = x0/rs1/rs2, producer/consumer hazards, CHERI permission/bounds/tag
  faults, misaligned and unmapped AMOs, random data bus errors with retry,
  random interrupts) checks rd, memory, trap CSRs and MPIE. 48 tests x 3
  modes (PMODE=1, PMODE=0, RV32 build) x default/delayed memory: 144/144
  pass on `1567152` (6462 traps, 7542 interrupts, 2547 AMO bus errors); all
  36 runs on `85bbd3f` fail with wrong rd values. Generator and runs:
  `/home/scratch/fortress/kunyanliu/kudu_temp/amo_stress_20261029_155513/` (`gen/gen_amo.py`, `results.txt`).
- **Location:** `rtl/cmplx_unit.sv:162-166` (the read phase has
  `rf_we = 1`, `is_load = 1`), `rtl/cheri_pkg.sv:1048-1049` (the read phase
  is checked for load permission only; store permission is checked only in
  the write phase).
- **Description:** An AMO is executed as a read request that writes rd,
  followed by a write request. A fault found in the write phase (missing SD
  permission, or a bus error on the write) is raised after rd has already
  been written.
- **Reference:** Sail `src/cheri_addr_checks.sail:198-201` checks LD and SD
  (and the other capability checks) before any access, so a faulting AMO
  has no architectural effect. Precise exceptions: a trapping instruction
  must not write rd.
- **Expected:** `amoswap.w`/`amoadd.w` with an LD-only capability: mcause
  **0x1c**, mtval **0x1d3**, rd and memory unchanged.
- **Observed:** mcause and mtval are correct, but rd = **0x11223344** (the
  old memory value).
- **Suggested fix:** check both LD and SD permissions in the read phase for
  AMOs (`amo_flag`), or suppress the rd write until the write phase
  completes without error.
- **Reproducer:** `sim/tests_2/rtl_bug_amo_cheri_fault/`, `amo-rd` cases.
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/fullreview_20261024_234209/lsu/run_cheri_p1/`.

## KUDU-033: stale load data after a store spanning two words

- **Status:** Fixed in `f61f89d`, with a performance refinement in
  `6e157c3`; fixed together with KUDU-050 (same root cause). The store
  bypass (`byp_data_good`) now excludes `csc`, and a cache hit
  (`rd_data_good`) is refused while the outstanding request
  (`lsu_req_q`) is a capability access, a misaligned access or an SC.
  `6e157c3` added the `lsu_req_q` qualifier, so a load after a completed
  cap/misaligned/SC access hits again. Found 2026-10-25; reproduced on
  all builds and modes.
- **Fix verification (2026-10-28):** see KUDU-050; the
  `rtl_bug_dcache_split_store` reproducer (`dss_r`/`dss_c`) passes
  36/36 runs on `6e157c3` and fails all 12 runs on `991dba4`.
- **Location:** `rtl/dcache.sv:133-134` (`byp_tag_match` compares only the
  previous request's word address), `rtl/dcache.sv:163`
  (`cache_rd_match_ok`), `rtl/dcache.sv:272-277` (the line is invalidated
  only at the store response).
- **Description:** A misaligned `sw`/`sh` (split by `load_store_unit`) or a
  `csc` writes two words, but the dcache tracks only the first. A load of
  the second word that hits in the window before the store response
  forwards the old cached data to its consumers. The load's own retired
  value and a later reload are correct.
- **Expected:** after `sw` of `0xaabbccdd` to `X+2`, a load of `X+4` and a
  dependent `addi` see **0x1111aabb**.
- **Observed:** the consumer sees **0x11111111**.
- **Suggested fix:** treat any store that covers the second word (misaligned
  or capability) as a match for both word addresses, or block cache hits
  while such a store is outstanding.
- **Reproducer:** `sim/tests_2/rtl_bug_dcache_split_store/` (`split-store`
  cases; `csc` case at PMODE=1 only).
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/fullreview_20261024_234209/lsu/runs/`.

## KUDU-034: U-mode MRET and WFI are not privileged

- **Status:** Fixed in `546cc56`; found 2026-10-25 by three reviewers.
  `issuer.sv:781-783` adds `ir0_mode_err`: MRET when priv != M, and WFI
  when `mstatus.TW = 1` and priv != M, raise illegal instruction
  (`:791`, `:981`; DRET outside debug mode moved into the same term).
  `mstatus.TW` now reaches the issuer (`kudu_top.sv:365`). At PMODE=1, a
  U-mode MRET without PCC.ASR reports illegal instruction, which takes
  priority over the ASR violation.
- **Fix verification (2026-10-29):** `rtl_bug_umode_priv` passes all cases
  (A, B, and control D: M-mode WFI with TW = 1 does not trap) on `simv32`
  and `simv` at PMODE=0, default and delayed memory
  (`/home/scratch/fortress/kunyanliu/kudu_temp/k034_038b_20261029_190229/`); full regression as noted under
  "Status is judged on the code in `rtl/`".
- **Location:** `rtl/ir_decoder.sv:443-451` (MRET/WFI decode with no
  privilege check), `rtl/issuer.sv:575` (WFI sleep), `rtl/issuer.sv:914`
  (MRET restore), `rtl/kudu_top.sv:634` (`mstatus.TW` is produced by
  `cs_registers.sv:849` but not used).
- **Description:** Kudu implements U-mode (`misa.U = 1`, `mstatus.MPP`
  writable), but MRET executed in U-mode is not illegal: it sets PC = mepc,
  MIE = MPIE and priv = MPP. If MPP = M (for example set up by a debugger
  before `dret`), U-mode code raises itself to M-mode. WFI in U-mode with
  `mstatus.TW = 1` sleeps instead of trapping. At PMODE=1 the MRET ASR check
  partly hides the MRET case.
- **Reference:** Privileged spec: MRET is illegal below M-mode; WFI in
  U-mode with TW = 1 raises illegal instruction. Sail
  (`riscv_insts_base.sail`, MRET/WFI); cheriot-ibex `illegal_umode`
  (`ibex_controller.sv:241-243`).
- **Expected:** mcause **2** at the `mret` in U-mode (case A), and at the
  `wfi` in U-mode with TW = 1 (case B).
- **Observed:** A: no trap; MRET jumps back to mepc and the U-mode code runs
  twice. B: no trap; the WFI wakes on the pending interrupt.
- **Suggested fix:** decode MRET, and WFI when TW = 1, as illegal when the
  current privilege is not M.
- **Reproducer:** `sim/tests_2/rtl_bug_umode_priv/`, cases A and B (RV32,
  PMODE=0, needs `+INTR_INTVL=4`).
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/fullreview_20261024_234209/issuer/`,
  `.../frontend/run_umode/`.

## KUDU-035: ECALL in debug mode goes to mtvec

- **Status:** Fixed in `d290cd0` (ECALL in debug mode targets `DmExcAddr`);
  found 2026-10-25. The KUDU-022 fix (`d88c674`) covered other exceptions in
  debug mode but not ECALL.
- **Fix verification (2026-11-10):** checked on `rtl/` identical to `d290cd0`
  (only comments differed). See the `d290cd0` note at the top of this file.
- **Location:** `rtl/issuer.sv:834` (the ECALL arm always loads
  `special_pc_q` with mtvec).
- **Description:** The KUDU-022 fix sends a debug-mode `ebreak` to
  `DmHaltAddr` (`issuer.sv:833`) and other debug-mode exceptions to
  `DmExcAddr` (`:807`, `:820`), but ECALL still jumps to mtvec. An `ecall`
  in the debug ROM therefore runs the M-mode trap handler while still in
  debug mode. mcause and MEPCC are not updated (`cs_registers` gates the
  save on `debug_mode_i`); only the target is wrong.
- **Reference:** Debug Spec v0.13.2 section 4.1: an exception in debug mode
  does not update registers and jumps to the debugger's exception handler.
  cheriot-ibex uses `EXC_PC_DBG_EXC` for every exception in debug mode.
- **Expected:** `ecall` in debug mode enters `DmExcAddr` once; the mtvec
  handler does not run; mcause/MEPCC unchanged.
- **Observed:** `dmexc_hits=0 mtvec_hits=1`.
- **Suggested fix:** `special_pc_q <= debug_mode_q ? DmExcAddr : mtvec` for
  ECALL (passes in a scratch build).
- **Reproducer:** `sim/tests_2/rtl_bug_debug_ecall/`, case E1 (E2, an illegal
  instruction in debug mode, is the KUDU-022 control).
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/fullreview_20261024_234209/issuer/`.

## KUDU-036: trapping AMO saves mstatus.MPIE = 0

- **Status:** Fixed in `1567152`; found 2026-10-25. PMODE=1 only.
  `ls_pipeline.sv:196,198,210` set `lsu_req_dec.mie` from
  `csr_mstatus_mie_i` after the complex-unit request is selected.
- **Fix verification (2026-10-29):** the `amo-mpie` cases pass (handler
  mstatus **0x1880**); the AMO stress test also checks MPIE on every trap
  (see KUDU-032).
- **Location:** `rtl/cmplx_unit.sv:161` (the AMO request starts from
  `NULL_LSU_REQ_INFO`, so `mie = 0`), `rtl/ls_pipeline.sv:196`
  (`lsu_req_dec.mie` is set only for non-complex requests and is replaced by
  the complex-unit request), `rtl/cs_registers.sv:782` (at PMODE=1 MPIE is
  taken from the request's `mie`).
- **Description:** At PMODE=1 a load/store exception saves MPIE from the
  `mie` bit carried with the request. AMO requests always carry `mie = 0`,
  so after a trapping AMO, `mret` returns with interrupts disabled.
- **Reference:** Privileged spec: on a trap MPIE gets the old MIE.
- **Expected:** with MIE = 1, a trapping `amoswap.w`/`amoadd.w` leaves
  mstatus **0x1880** in the handler (as `csw` does).
- **Observed:** mstatus **0x1800**.
- **Suggested fix:** set `cmplx_lsu_req_info_o.mie` from
  `csr_mstatus_mie` in `cmplx_unit`, or override it in `ls_pipeline` after
  selecting the complex-unit request.
- **Reproducer:** `sim/tests_2/rtl_bug_amo_cheri_fault/`, `amo-mpie` cases.
- **Evidence:** as KUDU-032.

## KUDU-037: successful SC.W does not update MSHWM

- **Status:** Fixed in `1663deb`; found 2026-10-25 by two reviewers.
  `csr_lsu_wr_req_o` is now generated from the LSU response
  (`rtl/load_store_unit.sv:699-700`): every non-load, non-CSR request that
  completes without error, excluding an SC whose `data_sc_fail_i` is set.
  The memory-side SC status was renamed `data_sc_resp` → `data_sc_fail`.
- **Fix verification (2026-10-28, RTL identical to `1663deb`):**
  - `gen_mshwm.py` extended with LR/SC/AMO: `msa_s1..20` (mixed LR/SC/AMO)
    and `msf_s1..20` (adds failed SCs to a different address inside the
    MSHWMB..MSHWM window; 135 such failed SCs). 480/480 PASS on conf0-3,
    PMODE=1, default and two delayed-memory settings. Pre-fix RTL
    (`6e157c3`, default memory): 80/80 `msa` and 20/20 `msf` (conf1) fail.
    An intermediate fix using only `~is_load` passed `msa` but failed 76/80
    `msf` runs (a failed SC lowered MSHWM).
  - `rtl_bug_sc_mshwm`: 12/12 PASS, including the failed-SC control case.
  - Full regression 732/732 OK (shared with KUDU-016).
- **Location:** `rtl/ls_pipeline.sv:258`: `csr_lsu_wr_req_o` requires
  `~lsu_req_info.rf_we`, which excludes SC (it writes rd).
- **Description:** MSHWM must track every store below the current mark. A
  successful `sc.w` is a store but is never reported to the CSR unit. A
  failed SC writes nothing, so it must not update MSHWM.
- **Reference:** CHERIoT Sail `ext_check_phys_mem_write`
  (`src/cheri_addr_checks.sail:233-240`) updates MSHWM on every memory
  write, including a successful SC.
- **Expected:** after a successful `sc.w` to `block`, MSHWM = **block**.
- **Observed:** MSHWM = **block + 16** (unchanged).
- **Suggested fix:** include successful SC requests (`amo_flag` SC with a
  valid reservation) in `csr_lsu_wr_req_o`, or report the update from the
  SC response.
- **Reproducer:** `sim/tests_2/rtl_bug_sc_mshwm/`.
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/fullreview_20261024_234209/lsu/run_cheri_p1/`.

## KUDU-038: M-mode interrupts blocked in U-mode when MIE = 0

- **Status:** Fixed in `546cc56`; found 2026-10-25. cheriot-ibex has the
  same deviation. `issuer.sv:730`: `handle_irq` now uses
  `mstatus.MIE | (priv != M)`.
- **Fix verification (2026-10-29):** `rtl_bug_umode_priv` case C passes
  and control D (no interrupt in M-mode with MIE = 0) still passes, on
  `simv32` and `simv` at PMODE=0, default and delayed memory; see KUDU-034.
- **Location:** `rtl/issuer.sv:727` (`handle_irq` uses `mstatus.MIE` with no
  privilege term).
- **Description:** M-mode interrupts are globally enabled whenever the hart
  is below M-mode, regardless of `mstatus.MIE`. Kudu always requires MIE = 1.
- **Reference:** Privileged spec 3.1.6.1; Sail `getPendingSet`.
- **Expected:** a pending MEIP (MEIE = 1, MIE = 0) is taken during a
  3000-iteration U-mode loop.
- **Observed:** never taken (`irqs=0`).
- **Suggested fix:** `handle_irq` enable = `mstatus.MIE | (priv != M)`.
- **Reproducer:** `sim/tests_2/rtl_bug_umode_priv/`, case C (case D is the
  M-mode control).
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/fullreview_20261024_234209/issuer/`.

## KUDU-039: odd mepc/dpc after a JALR to an odd target

- **Status:** Fixed in `546cc56`; found 2026-10-25. Replaces the "JALR bit 0"
  row of the unconfirmed table. `branch_unit.sv:71`: `compute_jalr_target`
  clears bit 0, so the latched next PC, mepc and dpc are always even.
- **Fix verification (2026-10-29):** `rtl_bug_jalr_odd_epc` passes on
  `simv32` and `simv` at PMODE=0, default and delayed memory, 3 seeds each
  (12/12; all 12 fail on `1567152`). A scratch PMODE=1 variant (4000
  `cjalr cnull, 0(cs1)` to target + 1, `+INTR_INTVL=3`) reports 0 odd
  mepcc in 6/6 runs; on `1567152` all 6 fail with 48-196 odd mepcc
  (`/home/scratch/fortress/kunyanliu/kudu_temp/k039_20261029_164418/`, `mirror/tests/jalr_odd_c/`).
- **Location:** `rtl/branch_unit.sv:65-72` (`compute_jalr_target` does not
  clear bit 0), `rtl/issuer.sv:875-876` (target latched into
  `ir0_nxt_pc_q`), `rtl/cs_registers.sv:1677-1679` (mepc written without
  legalization).
- **Description:** IF masks bit 0 for the fetch, but the unmasked target is
  kept as the next PC. If an interrupt is taken while the IR is empty after
  such a JALR, the issuer uses that PC as the exception PC and the odd value
  is written to mepc. Debug entry with an empty IR uses the same path
  (`issuer.sv:947`), so dpc can also be odd (not covered by the test).
- **Reference:** RV32I: JALR clears bit 0 of the target. Privileged spec:
  mepc[0] is always 0 (IALIGN = 16); Sail legalizes xepc.
- **Expected:** no interrupt reports an odd mepc.
- **Observed:** 4000 `jalr x0, 0(t0)` with `t0 = target + 1` and
  `+INTR_INTVL=3`: 32 of 546 interrupts (default memory) and 205 of 1083
  (delayed) give mepc = target + 1.
- **Suggested fix:** clear bit 0 in `compute_jalr_target` (passes in a
  scratch build).
- **Reproducer:** `sim/tests_2/rtl_bug_jalr_odd_epc/`, case J1 (RV32,
  PMODE=0).
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/fullreview_20261024_234209/issuer/`.

## KUDU-040: halt request during single step reports cause STEP

- **Status:** Fixed in `d290cd0` (HALTREQ is tested before STEP); found
  2026-10-25 by code review and reproduced.
- **Fix verification (2026-11-10):** checked on `rtl/` identical to `d290cd0`
  (only comments differed). See the `d290cd0` note at the top of this file.
  cheriot-ibex (`ibex_controller.sv:669-675`) has the same STEP-first order.
- **Location:** `rtl/issuer.sv:951-954` (`debug_single_step_i` is tested
  before `debug_req_i`).
- **Description:** If a halt request is pending when a stepped instruction
  completes, `dcsr.cause` is set to STEP (4). Separate from KUDU-030
  (ebreak vs. step).
- **Reference:** Debug Spec v0.13.2 (`dcsr.cause`): haltreq has priority
  over step.
- **Expected:** stepped store that raises `debug_req` again: second debug
  entry has `dcsr.cause = 3` (HALTREQ), dpc = target + 4.
- **Observed:** `dcsr.cause = 4`; dpc correct.
- **Suggested fix:** test `debug_req_i` before `debug_single_step_i`
  (passes in a scratch build).
- **Reproducer:** `sim/tests_2/rtl_bug_halt_step_cause/`, case H1 (H2 and H3
  are controls).

## KUDU-041: illegal CSR access reports mtval = 0

- **Status:** Fixed in `85bbd3f`; found 2026-10-25. Briefly deferred on
  2026-10-28, then fixed the same day.
  Fix: `lsu_err_mtval = cheri_pmode ? 32'h0 : lsu_req_info_q.insn`, the same
  rule `issuer.sv` uses for other illegal instructions. CSR instructions are
  never compressed, so `insn` is the architectural encoding.
- **Location:** `rtl/load_store_unit.sv:628-630` (the CSR illegal-instruction
  exception sets mtval to 0).
- **Fix verification (2026-10-28, RTL identical to `85bbd3f`):**
  - Reproducer `rtl_bug_csr_mtval_mstatush`, conf0-3 × d/ws/wb memory modes
    (120 jobs). MTVAL checks 72/72 PASS: `simv32`, and `simv` at PMODE=0.
    PMODE=1 mtval = 0 controls and all CTRL checks (264/264) PASS. The only
    failures are the MSTATUSH (KUDU-042, Open) and CDBG (KUDU-043, Deferred)
    checks, as expected.
  - Pre-fix build (`simv32`): MTVAL c0-c2 FAIL (mtval = 0).
  - An intermediate version that reported `insn` unconditionally broke
    PMODE=1 (Sail expects mtval = 0): the `asr_allowlist` and `asr_scope`
    runs failed 12/12, along with the reproducer's CTRL checks. The
    `cheri_pmode` gate fixes this.
  - KUDU-015/018/031 reproducers still PASS on the same build. Full
    regression 732/732 OK (`/home/scratch/fortress/kunyanliu/kudu_temp/fullregr_k041v2_20261028_181557`).
- **Description:** Every other illegal instruction reports the instruction
  bits in mtval; an illegal CSR access (unimplemented CSR, write to a
  read-only CSR) reports 0.
- **Reference:** The privileged spec allows mtval = 0, so this is not a
  spec violation, but cheriot-ibex reports the instruction bits and the
  traces diverge. Kudu is also inconsistent with its own non-CSR illegal
  instructions.
- **Expected (ibex):** `csrr 0x3ff`: mcause **2**, mtval = the encoding.
- **Observed:** mtval **0**.
- **Suggested fix:** pass `insn` as mtval for CSR illegal instructions.
- **Reproducer:** `sim/tests_2/rtl_bug_csr_mtval_mstatush/`, cases c0-c2 at
  PMODE=0. At PMODE=1 mtval = 0 is the expected value (controls c0, c1).
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/fullreview_20261024_234209/csr/runs/`.

## KUDU-042: mstatush is not implemented

- **Status:** Open (low); found 2026-10-25.
- **Location:** `rtl/cs_registers.sv` (no case for 0x310).
- **Description:** `mstatush` (0x310) is defined for RV32 by the privileged
  spec (1.12 and later) and holds MBE/SBE. Accesses raise illegal instruction.
- **Expected:** reads 0; writes ignored (MBE/SBE are 0).
- **Observed:** mcause **2** on `csrr`/`csrw`.
- **Suggested fix:** add a read-only-zero `mstatush`.
- **Reproducer:** `sim/tests_2/rtl_bug_csr_mtval_mstatush/` (rv32 c5-c7,
  cheri c2-c4).
- **Evidence:** as KUDU-041.

## KUDU-043: CDBG_CTRL has no effect

- **Status:** Deferred (low) by the designer on 2026-10-28; found
  2026-10-25.
- **Location:** `rtl/cs_registers.sv:1029` (CDBG_CTRL, 0xBC4, is
  writable), `rtl/kudu_top.sv:684` (`csr_dbg_tclr_fault_o` not connected).
- **Description:** Setting CDBG_CTRL bit 0 should make operations that
  would clear a capability tag trap instead. The CSR is readable and
  writable but its output is unconnected, so nothing changes.
- **Reference:** cheriot-ibex `cheri_ex.sv:412,438`. Sail has no CDBG_CTRL,
  so this is a debug feature defined by ibex.
- **Expected:** with CDBG_CTRL.0 = 1, `csetboundsimm` past the bounds traps
  (mcause **0x1c**) and the tag of cd is kept.
- **Observed:** no trap; the tag is cleared.
- **Suggested fix:** connect `csr_dbg_tclr_fault_o` and implement the trap
  in the CHERI execution unit, or remove the CSR.
- **Reproducer:** `sim/tests_2/rtl_bug_csr_mtval_mstatush/`, PMODE=1 case c6.
- **Evidence:** as KUDU-041.

## KUDU-044: ALT tag fields reach the IR stage as X with the predictor off

- **Status:** Fixed in `f6dddaa`: `fetch_fifo64` ties `alt_valid` and
  `alt_id` of both fetch outputs to 0, and `alt_seq` was removed
  (KUDU-047). `c_insn` is driven by `compressed_decoder`. The
  `ir_reg_t.is_jalr` field is still undriven, but nothing reads it (the
  issuer uses the decoder's `ir_dec_o.is_jalr`, taken from the opcode).
  Checked by code inspection on `6e157c3`. Found 2026-10-26 (ALT review).
- **Location:**
  - `rtl/fetch_fifo64.sv:156-174`: the output structs `out_instr0_o` and
    `out_instr1_o` never drive `alt_valid`, `alt_id` or `alt_seq`.
    `is_jalr` and `c_insn` are also undriven there.
  - `rtl/branch_predict.sv:309-310`: with `pdt_en = 0` the fetch structs
    pass through unchanged.
  - `rtl/issuer.sv:701-705`: `cancel_alt` and `ex_alt_ctrl_o.id0`/`id1`
    are built from those fields.
- **Description:** when the branch predictor is enabled, `branch_predict`
  overwrites the ALT tags. When `cpuctrl.pdt_en = 0`, the undriven fields
  are captured into the IR registers as X, so the issuer's ALT cancel and
  id outputs are X.
- **Impact:** functionally benign in VCS. `if (X)` does not fire, and
  `apply_cause` also needs `mis_not_taken`, which needs `ptaken = 1`. It is
  still undriven logic: a lint and synthesis problem, and a risk under
  X-pessimistic or gate-level simulation. If an X resolved to 1, it would
  only spuriously free an ALT entry.
- **Expected:** ALT tag fields are 0 when the predictor does not set them.
- **Observed:** the review checker counted 1503-2773 cycles with an X
  cancel in random stress runs that toggle `cpuctrl` (0x7c0). Runs that
  never turn the predictor off show only the reset cycle.
- **Suggested fix:** tie `alt_valid`, `alt_id`, `alt_seq`, `is_jalr` and
  `c_insn` to 0 in `fetch_fifo64` (or in the `pdt_en = 0` path of
  `branch_predict`).
- **Evidence:** `/home/scratch/fortress/kunyanliu/kudu_temp/alt_review_20261026_102059/runs/c1_as_t4/sim.log`
  (`xcancel_cycles=1503 xtag_cycles=14318`) and the other `as_t*` runs.

## KUDU-045: alt_err_event is computed but unused

- **Status:** Deferred (low) by the designer on 2026-10-28; found
  2026-10-26 (ALT review, code review).
- **Location:** `rtl/fetch_fifo64.sv:476`. Line 459 also has a stray `;;`
  in the `alt_err_event` declaration.
- **Description:** `alt_err_event = apply_alt & ~alt_status[alt_apply_id]`
  flags a restore from a free ALT entry. The designer's comment above it
  says this cannot happen, but nothing checks it. Neither the review
  checker nor the fetch-integrity checker ever saw it fire.
- **Suggested fix:** turn it into an assertion (`ASSERT`) or remove it.
  Formal also excludes ALT (`fv/module_fv_ext.sv` assumes no apply/alloc).

## KUDU-046: flush_alt and apply_cause have no default when AltEnable = 0

- **Status:** Fixed in `f6dddaa`: `flush_alt = 1'b0` and
  `apply_cause = 2'b00` are now defaulted at the top of the block
  (`rtl/issuer.sv:688-689` on `6e157c3`). Checked by code inspection.
  Found 2026-10-26 (ALT review, code review).
- **Location:** `rtl/issuer.sv:681-705`.
- **Description:** in the ALT `always_comb` block, `flush_alt` and
  `apply_cause` are assigned only under `if (AltEnable)`. With
  `AltEnable = 0` (conf2) they are never assigned, which lint reports as a
  latch, and `flush_alt` is X in `ex_alt_ctrl_o`.
- **Impact:** none in conf2, because `fetch_fifo64` gates every ALT control
  with `AltEnable`.
- **Suggested fix:** default `flush_alt = 1'b0` and `apply_cause = 2'b00`
  with the other defaults at the top of the block.

## KUDU-047: alt_seq is never driven or used

- **Status:** Fixed in `f6dddaa`: the field was removed from
  `super_pkg` and `ir_decoder`; no `alt_seq` remains in `rtl/`. Checked
  by code inspection on `6e157c3`. Found 2026-10-26 (ALT review, code
  review).
- **Location:** `rtl/super_pkg.sv:60,140` (struct fields),
  `rtl/ir_decoder.sv:119` (pass-through).
- **Description:** the 5-bit `alt_seq` field is declared in the fetch and
  decoded-instruction structs and copied by the decoder, but no module
  drives or reads it. It is part of the X described in KUDU-044.
- **Suggested fix:** remove the field, or drive it if it is intended for
  future use.

---

## KUDU-048: conf2 RA prediction leaves the predicted-PCC outputs undriven

- **Status:** Fixed. `f210f63` sets `PredictRA = 0` in `KuduCfg2`
  (`rtl/kudu_cfg_pkg.sv:126`); `82f67d8` ties the two outputs to 0 in
  `rtl/ir_stage.sv` (`gen_no_stage1`). Found 2026-10-26 (RA-prediction review).
- **Location:** `rtl/ir_stage.sv:373-421` (`gen_no_stage1`, used when
  `IrStageBypass[1] = 1`, i.e. conf2 only).
- **Description:** with `PredictRA = 1`, the stage-bypass branch of
  `ir_stage` never assigned `cjalr_pcc_set_o` or `cjalr_rcap_o`, and never
  upgraded a predicted return's `ptarget` to the full `cur_ra` capability.
  - The outputs were X/Z for the whole run. In RTL simulation,
    `if (ir_cjalr_pcc_set_i)` (`cs_registers.sv:1885`) treats X as false,
    hiding the defect. In synthesis or gate-level simulation the value is
    undefined; if it resolved to 1, the predicted IR PCC (used for fetch
    bounds/permission checks) would be corrupted.
  - Because `ptarget` held only an address, the PMODE=1 full-capability
    JALR compare (`branch_unit.sv:91-93`) always failed: every CJALR return
    mispredicted (6035/6035 on `ra_odd`, against 9/6035 on conf1/conf3).
  - Architectural results were correct: `ra_dtest` 86/86 and stress
    signatures matching conf1/conf3.
- **Evidence:** an RA checker bound into the DUT reported 43k-67k X events
  per conf2 run (0 on conf1/conf3).
- **Fix verification (2026-10-26, conf2, `PredictRA = 0`, outputs tied to 0):**
  - full regression: 217 PASS, 43 XFAIL (open bugs), 0 FAIL;
  - 37 RA directed/stress programs × base/interrupt/wait-state (111 runs):
    all checker counters 0 (including X), no timeouts or bad signatures,
    72/72 stress signatures equal to conf1;
  - artefacts in `/home/scratch/fortress/kunyanliu/kudu_temp/kudu048_20261026_163141/`.
  - Every conf2 CJALR return now mispredicts by design (performance only).
- **Follow-ups:**
  - add an elaboration-time `$error` in `gen_no_stage1` when
    `PredictRA = 1`, since the restriction is only a configuration value;
  - `dec0_cjalr` in `gen_no_stage1` is now dead logic.

---

## KUDU-049: return-address prediction register resets outside the RA limit range

- **Status:** Fixed (`8e3b20b`); found 2026-10-26 (RA-prediction review).
- **Location:** `rtl/ir_stage.sv:598` (`gen_predict_ra`); affects every
  configuration with `PredictRA = 1` (conf0/1/3).
- **Description:** `RALimitLo`/`RALimitHi` are in 4 kB units (compared
  against `cur_ra_d[31:12]`, line 590). The clamp keeps the predicted
  return address `cur_ra32_q` inside the range so that speculative fetches
  never reach unpopulated memory. But the reset value was
  `cur_ra32_q <= RALimitLo`, i.e. `0x00080000` instead of `0x80000000`.
  A return (`c.jr ra`, `jalr x0, 0(ra)`, `cret`) predicted after reset,
  before any in-range write to x1, therefore fetched `0x00080000`. The
  same happens if every x1 write so far was out of range, since the
  clamp then holds the reset value. The mispredict is corrected at
  execute, so the error is not architecturally visible. However, the
  speculative bus access to unpopulated space is exactly what the clamp
  exists to prevent; the comment notes it can hang some memory systems.
- **Evidence:** the RA checker's fetch-range check (C3) on `ra_rst`
  flagged `addr=00080000 cur_ra32=00080000 pdt_set=1` on conf1, conf2
  (before KUDU-048) and conf3.
- **Fix:** `cur_ra32_q <= {RALimitLo[19:0], 12'h0};`
- **Fix verification (2026-10-26, conf1 and conf3):**
  - full regression: 211 PASS, 49 XFAIL (open bugs), 0 FAIL on each;
  - 37 RA directed/stress programs × base/interrupt/wait-state on both
    configs (222 runs): all RA checker counters 0, including
    `c3_fetch_oob` on `ra_rst`; no timeouts or bad signatures; `ra_dtest`
    passes 6/6;
  - artefacts in `/home/scratch/fortress/kunyanliu/kudu_temp/kudu049_20261026_171050/`.

---

## KUDU-050: dcache forwards stale data after a cap or misaligned store

- **Status:** Fixed in `f61f89d`, with a performance refinement in
  `6e157c3` (see KUDU-033 for the change). Found 2026-10-26 (RAW/WAW
  hazard review).
- **Fix verification (2026-10-28, `6e157c3`):**
  - Random stress: a new generator (`gen_dcr.py`) builds 40 programs
    (20 RV32, 20 CHERIoT), each with about 200 checked loads. It mixes
    aligned and misaligned stores, `csc`/`clc` and cache-warming loads,
    biases loads to the word after the previous store, and checks both
    the forwarded consumer value and the RF value.
  - With `dcs_r`/`dcs_c` and `dss_r`/`dss_c` (KUDU-033): 792/792 PASS on
    conf0-3, `simv32`, `simv` PMODE=0/1, default and two delayed-memory
    settings. Pre-fix RTL (`991dba4`): 240/264 fail, including every
    `dcs`/`dss` run and 216/240 `dcr` runs.
  - No regression: SC stress (KUDU-014) 264/264 and fetch-error stress
    (KUDU-013) 192/192 PASS; full regression 732/732 OK on `6e157c3`
    (730/730 completed runs OK on `f61f89d`).
  - Performance: CHERIoT CoreMark on conf1 costs +0.40% cycles on
    `f61f89d` and +0.11% on `6e157c3`, relative to `991dba4`. RV32
    CoreMark is unchanged.
  - Artefacts: `/home/scratch/fortress/kunyanliu/kudu_temp/k033chk2_20261028_095227/` (generator, pre-fix
    comparison), `/home/scratch/fortress/kunyanliu/kudu_temp/k050chk_20261028_103220/`,
    `/home/scratch/fortress/kunyanliu/kudu_temp/fullregr_k050_20261028_104008/`.
- **Location:** `rtl/dcache.sv:124-184` (read side) and `:236-300`
  (update side); every configuration with `DCacheEn = 1` (all of conf0-3),
  PMODE=1, PMODE=0 and the RV32-only build.
- **Description:** the dcache updates or invalidates lines only when the
  store's response arrives (`lsu_resp_valid_i`, registered). The LSU
  accepts the next request in that same cycle (`resp_wait =
  outstanding_resp_q & ~lsu_resp_valid`), so the next load's cache lookup
  still sees the old lines. The only protection is the store-to-load bypass
  (`byp_tag_match`), which compares `addr[31:2]`, i.e. one word only. A
  store that writes more than one word is not covered:
  - `csc` to A writes A..A+7; a following load from A+4 hits the old
    line for A+4 (the cap is later invalidated via `resp_invalidate`);
  - a misaligned `sw`/`sh` that spans into the next word (e.g. `sw` to
    A+1/A+2/A+3, `sh` to A+3); `unaligned_access_q` invalidates every line
    at the response, again one cycle too late.

  On a hit, `fwd_info_o.valid[1]` is set with the stale `cache_rdata_ext`.
  A dependent instruction issued in that cycle takes the forwarded value
  (the issuer does not stall on `reg_wrsv` when `fwd_act` matches). The
  load itself still writes the correct memory value to the RF at commit,
  so only the consumer is wrong. For misaligned stores, the following load
  waits in `lsu_if` until the multi-beat store finishes, so it lands in the
  overlap cycle even with several instructions between store and load.
- **Evidence:** `dcs_c` (CHERIoT: `csc` + 4 misaligned-store kinds, 60
  cases) and `dcs_r` (RV32: 4 misaligned-store kinds, 48 cases). Each case
  pre-fills the A+4 line, does the store, then `lw a3, A+4` followed by
  `xor a4, a3, x0` after 0-3 / 0-2 nops, and compares both against a
  delayed re-read. Results on the current RTL (`8e3b20b`):
  - `dcs_r` fails 40/48 on conf1, conf2 and conf3 (PMODE=0) and on the
    conf1 RV32-only `simv32`;
  - `dcs_c` fails 44-48/60 on conf1/2/3 (PMODE=1), including `csc` cases;
  - in every failing case, `a3` (RF) is correct and `a4` (forwarded) holds
    the stale line. Trace example (conf1, PMODE=1): `clw x13,260(c9)` →
    `x13=0x3333b4b4`, then `xor x14,x13,x0` reads `x13:0x33333333`.
  - artefacts in `/home/scratch/fortress/kunyanliu/kudu_temp/rawwaw_20261026_222811/` (`gen/gen_dcs.py`,
    `runs/`).
- **Suggested fix:** treat the lookup as a miss while a store that is
  outstanding (`lsu_req_q & ~lsu_req_info_q.is_load`) is a cap store,
  misaligned, or not cache-OK, unless the load hits the existing
  same-word `byp_data_good` case. Alternatively, match the bypass on
  `addr[31:3]` for caps and on both touched words for misaligned stores.
  Another option is to invalidate the touched lines at `lsu_req_done`
  instead of at the response.

---

## PMODE=0 vs RV32 equivalence (2026-10-19)

Question: does the CHERIoT build (`CHERIoTEn=1`) at `cheri_pmode_i=0` behave
architecturally like the RV32 build (`CHERIoTEn=0`)?

**RTL review.** Every `CHERIoTEn`/`cheri_pmode` use in `rtl/` was checked.
All architectural paths gate on `cheri_pmode = CHERIoTEn & cheri_pmode_i`:
- decode: `clc`/`csc`, CHERI and AUICGP opcodes, AUIPCC, x16-x31 and the
  compressed decoder;
- pipeline routing: CJALR to the mult pipeline and its serialisation
  (`issuer.sv:138,335,744`), the JALR mispredict compare
  (`branch_unit.sv:92`);
- trap behaviour: fetch bounds/permission checks, LSU CHERI checks,
  CJALR errors, illegal-instruction mtval (`issuer.sv:971`) and the
  mstatus.MPIE source (`cs_registers.sv:782`);
- CSRs: MTVEC/MEPC versus MTCC/MEPCC access, MSHWM/MSHWMB/CDBG_CTRL,
  mvendorid/marchid and the misa X/I/E bits;
- load-filter hazards (`issuer.sv:474-477`).

Paths gated on `CHERIoTEn` alone either carry capability metadata that is
not visible at PMODE=0 (register/memory tag and bounds bits, PCC,
MTDC/MSCRATCHC reset values, the `cmplx_unit`/`ls_pipeline` request `pc` as
`pcc2regcap`), are only reachable through `clc` (load-filter reservation,
`cheri_trvk_stage`, regfile revocation tag clear), or are unused
(`ir_decoder.sv:190` `cjalr_insn`). The only architectural defect is
KUDU-020 (fixed in `d88c674`).

Differences that are timing-only:
- `rtl/ir_stage.sv:375,433` (`dec0_cjalr`/`dec_cjalr = CHERIoTEn & is_jalr`)
  treat every JALR as a CJALR at PMODE=0. This changes IR-stage
  dual-issue and RA-prediction decisions (and updates the unused IR PCC
  copy). Committed results are unchanged, but cycle counts (mcycle,
  interrupt points) can differ from the RV32 build.
- `rtl/kudu_top.sv:181` ties `cheri_tsafe_en` to `CHERIoTEn`. It has no
  effect at PMODE=0 because `clc` cannot decode.

**Simulation.** Fresh conf1/2/3 builds of both `simv32` and `simv +PMODE=0`
were compared on retired-instruction traces with time and cycle columns
removed:
- 88 directed programs: riscv-tests rv32ui/ua/uzb*, `rv32_test_csr`,
  `rv32_test1`, `coremark.rv32o3`, `hello_world`;
- the 9 RV32 `rtl_bug_*` tests;
- 30 seeds of a random RV32 stream biased to PMODE-sensitive encodings:
  CHERI/AUICGP opcodes, `ld`/`sd` (clc/csc) funct3, the C0/C2 FP/CHERI
  slots, `c.addi16sp`/`c.addi4spn`, x16-x31, CHERIoT-only CSRs, JALR/RA
  returns, AMOs and traps.

Every program ran on conf1/2/3 with default memory timing. Delayed
memory was added on conf1 for the directed programs and on all three
configs for the fuzz seeds, giving 568 pairs in total. 369 pairs were
identical. 191 differed only in the trailing instructions after the
end-of-test UART write or timeout (stop timing). The remaining 8 pairs
were the misa reads of KUDU-020 (`rtl_bug_misa_value`, and
`rv32_test_csr`, which reads misa). The generator and runner are in `/home/scratch/fortress/kunyanliu/kudu_temp/pmode0_equiv_20261019_143106/`
(`gen_rv32.py`, `batch.sh`, `prefix.py`).

---

## Sail divergences (not classified as bugs)

| Area | Kudu | CHERIoT Sail | Assessment |
|---|---|---|---|
| Zbkb/Zbkx (`pack`, `packh`, `brev8`, `zip`, `unzip`, `xperm4`, `xperm8`) | Illegal instruction | Legal (Makefile `SAIL_DEFAULT_INST`, `riscv_insts_zbkb.sail`, `riscv_insts_zbkx.sail`) | Scope: Kudu implements B (Zba/Zbb/Zbc/Zbs), not scalar crypto. Demo: `sim/tests_2/rtl_bug_sail_zbkb_zbkx_missing/` |
| Trigger CSRs (`tselect`, `tdata*`) | Implemented per Debug Spec | Disabled; `tselect` reads all ones | Scope: Sail models no triggers. Demo: `sim/tests_2/rtl_bug_trigger_csr_sail/` |
| Misaligned load/store, second half faults | mtval = word-aligned address of the faulting half (e.g. `0x80040000`) | mtval = original address (`0x8003fffd`), `riscv_insts_base.sail:328-343` | Both permitted by the privileged spec; Kudu matches cheriot-ibex (`load_store_unit.sv:235-238`) |
| A extension | Implemented | Not in model | No Sail golden; KUDU-007/008 judged against the RV32A spec |
| DRET, ECALL, EBREAK | — | DRET illegal; ECALL tval 0; EBREAK tval PC | Sail confirms KUDU-004 and KUDU-005 |
| Reserved FENCE/FENCE.I fields | Accepted | Accepted as hints (`riscv_insts_hints.sail:134-165`) | Match |
| `mcounteren` (`0x0306`) | Implemented, reads 0; `misa.U` = 1 | Illegal instruction; `misa.U` = 0 so the CSR is undefined (`sail-riscv/model/riscv_sys_control.sail:31`) | Configuration difference; Kudu matches cheriot-ibex (`ibex_cs_registers.sv:406-408`) |

The **isa_test1** ELF compares equal on Kudu (PMODE=1) and Sail
(`compare_trace.py`: 6985/6985 trace objects).

---

## Suspicious, unconfirmed

| Location | Concern | Why not confirmed |
|---|---|---|
| `rtl/ir_decoder.sv:276-319` | OP-IMM bitmanip legality gated by `RV32M` instead of `RV32B` | Not observable while both are enabled |
| `rtl/cs_registers.sv` | DPC shares the KUDU-001 legalizer path | Fixed with KUDU-001; not reproduced in debug mode |
| LR/SC reservation | Reservation clearing on trap/xRET relies on memory response | No failing case built |
| PMP | `data_pmp_err` is tied to 0 in the current top | Matches Sail default of 0 PMP regions; not a bug unless PMP is required |

Resolved: the conf2 (`StageBypass[1]`) unassigned CJALR PCC outputs were
confirmed on 2026-10-26 as KUDU-048.

Resolved: vectored `mtvec` (`rtl/issuer.sv:822`) is not a bug. The mode
field is WARL and is forced to direct mode, which is legal and matches
Sail's direct-only MTCC.

Resolved: the JALR bit-0 concern (`rtl/branch_unit.sv:65-72`) was confirmed
on 2026-10-25 as KUDU-039. IF masks bit 0 for fetch, but the unmasked target
reaches mepc/dpc when an interrupt is taken with an empty IR.

Possibly intended (2026-10-25 review, needs a design decision):
- At PMODE=1, `csrr mtvec`/`csrr mepc` are illegal. Sail treats them as
  reads of the MTCC/MEPCC address.
- WARL choices that differ from cheriot-ibex but are legal:
  `mcountinhibit[31:3]` read as 1, `mcause` keeps only bits {31, 4:0}, and
  `mie[30:16]` is writable.
