# CHERIoT-Kudu RTL bug log — review round 2

Second full RTL review, 2026-11-05. Debug mode/single-step and the CSR
performance counters were excluded by request (see `debug_bugs.md` for the
debug items). IDs continue from `bug_logs.md` (KUDU-001..050).

- **RTL reviewed:** `7fbbb44` plus the uncommitted LR/SC hazard fix
  (KUDU-051: `is_cheri` → `rs_cheri` including `OPCODE_AMO`, in
  `rtl/ir_decoder.sv`, `rtl/issuer.sv`, `rtl/super_pkg.sv`). The review
  started on unmodified `7fbbb44`; every finding below was re-verified on the
  fixed RTL.
- **References:** CHERIoT Sail (`/home/scratch/fortress/kunyanliu/kudu_temp/cheriot_sail_dii_20261013_155851`,
  branch `dii-read-from-file`), cheriot-ibex (`sim/run_ibex`), the RISC-V
  unprivileged/privileged specs, and Python reference models written for the
  review. Sail and ibex do not implement the A extension, so AMO behaviour was
  checked with self-checking programs and kudu-vs-kudu comparisons.
- **Scratch area:** `/home/scratch/fortress/kunyanliu/kudu_temp/review2_20261105_004317/` (`$R` below). Builds
  `$R/build_c{0..3}` are the original RTL and `$R/build2_c{1,2,3}` the fixed
  RTL; each holds `simv` and `simv32` and was compiled with `-nowave` (conf0 and
  conf1 are the same configuration). Each area's raw report is
  `$R/<area>/REPORT.md`; my independent re-verification runs are in
  `$R/verify/`.

## Summary

| ID | Status | Severity | Area | Location | Summary | Reproducer |
|---|---|---|---|---|---|---|
| KUDU-051 | **Fixed** (`0ab3b26`) | High | Issue/CHERI load barrier | `rtl/ir_decoder.sv:109-113`, `rtl/issuer.sv:475-478` | LR.W/SC.W skip the load-barrier (trvk) hazard after CLC, so a revoked capability can still be used | `$R/lsu/M/tests/lsu_rvk_lrsc/` |
| KUDU-052 | **Fixed** (`a6e599e`) | Low–medium | LSU/trap | `rtl/load_store_unit.sv:126,242,470-487` | Misaligned access, second-half bus error: mtval = first word's address when the 2nd grant precedes the 1st rvalid | `$R/lsu/M2/tests/lsu_split_mtval{,_c}/`, `lsu_split_wr/` |
| KUDU-053 | **Fixed** (`a6e599e`) | Low (lint/synthesis) | CHERI EX | `rtl/mult_pipeline.sv:251-281` | `set_bounds_comb` infers 164 latch bits | Verilator lint (below) |
| KUDU-054 | **Fixed** (`a6e599e`) | Low | Fetch | `rtl/fetch_fifo64.sv:151,434,451,568` | ALT save path drops the `align64` bit (64-bit `rdata_alt_d` vs 65-bit entries) | Code review / VCS lint |
| KUDU-055 | **Fixed** (`c7598d2`, `69b5f26`) | Low–medium (verification) | Tracer | `rtl/tracer.sv:224-237` | AMOs are traced and RVFI-reported with rd = x0, value 0 (regression from the KUDU-032 fix) | `$R/issue/mirror/tests/is_r_s501_amo_nobus` |
| KUDU-056 | **Fixed** (`69b5f26`) | Low (verification) | Tracer | `rtl/tracer.sv:343,473` | After an interrupt, CLC tag annotations are off by one; `final_fifo` can overflow silently | `$R/issue/mirror/tests/rvk_s1` |
| KUDU-057 | **Fixed** (`c7598d2`) | Low (verification) | Tracer | `rtl/tracer_pkg.sv:1838-1849`, `rtl/tracer_dpi.cpp:1175-1184` | `amoand.w` disassembled as `INVALID` with no rd write | `$R/issue/mirror/tests/is_r_s501_amo_nobus` |
| KUDU-058 | **Fixed** (`6722f7c`) | Low (verification) | Tracer | `rtl/tracer_pkg.sv:1507` | `c.ebreak` trace line has no PC/encoding, breaking `compare_trace.py` | `$R/fuzz/repro/tracer_cebreak/` |
| KUDU-059 | **Fixed** (`94e007e`) | Low (testbench) | TB | `sim/tb/tb_kudu_top.sv:99,148-149,561` | `+CAP_ERR_RATE` is parsed but drives nothing; no capability-tag errors are ever injected | Code review |

No functional bug was found in the front end, decode/legality, execution
units, issue/hazard/commit logic, or CSR/trap/interrupt logic (see
"Areas checked clean").

---

## KUDU-051: LR.W/SC.W skip the load-barrier hazard after CLC

- **Status:** Fixed in commit `0ab3b26` (`OPCODE_AMO` added to `rs_cheri`).
  Found by the LSU review.
- **Severity:** High — CHERIoT temporal safety (use after free through a
  revoked capability).
- **Location:** `rtl/ir_decoder.sv:109-113` (`is_cheri`, now `rs_cheri`),
  consumed by `ir_cheri_hazard` in `rtl/issuer.sv:475-478`.
- **Description:**
  - A CLC result passes through the 3-stage `cheri_trvk_stage`, which clears
    the tag if the base granule is marked in the revocation bitmap.
  - Until that result is written back, the issuer must stall any instruction
    that uses the loaded register as a capability.
  - `is_cheri` listed load/store/CHERI opcodes but not `OPCODE_AMO`, so
    `lr.w`/`sc.w` issued with the stale, still-tagged capability.
  - Other AMOs were masked by `cmplx_unit`'s WAIT_CMT0 sequencing; LR/SC were
    not.
- **Observed (original RTL):** `lr.w`/`sc.w` issued 0–4 instructions after a
  `clc` of a revoked capability did not trap. `lr.w` returned memory data;
  `sc.w` wrote memory and returned 0 (success).
- **Expected:** Sail `cheri_insts.sail:914-920` clears the loaded tag. Any later
  access through it takes a CHERI tag violation (mcause 0x1c,
  mtval = (rs1<<5)|0x02), as plain `clw`/`csw` and the other AMOs already do.
- **Reproducer:** `$R/lsu/M/tests/lsu_rvk_lrsc/` (CHERIoT, 22 cases:
  lr/sc/clw/csw/amoadd × 0/2/4 NOPs after the clc, plus non-revoked controls).
  ```
  cd $R/lsu/M/tests && bash ../scripts/build_test.sh lsu_rvk_lrsc
  submit -i $R/build2_c1/simv +TEST=lsu_rvk_lrsc +PMODE=1 +TIMEOUT=2000000
  ```
- **Fix:** `is_cheri` was renamed `rs_cheri` and now includes `OPCODE_AMO`;
  `ir_cheri_hazard` uses `rs_cheri`. The fcov references were updated to
  match.
- **Fix verification (2026-11-05):**
  - My rerun (`$R/verify/runs/lsu_rvk_lrsc/`): original `build_c1` 16 PASS /
    6 FAIL (e.g. `FAIL revoked lr.w nops=0 ... trapped=0 rd=0x12345678`); fixed
    `build2_c1` 22/22 PASS; fixed `build2_c3` with
    `+DATA_GNT_WMAX=3 +DATA_RESP_WMAX=3` 22/22 PASS.
  - LSU review: 22/22 on `build2_c{1,2,3}`, with and without wait states.
  - Fuzz review (`FZ_AMO_CLC` mode, which reloads the AMO's address capability
    with `clc` just before it): 4/16 programs fail on the original build,
    16/16 pass on `build2`, plus 56 more on `build2`, all passing.

## KUDU-052: Misaligned access, second-half bus error reports the first word's address in mtval

- **Status:** Fixed in commit `a6e599e`. The LSU was reworked:
  `WAIT_RVALID_MIS_GNTS_DONE` and `addr_incr_req` are removed, the second half of a
  misaligned access is requested only after the first rvalid, and
  `addr_last_d = handle_misaligned_q ? aligned : data_addr`.
  Found by the LSU review.
- **Verification:**
  - `lsu_split_mtval`/`lsu_split_mtval_c` with waits: 9/9 PASS on conf1/2/3
    (0/9 on `ff98820`). `lsu_split_wr`: 0 failures. Bus-error replay:
    34/34 per conf (`/home/scratch/fortress/kunyanliu/lsuchk2_20261107_140136/`).
  - 11/12 comparison traces byte-identical to the previous RTL. The 12th
    (isa_test2 with delay) differs only in time/cycle columns, +175 cycles on conf2.
    CoreMark cycle counts unchanged.
  - LSU stress (`/home/scratch/fortress/kunyanliu/lsstress_20261107_142657/`, seeds 5001-5040, conf1/2/3, random waits and
    interrupts): 600/600 PASS. That is 120 Sail-compared CHERIoT runs (`cst`),
    240 reference-model runs (`rst`, PMODE 0 and rv32), and 240 bus-error runs (`rer`)
    checked strictly, with exact mtval and no KUDU-052 allowance.
  - Full regression (`/home/scratch/fortress/kunyanliu/kudu_temp/full_regr_batch_c{1,2,3}_20261107_150020/`): every conf has 246 PASS, plus XFAIL and DEFER only for
    known bugs (KUDU-019/035/042/043); dcsr.step tests skipped.
- **Severity:** Low–medium. mcause, the trapping PC, rd preservation and memory
  are correct; only mtval is wrong. The trigger (memory response latency) is
  the normal case on a real bus.
- **Location:** `rtl/load_store_unit.sv:126`, interacting with `:242` and the
  `WAIT_RVALID_MIS_GNTS_DONE` state (`:470-487`).
  ```
  126: assign data_addr   = handle_misaligned_q ? (lsu_req_info_q.addr + {addr_incr_req, 2'b00}) : lsu_req_info_i.addr;
  242: assign addr_last_d = addr_incr_req ? data_addr_w_aligned : data_addr;
  ```
- **Description:**
  - The intent (comment at `:236-240`, and the Kudu/ibex convention recorded in
    the "Sail divergences" table of `bug_logs.md`) is that once the first half
    completes without error, `addr_last_q` holds the second word's aligned
    address.
  - If the second request is granted before the first rvalid, the FSM is in
    `WAIT_RVALID_MIS_GNTS_DONE`, where `handle_misaligned_q` is already 0.
  - So `addr_incr_req = 1` but `data_addr` falls back to `lsu_req_info_i.addr`,
    and when the first rvalid arrives without error, `addr_update` latches the
    **first** word's aligned address.
  - If the second half then returns `data_err_i`, mtval is that address.
  - With no response latency the FSM goes through `WAIT_RVALID_MIS`, where
    `handle_misaligned_q = 1`, and mtval is correct.
  - Not the same as KUDU-015, which concerned rejected capability/atomic
    requests.
- **Observed:** for `lw` at `0x8007fffd` with the second half at the unmapped
  `0x80080000`: mcause 5, mtval **`0x8007fffc`**.
- **Expected:** mtval **`0x80080000`** (Kudu/ibex convention) or `0x8007fffd`
  (Sail, `riscv_insts_base.sail:328-343`). Privileged spec §3.1.16 permits
  either. `0x8007fffc` is outside the access and is not the faulting portion.
  The same applies to stores (mcause 7), `lh/lhu/sh`, and the CHERIoT
  `clw/clh/clhu/csw/csh` forms.
- **Reproducers:** directed tests that iterate each op 16 times so random wait
  states reach the GNTS_DONE path:
  - `$R/lsu/M2/tests/lsu_split_mtval/` (RV32: lw/lh/lhu/sw/sh at offsets
    +13/+14/+15 straddling `0x80080000`);
  - `lsu_split_mtval_c/` (CHERIoT, PMODE=1);
  - `lsu_split_wr/` (stores).
  ```
  submit -i $R/build2_c2/simv32 +TEST=lsu_split_mtval +TIMEOUT=2000000 +DATA_RESP_WMAX=3 +DATA_GNT_WMAX=1
  submit -i $R/build2_c1/simv   +TEST=lsu_split_mtval_c +PMODE=1 +TIMEOUT=2000000 +DATA_RESP_WMAX=3
  ```
- **Verified on (2026-11-05, current RTL; `$R/verify/runs/`):**
  - `lsu_split_mtval` on `build2_c2/simv32` with waits: 0/9 PASS
    (`FAIL lw+13 ... mcause=00000005 mtval=8007fffc`).
  - The same test without waits: 9/9 PASS.
  - `lsu_split_mtval_c` on `build2_c1/simv` PMODE=1 with waits: 0/9 PASS
    (`FAIL clw+13 ... mtval=8007fffc`).
  - The LSU review also reproduced it on c1/c2/c3, PMODE 0 and 1, with
    `+DATA_RESP_WMAX` ≥ 1–2. 11 of the 1,262 faults injected in its random
    bus-error replay hit this case.
- **Suggested fix:** use the incremented address whenever the second half is
  being tracked:
  `assign data_addr = (handle_misaligned_q | addr_incr_req) ? (lsu_req_info_q.addr + {addr_incr_req, 2'b00}) : lsu_req_info_i.addr;`
  The LSU reviewer validated this on a shadow RTL copy (directed tests plus
  regression seeds). Check that `data_offset` and the request-side
  `data_addr` use are unaffected in `WAIT_RVALID_MIS_GNTS_DONE`, since no new
  request is issued in that state.
- **Side note (not a bug):** when one half of a misaligned store faults, the
  other half is still written. The privileged spec allows this.

## KUDU-053: `mult_pipeline` `set_bounds_comb` infers latches

- **Status:** Fixed in commit `a6e599e` (`set_bounds_comb` now assigns every
  output on every path). Found by the exec review.
- **Verification:** Verilator lint reports 0 LATCH warnings (was 4). Traces on
  conf1/2/3 are identical to the previous RTL (36/36). The full regression and
  LSU stress listed under KUDU-052 also pass on this RTL.
- **Severity:** Low. No simulation-visible effect; it affects lint, synthesis,
  STA and DFT.
- **Location:** `rtl/mult_pipeline.sv:251-281` (`always_comb begin: set_bounds_comb`).
- **Description:** the `if / else if` chain (cjalr, csetbounds/rndn,
  csetboundsex, csetboundsimm, crrl/cram) has no final `else` and no default
  assignments for `newlen`, `req_exact_d` and `ex1_tfcap_d`, so
  `setbounds_req_d = prep_bound_req(ex1_tfcap_d, newlen)` is computed from
  latched values. RTL simulation still matches the netlist because the result
  is consumed only by the selected CHERI ops.
- **Observed:**
  - Verilator `-Wall` reports `%Warning-LATCH` for `newlen`, `req_exact_d`,
    `ex1_tfcap_d` and `setbounds_req_d` (re-run: `$R/verify/mp_lint.log`).
  - Design Compiler reports `ex1_tfcap_d_reg` (131 bits), `newlen_reg2` (32)
    and `req_exact_d_reg` (1) as latches
    (`ELAB-974`, `syn/syn028lp/dc.*.log`). It is the only latch in the design.
  - The repo's Verilator flow passes `-Wno-LATCH`, which hides it.
- **Reproducer:**
  ```
  verilator --lint-only -Wall -Wno-fatal -GCHERIoTEn=1 +define+CHERIoT -Iprim -Irtl \
    rtl/cheri_pkg.sv rtl/csr_pkg.sv rtl/super_pkg.sv rtl/kudu_cfg_pkg.sv \
    rtl/multdiv32.sv rtl/mult_pipeline.sv --top-module mult_pipeline 2>&1 | grep LATCH
  ```
- **Suggested fix:** default assignments at the top of the block, e.g.
  `newlen = cs2_fcap.addr; req_exact_d = 1'b0; ex1_tfcap_d = cs1_fcap;`, or
  make the last branch a plain `else`.

## KUDU-054: fetch_fifo64 ALT save drops the `align64` bit

- **Status:** Fixed in commit `a6e599e`. `rdata_alt_d`, `alt_rd_rdata` and
  `alt_entry_t.rdata` are widened to 65 bits, so ALT save and restore keep
  `align64`. Found by VCS `+lint=all`.
- **Verification:** the width-truncation lint warnings are gone. Traces on
  conf1/2/3 are identical to the previous RTL (36/36). The full regression and
  LSU stress listed under KUDU-052 also pass on this RTL.
- **Severity:** Low. No configuration enables `UnalignedFetch`, the only mode
  that uses `align64`, so there is no effect today.
- **Location:** `rtl/fetch_fifo64.sv:151` declares
  `logic [DEPTH-1:0] [63:0] rdata_alt_d;`. Lines 434 and 451 assign the 65-bit
  `{in_rdata_align64_i, in_rdata_i}` / `rdata_q[i+1]` into it, and line 568
  stores it into `alt_table[i].rdata`.
- **Description:** the MSB (`align64`) is truncated when an entry is saved to
  the ALT table, so a restored ALT entry always has `align64 = 0`.
- **Suggested fix:** declare `rdata_alt_d` with the same width as the FIFO
  entry (65 bits).

## KUDU-055: AMOs traced and RVFI-reported with rd = x0

- **Status:** Fixed in two commits. Found by the issue/hazard review.
  Regression from the KUDU-032 fix (`1567152`).
  - `c7598d2`: `rd_addr`/`rd_wdata` are captured in `amo_state == 1`, when
    `rf_we` is high.
  - `69b5f26`: `mem_rdata` moved from `amo_state == 0` (where the tracer reads 0)
    to `amo_state == 1`. Before this, every AMO was traced with
    `load:0x00000000`.
- **Correction (2026-11-07):** an earlier note here claimed full verification
  with 424 runs in `k055_057_20261107_161354`. Those runs used the issue review's
  privately patched build3 simv, not `c7598d2`, because a path substitution
  silently missed. Disregard them.
- **Verification of `c7598d2` alone** (`/home/scratch/fortress/kunyanliu/kudu_temp/k056_058_059_20261107_172203/`, 318 AMO jobs on conf1/2/3):
  - all pass RW and the shadow-regfile check;
  - `amo_chk.py` reports 0 rd-field or missing-rd errors;
  - 9,120 AMOs show `load:` ≠ old value (always `0x00000000`).
- **Second fix, first verified in scratch** (`/home/scratch/fortress/kunyanliu/kudu_temp/k056_058_059_20261107_172203/iso/fix055b.diff`): move
  `result.rvfi.mem_rdata = reg_wdata;` from the `amo_state == 0` branch to the
  `amo_state == 1` branch (`reg_wdata` there is `amo_rdata_q`, the old value).
  - Result: 318/318 runs pass RW, shadow and `amo_chk.py` on conf1/2/3.
  - That covers 10,422 AMOs (1,122 `amoand.w`), each with rd = `load:` = the old value.
- **Final verification** (`/home/scratch/fortress/kunyanliu/kudu_temp/kfinal_20261107_183302/`): the built RTL is byte-identical to
  `6722f7c` (md5 of every `rtl/` file checked).
  - SV tracer, conf1/2/3: 318/318 AMO runs pass.
  - DPI tracer, conf1: 106/106 AMO runs pass.
  - That is 13,896 AMOs (1,496 `amoand.w`), all with rd = `load:` = the old value.
- **Severity:** Low–medium (verification infrastructure). The core writes rd
  correctly, but every AMO with rd ≠ 0 is misreported in both
  `trace_kudu_core.log` and `rvfi_kudu_core.log`. Any trace or RVFI comparison
  that includes AMOs either fails or has to be masked. LR/SC are reported
  correctly.
- **Location:** `rtl/tracer.sv:224-237` (`fill_cmt_info`, AMO branch), together
  with `rtl/cmplx_unit.sv:164`
  (`cmplx_lsu_req_info_o.rf_we = (cmplx_fsm_cs == AMO_WRITE);`).
- **Description:** after KUDU-032, `rf_we` is 0 in the AMO read phase, and the
  tracer captures `rd_addr`/`rd_wdata` only when `amo_state == 0`. So it
  records `rd_addr = 0`, which forces `rd_wdata = 0`. The write-phase branch
  (`amo_state == 1`) never fills in rd.
- **Observed:**
  `$R/issue/runs/b2c1_amo_rv32_irqws/is_r_s501_amo_nobus/trace_kudu_core.log:3827`:
  `80000740 2483a32f amoxor.w x0,x7,x8 ... x0=0x00000000 ... load:0x00000000`.
  The encoding has rd = x6, and the next reader of x6 sees the loaded value.
- **Expected:** `amoxor.w x6,x7,x8 ... x6=<old memory value>`.
- **Reproducer:** any AMO with rd ≠ 0 on any build that contains `1567152`:
  ```
  submit -i $R/build2_c1/simv32 +TEST=is_r_s501_amo_nobus +TIMEOUT=5000000   # bin: $R/issue/mirror/run/bin
  ```
- **Suggested fix:** in the `amo_state == 1` branch, add
  ```
  result.rvfi.rd_addr   = rf_we ? `TOP_PATH.lspl_output.waddr : 0;
  result.rvfi.rd_wdata  = reg_wdata;
  result.rvfi.mem_rdata = reg_wdata;
  ```
  Alternatively, latch rd in state 0 and qualify it with the state-1 `rf_we`.
  Validated by the issue review on a private tracer copy: 318/318 AMO runs
  shadow-clean together with KUDU-057.

## KUDU-056: tracer CLC/trvk matching breaks after an interrupt; `final_fifo` can overflow

- **Status:** Fixed in commit `69b5f26`. Found by the issue/hazard review.
  - `is_good_clc` now also requires `~instr_tmp2.rvfi.intr`.
  - `$error` checks fire if the `instr_trace_fifo` or `final_fifo` occupancy
    exceeds 48.
- **Verification:**
  - Before the fix (`c7598d2`, `/home/scratch/fortress/kunyanliu/kudu_temp/k056_058_059_20261107_172203/`): 0 of 48 `rvk` interrupt/wait-state runs
    passed the shadow-register check.
  - After the fix: 144/144 pass on conf1/2/3 in the same area. They pass again in
    `/home/scratch/fortress/kunyanliu/kudu_temp/kfinal_20261107_183302/`: 144/144 on SV-tracer conf1/2/3 plus 16/16 on the DPI-tracer conf1
    build.
  - Neither occupancy `$error` fired in any run, including the full regression on
    conf1/2/3 (246 PASS, 9 XFAIL, 0 FAIL each).
- **Severity:** Low (verification infrastructure). It produced false
  trace/RVFI miscompares, and possibly dropped trace lines, in any CHERIoT run
  with interrupts.
- **Location:** `rtl/tracer.sv:473`
  (`is_good_clc = instr_tmp2.ir_dec.cheri_op.clc & ~instr_tmp2.rvfi.trap;`) and
  `rtl/tracer.sv:343` (`final_fifo[64]`, no full check).
- **Description:**
  - An interrupt-entry record (`rvfi.intr = 1`) carries the `ir_dec` of the
    instruction it displaced.
  - If that instruction is a `clc`, the tracer waits for a trvk result that
    never comes.
  - Every later `clc` then takes the previous one's trvk, so traced tags are
    off by one.
  - When the queue falls far enough behind, `final_fifo` wraps silently.
- **Observed:** `$R/issue/runs/b2c1_rvk_irqws/rvk_s1/trace_kudu_core.log`
  ~4355-4372.
  - `CH.clc c6,216(c9)` is traced with tag 1, but the next `CH.cgettag x15,c6`
    reads tag 0 (x15 = 0).
  - `c.CH.clc c12,48(c9)` is traced with tag 0, but `CH.cgettag x15,c12`
    returns 1.
  - The program signature passes (hardware tags are correct).
- **Reproducer:** PMODE=1 with interrupts:
  ```
  submit -i $R/build2_c1/simv +TEST=rvk_s1 +TIMEOUT=5000000 +PMODE=1 +DATA_GNT_WMAX=5 +DATA_RESP_WMAX=5 \
     +INTR_INTVL=2 +ntb_random_seed=55340      # bin: $R/issue/mirror/run/bin
  python3 $R/issue/gen/trace_shadow.py trace_kudu_core.log
  ```
  Reproduces on the original and fixed builds, c1/c2/c3. Does not occur at
  PMODE=0 or on simv32.
- **Suggested fix:** add `& ~instr_tmp2.rvfi.intr` to `is_good_clc`, and add an
  `$error` or assertion when `final_fifo` is full.

## KUDU-057: `amoand.w` disassembled as `INVALID`

- **Status:** Fixed in commit `c7598d2` (`INSN_AMOAND` added to both
  `tracer_pkg.sv` and `tracer_dpi.cpp`). Found by the issue/hazard review.
- **Verification** (`/home/scratch/fortress/kunyanliu/kudu_temp/k056_058_059_20261107_172203/`, `c7598d2` + working tree):
  - 318 AMO jobs on conf1/2/3 retire 1,122 `amoand.w` with 0 `INVALID`. Each has
    the correct rd field and rd write.
  - The earlier 424-run claim is withdrawn; see the KUDU-055 correction.
  - The SV-vs-DPI decoder testbench (3.26M decodes) shows no AMO mismatches;
    only the 12 known `c.ebreak` differences (KUDU-058) remain.
- **Severity:** Low (trace text). It also hides the rd write from trace-based
  checkers.
- **Location:** `rtl/tracer_pkg.sv:1838-1849`. The ATOMIC `case` lists LR, SC,
  AMOSWAP, AMOADD, AMOXOR, AMOOR and AMOMIN/MAX/MINU/MAXU, but not
  `INSN_AMOAND`, although it is defined at `:387`. The DPI tracer has the same
  omission: the pattern is defined at `rtl/tracer_dpi.cpp:46` but is missing
  from the match list at `:1175-1184`.
- **Observed:** `80001c2c 6277a52f INVALID`, with no operands and no rd write.
  1,122 instances in the issue review's reruns.
- **Expected:** `amoand.w x10,x6,x15 ... x10=<old value>`.
- **Suggested fix:**
  `INSN_AMOAND: decode_str = decode_amo_insn("amoand.w", rvfi_data);` in
  `tracer_pkg.sv`, and the matching line in `tracer_dpi.cpp`.

## KUDU-058: `c.ebreak` trace line has no PC or encoding

- **Status:** Fixed in commit `6722f7c` (`decode_mnemonic("c.ebreak", ...)`).
  Found by the fuzz review.
- **Verification:**
  - The SV-vs-DPI decoder testbench (3.26M decodes, `/home/scratch/fortress/kunyanliu/kudu_temp/k056_058_059_20261107_172203/`) shows 0 mismatches,
    down from 12.
  - The reproducer's `compare_trace.py` vs Sail passes on conf1/2/3 and on the
    DPI build. It fails on `c7598d2`.
  - In `/home/scratch/fortress/kunyanliu/kudu_temp/kfinal_20261107_183302/`, all 10 `c.ebreak` runs show no line without a PC or encoding.
- **Severity:** Low (verification infrastructure). The core executes
  `c.ebreak` correctly.
- **Location:** `rtl/tracer_pkg.sv:1507`
  (`decode_str = "c.ebreak";`). Every other mnemonic goes through
  `decode_mnemonic(...)`, which emits PC, encoding and the trap marker.
- **Observed:** `$R/fuzz/repro/tracer_cebreak/run_c1/trace_kudu_core.log:238`
  is just `2905000  281  c.ebreak`. `compare_trace.py` cannot parse it, and
  reports 316 equal records followed by 4,166 "not equal" because every later
  record is misaligned.
- **Reproducer:** `$R/fuzz/repro/tracer_cebreak/` (README has the commands).
  It reproduces on `build_c1`, `build2_c{1,2,3}` at PMODE=1, on `build2_c1/simv32`
  and on `simv` at PMODE=0.
- **Suggested fix:** `decode_str = decode_mnemonic("c.ebreak", rvfi_data);`

## KUDU-059: `+CAP_ERR_RATE` has no effect

- **Status:** Fixed in commit `94e007e`: the plusarg and its unused signals are
  removed from `sim/tb/tb_kudu_top.sv`. Found by the LSU review.
- **Verification:**
  - The committed `tb_kudu_top.sv` is byte-identical to the one built in
    `/home/scratch/fortress/kunyanliu/kudu_temp/kfinal_20261107_183302/`.
  - Full regression on conf1/2/3 (`/home/scratch/fortress/kunyanliu/kudu_temp/k056_058_059_20261107_172203/`): 246 PASS, 9 XFAIL, 0 FAIL each.
  - The `+CAP_ERR_RATE` references were also removed from `sim/testplan/README.md`
    and `.github/copilot-instructions.md`.
- **Severity:** Low (testbench). Capability tag errors on the data bus are never
  injected, so that error path is untested by every regression that sets the
  plusarg.
- **Location:** `sim/tb/tb_kudu_top.sv`. `cap_err_rate` is parsed at `:148-149`
  and printed at `:157`, and `cap_err_enable` is computed at `:561`, but
  neither feeds the memory models.
- **Suggested fix:** wire `cap_err_rate`/`cap_err_enable` into the data memory
  model's tag-error injection, or remove the plusarg.

---

## Code-review notes (no architectural effect observed)

| Location | Observation |
|---|---|
| `rtl/branch_predict.sv:188-195` | `is_branch` is gated by `errs.fetch_err`, but `is_jal`/`is_jalr_ra` are not. A fetch-error word whose data decodes as JAL or `jalr x0,0(ra)` still redirects fetch speculatively (possibly to MMIO). The errored instruction traps before anything younger retires; 150 fetch-error runs were clean. Not a bug: the designer classifies this as a don't care (2026-11-15). |
| `rtl/issuer.sv:627-628` | `csr_mispredict_o = ctrl_fsm_cs[CSM_DECODE] & (m0 && i0) \|\| (m1 && i1)`: the ir1 term is not gated by CSM_DECODE. Harmless today (ir1 issues only in DECODE); add parentheses. |
| `rtl/branch_predict.sv:262-290` (conf2) | BTB/JTB entries are untagged and the valid bit is ignored. Correctness is preserved by the EX target compare; performance only. |
| `rtl/rv32_alu.sv:412` | The no-RVB branch assigns undeclared `sext_result` (implicit net) and leaves `ext_result` undriven. Every config enables RVB. |
| `rtl/alu_pipeline.sv` | The two-stage option is dead code; every instance is single-stage. |
| `rtl/ir_decoder.sv` | OP-IMM bitmanip legality is gated by RV32M; `dec_cjalr` is not masked by the decode error. Neither is observable. |
| `rtl/tracer_pkg.sv` | A failed `sc.w` (no memory write) is still printed with a `store:` annotation. Cosmetic. |
| `rtl/fetch_fifo64.sv:218` | "QQQ fetch_err for unalignedFetch not completely handled": only affects the unused `UnalignedFetch` mode. |

## New Sail divergences (implementation choices, Kudu acceptable)

| Behaviour | Kudu | Sail |
|---|---|---|
| x16–x31 in an instruction that would also fault (misaligned/CHERI) | Illegal instruction (higher priority) | Other fault first |
| `mstatus.SIE` | Reads 0 (no S-mode) | Writable |
| `sfence.vma` | Illegal | Accepted |
| `cycle`/`time`/`instret` (0xC00–0xC02), `cycleh` (0xC80) | Illegal at both PMODEs (same as cheriot-ibex) | Implemented, on the no-ASR allow-list. Belongs to the performance-counter area. |
| `mccsr`, 0xBC4, 0x7C0/0x7C1, `mvendorid`, `mip.MTIP` | Platform-specific values/legality | Different |

## Areas checked clean (with evidence)

All runs are in `$R/<area>/`. "Wait states" means random
`+INSTR/DATA_GNT/RESP_WMAX`.

| Area | Method | Result |
|---|---|---|
| Front end (fetch, FIFO, prediction, ALT, redirect) | 70 random self-checking runs (ALT stress, new front-end generator with skip-returns, odd jump tables, straddling 32-bit instructions, `fence.i`, predictor toggles, interrupts), with every retired PC/encoding checked against the ELF (~8.4M instructions); `fe_smc` (128 SMC/`fence.i` cases); `fe_ferr` (25 fetch bus-error cases × 156 runs); `fe_pcc`/`fe_pcc2` (96 PCC fetch-bound cases vs Sail) | Clean on c1/c2/c3, PMODE 0/1, simv32, with and without wait states and interrupts; PCC cases byte-identical to Sail |
| Decode / legality | All 65,536 compressed encodings; 32-bit op (32,768), op-imm (8,768), system (22,646, every CSR), ~17k mixed (loads/stores, AMO, FENCE, CHERI 0x5B with every SCR, x16–x31); slot-1 vs slot-0 placement; 2-byte-shifted straddling illegal instructions; 16-bit mtval zero-extension (12,000) | 0 unexplained mismatches vs Sail (PMODE=1), simv32 and Python RVC/spec models (PMODE=0); conf2/conf3 identical to c1 |
| Execution units / CHERI ALU | ~1,100 random/directed runs vs Sail (~4.3M trace objects): CHERI ops, bitmanip, M ext, dependent chains, 200 sentry/MIE vs faulting load cases | 0 functional mismatches |
| LSU / data path | Directed: `lsu_rvk_lrsc`, `lsu_rvk_race`, `lsu_mshwm_amo`, `lsu_split_*`. Random on build2: 30 seeds, 90 CHERIoT stress runs vs Sail, 60 RV32 stress runs vs a Python model, 60 bus-error replays (1,262 faults) | Clean apart from KUDU-051 (fixed) and KUDU-052 |
| Issue / hazard / commit | 3,846 random hazard-heavy self-checking runs (WAW/RAW, long-latency ops, clc/trvk, AMO/LR/SC, WFI, faults, interrupts) with a trace shadow-register checker; 26 seeds vs Sail | All signatures correct; shadow failures traced to KUDU-055/056/057 |
| CSR / trap / interrupt | `csr_probe_rv32` (119), `csr_probe_cheri` (155), `mret_cheri` (12), `irq_rv32` (492), `irq_cheri` (70), with a shadow TB driving IRQ lines from software | All differences are WARL/platform choices or already logged (KUDU-018/019/034/038/041/042) |
| Random differential fuzz | ~640 programs (~4,700 simulations): 240 CHERIoT vs Sail, 120 RV32 vs cheriot-ibex, `simv +PMODE=0` vs `simv32`, AMO kudu-vs-kudu; `FZ_AMO_CLC` mode for KUDU-051 | No core bug; KUDU-058 found |
| Static | VCS `+lint=all` on the full design; Verilator `-Wall` on `mult_pipeline` | KUDU-053, KUDU-054; remaining warnings by design |

### Known gaps

- Capability tag-error injection on the data bus was never exercised (KUDU-059).
- The interrupt tests ran on the original-RTL shadow TB only. The KUDU-051 fix
  does not touch that logic, and the static CSR probes gave identical results
  on `build2_c1`.
- U-mode interrupt/mret/wfi (KUDU-034/038) and debug were out of scope.
- AMO results have no independent golden model (Sail and ibex lack RV32A);
  they were checked by self-checking signatures and kudu-vs-kudu only.
- The shared home filesystem filled up for about 18 minutes (≈05:00–05:18)
  during the review. Every run affected in that window was identified and
  rerun.

---

# Review round 3 (CHERIoT-focused)

Third review, 2026-11-05, on the same RTL as round 2 (HEAD plus the
uncommitted KUDU-051 fix; `rtl/` byte-identical throughout the review). Debug
and performance counters were excluded. This round put the emphasis on the
CHERIoT instructions: each area agent first wrote an independent model from
the Sail source (`MODEL.md`, with a corner-case table) and then hit every
table row with directed tests on conf1/2/3, with and without memory wait states.

- **Scratch area:** `/home/scratch/fortress/kunyanliu/review3_20261105_125256/` (`$R3` below).
  `$R3/build_c{1,2,3}` = current RTL plus the KUDU-055..058 tracer fixes
  (`$R3/tracer_fixes.patch`), so trace comparison is no longer polluted by
  those tracer bugs. Area reports: `$R3/{capmodel,cinsn,cmem,cpipe,cfuzz,covhunt,freshrev}/REPORT.md`;
  my independent re-verification runs: `$R3/verify/`.

## Summary (round 3)

| ID | Status | Severity | Area | Location | Summary | Reproducer |
|---|---|---|---|---|---|---|
| KUDU-060 | **Not a bug** (by design) | — | CHERI load barrier | `rtl/cheri_trvk_stage.sv:52,93` | CLC revocation lookup (indexed by the loaded cap's base) can observe a store to the bitmap issued right after the CLC; differs from Sail, accepted CHERIoT behaviour | `$R3/cmem/M/tests/cm_rvkwar`, `cm_rvk` (cases 103/104) |
| KUDU-061 | **Fixed** (`ff98820`) | Low | CHERI/LSU trap | `rtl/cheri_pkg.sv:1048-1050`, `rtl/cmplx_unit.sv:162,167` | AMO through a cap with LD but no SD reports bounds/misaligned instead of the SD violation | `$R3/cmem/M/tests/cm_rep_amo` |
| KUDU-062 | **Waived** | Low (metadata only) | CHERI PCC/trap | `rtl/cheri_pkg.sv:101-111,644-725`, `rtl/cs_registers.sv:1835` | MEPCC written on a trap loses B/T bits when the PCC exponent is ≥ 24 | `$R3/capmodel/M/tests/cd_mepcc_0` |
| KUDU-063 | **Deferred** (low) | Low (testbench) | TB | `sim/tb/data_mem_model.sv:315` | A failed SC.W still writes the memory tag bit | Code review; `$R3/cmem` `cm_amo1`/`cm_amo2` |

## KUDU-060: CLC revocation lookup can observe a younger store to the bitmap — not a bug (by design)

- **Status:** closed, not a bug (design owner, 2026-11-06). The revocation
  bitmap index must be computed from the *base of the loaded capability*, so the
  lookup can only start after the CLC data has returned
  (`rtl/cheri_trvk_stage.sv:44-52,93`). This is how CHERIoT revocation works;
  cheriot-ibex uses the same structure.
- **Observation, kept for reference so it is not re-reported:** a store to the
  revocation bitmap issued immediately after a CLC (0-2 instructions, or a few
  more with memory wait states) can be visible to that CLC's lookup. Directed
  tests `$R3/cmem/M/tests/cm_rvkwar` and `cm_rvk` cases 103/104 differ from
  Sail on conf1/2/3 for this reason (`$R3/verify/rvk*`). Sail performs the
  lookup atomically with the load. Tests that store to the bitmap must keep
  such stores away from in-flight CLCs, or filter these cases when comparing
  against Sail.

## KUDU-061: AMO with LD-only authority reports bounds/misaligned instead of SD violation

- **Status:** Fixed in commit `ff98820`.
  - `check_ls_err` now sets
    `result.sd = (~is_load | amo_flag[2]) && ~perms[PERM_SD]`, so the AMO
    read phase checks SD as well.
  - The matching `amo_flag[2]` term added to `result.ld` is redundant (the
    read phase always has `is_load=1`) but harmless.
  - LR/SC are unchanged.
- **Verification** (`/home/scratch/fortress/kunyanliu/kudu061_20261106_224511/`):
  - `cm_rep_amo` on conf1/2/3: all 4 cases now report mcause 0x1c,
    mtval 0xb3. Memory, tag and rd are unchanged from the pre-fix run.
  - `lsu_rvk_lrsc` (KUDU-051 test) still gives 22/22 PASS on conf1/2/3.

- **RTL:** `rtl/cheri_pkg.sv:1048-1050` (`check_ls_err`):
  `result.sd = ~is_load && ~cs1_fcap.perms[PERM_SD]`. The AMO read phase is sent
  with `is_load=1`, `amo_flag=4'b0100` (`rtl/cmplx_unit.sv:162,167`), so SD is
  only checked in the write phase, which never starts if the read phase faults.
- **Expected:** `sail-riscv/model/riscv_insts_aext.sail:219` calls
  `ext_data_get_addr(..., ReadWrite(Data, Data), ...)` first;
  `src/cheri_addr_checks.sail:207-214` checks tag → seal → LD → **SD** → bounds.
  So an AMO through a cap without SD always gives mcause 0x1c, mtval
  `(rs1<<5)|0x13`.
- **Re-verified** (`$R3/verify/amo_build_c{1,2,3}_w0`, identical on all configs):

  | case | Kudu mcause / mtval | expected |
  |---|---|---|
  | amoadd, no SD, in bounds | 0x1c / 0xb3 | 0x1c / 0xb3 ✓ |
  | amoadd, no SD, at top | 0x1c / **0xa1** (bounds) | 0x1c / 0xb3 |
  | amoswap, no SD, misaligned 0x80023002 | **6 / 0x80023002** | 0x1c / 0xb3 |
  | amoadd, no SD, zero-length cap | 0x1c / **0xa1** | 0x1c / 0xb3 |

  This Sail build has no A extension (it returns illegal instruction), so the
  expected column comes from the Sail source quoted above. Memory, tag and rd
  are unchanged in every case, so there is no security impact; only the
  reported cause is wrong.
- **Suggested fix:** `result.sd = (~is_load | amo_flag[2]) & ~cs1_fcap.perms[PERM_SD];`
  (LR, `amo_flag[0]`, must stay load-only).

## KUDU-062: trap MEPCC loses upper B/T bits when the PCC exponent is ≥ 24 — waived

- **Status:** waived (design owner, 2026-11-06). CHERIoT is not expected to
  use capability exponents larger than 24; a PCC with E ≥ 24 can only arise
  from an untagged, malformed capability. The details are kept below for
  reference so this is not re-reported; Sail comparisons that construct such a
  PCC should filter the resulting MEPCC metadata mismatch.

- **RTL:** `pcc_cap_t` (`rtl/cheri_pkg.sv:101-111`) holds only
  `base32/top33/exp`. `pcc2fullcap`/`pcc2fullcap_lite`/`pcc2regcap`
  (`:644-725`) rebuild B/T by shifting base/top right by E, which drops bits
  for E ≥ 24. The result is written to MEPCC on a trap
  (`rtl/cs_registers.sv:1835`).
- **Expected:** `cheri_sys_exceptions.sail:71-80` copies the PCC bit-exactly
  into MEPCC.
- **Trigger:** a PCC with E ≥ 24 is only possible as an untagged, malformed cap,
  e.g. `csethigh` a cap, `cspecialw mepcc`, `mret` → fetch fault, and the trap
  writes a truncated MEPCC (`cgethigh` 0x5E0E803F vs Sail 0x5E0E813F).
- **Re-verified:** `$R3/verify/mepcc/c{1,2,3}`: 43 of 10,535 trace objects
  differ from Sail on every config, all of them MEPCC metadata. Found
  independently by two agents (capmodel at function level, 75,057 mismatching
  vectors all with E ≥ 24; cinsn at instruction level).
- **Impact:** metadata only, on an untagged cap; no security effect.
  cheriot-ibex has the same structure.
- **Suggested fix:** carry the encoded 9-bit B/T in `pcc_cap_t` (or keep the
  raw MEPCC metadata) instead of re-deriving them.

## KUDU-063: TB memory model writes the tag on a failed SC.W

- **Status:** Deferred (low) by the design owner on 2026-11-06. AMO/LR/SC are
  not expected to be used to access capability storage, so the ungated tag
  write does not affect intended usage. Kept for reference; tests that use
  SC.W on capability granules may see a tag mismatch.

- **Location:** `sim/tb/data_mem_model.sv:315`:
  `if (dram_cs && mem_we) dram[dram_addr][64] <= mem_wdata[64];` runs on every
  write. Unlike the data writes (lines 293, 302) it is not gated by
  `(~mem_amo_flag[1] | dram_lr_status_q)`, so a failed SC.W on a capability
  granule clears that granule's tag.
- **Impact:** testbench only. In a real system the memory decides SC success
  and suppresses the whole write, tag included. It can mask or create
  tag-related mismatches in LR/SC tests.
- **Suggested fix:** apply the same SC-success gate to the tag write.

## Round-3 code-review notes (no architectural effect observed)

- `rtl/cs_registers.sv:1641-1642` declares `cheri_mpecc_wr` and `rv32_decc_wr`
  (misspelled); the names used at 1650-1651 (`cheri_mepcc_wr`, `rv32_depc_wr`)
  become implicit 1-bit nets. Behaviour is correct, but it breaks under
  `` `default_nettype none `` (freshrev).
- `rtl/dcache.sv` (~174-192): the forwarding valid bit has no flush term and
  stays set for one cycle after a commit flush. It is safe today only because
  the issuer always spends at least one cycle in WAIT_TRVK before it can issue
  again; adding `flush_i` to the clear condition is recommended (freshrev).
- CJALR changes MIE before an older load/store has finished. It is correct
  today because the trap uses the MIE captured at load/store issue, so any new
  late-fault source outside that pipe would break it (cpipe).
- Operator-precedence quirks in `rtl/issuer.sv:626-627` and `rtl/dcache.sv:155`
  are benign (cpipe, covhunt).

## Round-3 areas checked clean (with evidence)

| Area | Evidence |
|---|---|
| Capability functions (`cheri_pkg.sv`, `cheri_alu`) | 15.16 M random vectors plus exhaustive sweeps (all perm encodings, otypes, exponents, corrections, ~595 K mem→reg→op→full→mem round trips) vs a Python model; the model matched Sail on 4,039 setbounds corners. Only KUDU-062 found. |
| Non-memory CHERI instructions, sentries, SCRs | 18 directed ELFs × conf1/2/3 × wait states vs Sail: 64,646 trace objects equal, all other diffs the known MPP readback. 16,731 IRQ-arrival sweep runs around CJALR, sentry returns, mret and CSpecialRW: no interrupt taken inside an interrupt-disabling sentry. |
| CHERI memory access | Load/store cap checks, CLC/CSC, store-local, CLC attenuation (no LG/LM/MC), sealed caps, revocation address mapping, partial/misaligned store tag clearing, MSHWM (incl. LR/SC/AMO), dcache forwarding, bus errors with wait states: all PASS vs Sail/self-check on conf1/2/3 (except KUDU-061; KUDU-060 timing difference is by design). |
| CHERI × pipeline | Cap-metadata forwarding: 38 producers × 33 consumers × distance 0-4 × both slots; PCC changes at every 2-byte offset of the new top; sentry/IRQ cycle sweeps; kills of younger CHERI/multi-cycle ops: 112,683 + 24,192 cell-runs PASS. Mutation check: 3 injected faults all caught. |
| Capability-aware fuzzing | 317 programs × conf1/2/3 × wait states (~3.15 M instructions per variant) vs Sail; 1,611 corner classes hit (round 2: 541). Only the known MPP difference. |
| Coverage-guided holes | Every uncovered item in 20 modules hit by a passing test or justified unreachable; ~140 K self-checking exception/interrupt × multi-cycle-op × wait-state cases PASS. E.g. multdiv32 cond 69→100 %, cs_registers line 81→96 %, cmplx FSM 67→83 %. |
| Bug-dense files, line by line | issuer, LSU, ls_pipeline, committer, cmplx_unit, waw_tracking_fifo, fetch_fifo64: state-register set/clear/flush audit, flag-list completeness, 19 directed rows × 4 seeds × 6 variants PASS; Verilator `-Wall` on all configs: nothing new beyond the notes above. |

# Tracer consistency check: SystemVerilog vs DPI-C

Check run on 2026-11-06 against the current `rtl/`: does `tracer_pkg::decode_rvfi_instr_vlog`
(SV) produce the same text as `tracer_dpi.cpp` `decode_rvfi_instr` (C, selected
by `+define+TraceDPI`)? Only the formatter differs between the two flows; the
retire loop in `rtl/tracer.sv` is shared.

- **Scratch area:** `/home/scratch/fortress/kunyanliu/tracer_cmp_20261106_023805/` (`$TC` below).
- **Standalone differential TB** (`$TC/tb_trc.sv`): both formatters get the same
  `rvfi_t` packet. Builds: CHERIoT with pmode 0 and 1 (`$TC/b_cheri`), and RV32
  (`$TC/b_rv32`). Stimulus:
  - every 16-bit encoding;
  - every opcode × funct3 × funct7 × rs2 combination;
  - every CSR × funct3 combination;
  - 500 K random words;
  - random trap/intr, register and capability data, and memory masks.

  Results: 3.26 M comparisons, 59.8 K mismatches, all in the classes below.
  Full log: `$TC/b_cheri/mismatch_full.log`.
- **Full-core** (`$TC/core_{dpi,vlog}`, `$TC/runs`): the 12 mini-regression
  tests (with and without `+INTR_INTVL`/memory delay/error injection) give
  identical traces except where DPI prints X values as 0, which is expected.
  These tests do not exercise KUDU-064/065.
- Register, capability, memory and trap/interrupt annotation formatting matched
  everywhere. Existing tracer bugs KUDU-057 (`amoand.w`, missing in both) and
  KUDU-058 (bare `c.ebreak`, SV only) were reproduced and are not repeated here.

## Summary (tracer consistency)

| ID | Status | Severity | Side | Location | Summary |
|---|---|---|---|---|---|
| KUDU-064 | **Fixed** (`0ab3b26`) | Medium (trace) | C | `rtl/tracer_dpi.cpp:45-53,170,222` | AMO/LR/SC masks ignore insn bit 31 (and LR ignores bit 24): `amomin/amomax/amominu.w` print as `amoadd/amoxor/amoor.w` |
| KUDU-065 | **Fixed** (`0ab3b26`) | Medium (trace) | SV | `rtl/tracer_pkg.sv:1149,1185` | `c.CH.clcsp`/`c.CH.cscsp` offset truncated to 8 bits; offsets ≥ 256 print wrong |
| KUDU-066 | **Fixed** (`0ab3b26`) | Low (trace) | SV | `rtl/tracer_pkg.sv:1234` | Loads with funct3 = 6/7 print a bare `INVALID` with no PC/encoding |
| KUDU-067 | **Fixed** (`0ab3b26`) | Low (trace) | C, and SV for `fence.i` | `rtl/tracer_dpi.cpp:89-105,155-159,176,259`, `rtl/tracer_pkg.sv:307` | Decode patterns disagree with `ir_decoder.sv`: C decodes illegal SYSTEM/CHERI encodings as valid instructions; both tracers mis-handle `fence.i` with non-zero reserved fields (SV prints `INVALID` for an instruction the core executes) |
| KUDU-068 | **Fixed** (`0ab3b26`) | Cosmetic | both | `rtl/tracer_pkg.sv:457,705`, `rtl/tracer_dpi.cpp:372,619` | Unnamed CSR/SCR formatting differs: `0x006` vs `0x6`, `scr 4` vs `scr4` |
| KUDU-069 | **Fixed** (`ff98820`, `774ec06`) | Medium (flow) | — | `sim/run/vcscomp:26-35` | `-dw`, `-trace_dpi` and `-nowave` all set `VlogArg3`; the last flag wins, so `-trace_dpi -nowave` silently builds without DPI |

## KUDU-064: DPI tracer prints amomin/amomax/amominu as amoadd/amoxor/amoor

- **Status:** Fixed in commit `0ab3b26` (masks widened as suggested).
  Differential TB (`$TC/b2_*`): 0 AMO/LR/SC mismatches.
- **Location:** `rtl/tracer_dpi.cpp:45-53` (`INSN_AMOADD/XOR/OR/SWAP/AND`), `:170`
  (`INSN_LR`) and `:222` (`INSN_SC`).
  - These patterns use mask `0x7800707f`, which covers funct5 bits 30:27
    but not bit 31.
  - Because `decode_rvfi_instr_cpp` (`:1175-1184`) tests ADD/XOR/OR before
    MIN/MAX/MINU, an instruction with funct5 bit 4 set matches the
    funct5 & 0xf instruction first:
    - `amomin.w` (0x10) is printed as `amoadd.w`;
    - `amomax.w` (0x14) as `amoxor.w`;
    - `amominu.w` (0x18) as `amoor.w`.
  - `amomaxu.w` only prints correctly because `amoand` is missing (KUDU-057).
  - Reserved funct5 values 0x11/0x13 decode as `amoswap.w`/`sc.w`.
  - `INSN_LR`'s mask `0x78f0707f` also ignores rs2 bit 24.
- **SV reference:** `rtl/tracer_pkg.sv:382-392` specify all 5 funct5 bits.
- **Example:** insn `a00eafaf`: SV `amomax.w x31,x29,x0`, C `amoxor.w x31,x29,x0`.
- **Impact:** with `-trace_dpi`, every amomin/amomax/amominu line is
  mis-disassembled, so traces diff against cheriot-ibex or the SV-tracer build.
- **Suggested fix:** widen the masks to `0xf800707f` (LR: `0xf9f0707f`).

## KUDU-065: SV tracer truncates the c.CH.clcsp / c.CH.cscsp offset

- **Status:** Fixed in commit `0ab3b26` (`imm` is now `logic [8:0]`).
  Differential TB (`$TC/b3_*`): 0 clcsp/cscsp mismatches. The same bug is
  present in the cheriot-ibex tracer (`ibex_tracer.sv`), which produces the
  golden traces; an upstream issue draft is in
  `/home/scratch/fortress/kunyanliu/issue_drafts/cheriot-ibex_tracer_clcsp_imm.md`.
- **Location:** `rtl/tracer_pkg.sv:1149` (`decode_compressed_load_insn`) and
  `:1185` (`decode_compressed_store_insn`).
  - `imm` is declared `logic [7:0]`, but the stack-relative CLC/CSC offsets are
    9 bits:
    - load: `{insn[4:2], insn[12], insn[6:5], 3'b000}`;
    - store: `{insn[9:7], insn[12:10], 3'b000}`.
  - Bit 8 is dropped on assignment.
  - The C version (`rtl/tracer_dpi.cpp:826,843`) uses a 32-bit `imm` and is
    correct.
  - The register-relative `c.CH.clc`/`c.CH.csc` forms are 8 bits and are not
    affected.
- **Example:** insn `6016`: SV `c.CH.clcsp c0,64(c0)`, C `c.CH.clcsp c0,320(c0)`
  (correct).
- **Impact:** the default (SV) trace shows the wrong offset for any CLCSP/CSCSP
  with an offset ≥ 256. PA and data are unaffected.
- **Suggested fix:** declare `imm` as `logic [8:0]`.

## KUDU-066: SV tracer prints a bare INVALID for loads with funct3 = 6/7

- **Status:** Fixed in commit `0ab3b26` (`build_disp_str` now called on the
  `INVALID` string). Differential TB (`$TC/b5_*`): 0 bare `INVALID` lines.
- **Location:** `rtl/tracer_pkg.sv:1234` (`decode_load_insn`).
  - The reserved-size branch does `decode_str = "INVALID"; return decode_str;`.
  - It skips `decode_mnemonic`/`build_disp_str`, so the line has no PC, no
    encoding and no `-->` trap marker.
  - C (`rtl/tracer_dpi.cpp:863`) calls `decode_mnemonic("INVALID", d)`.
  - This is the same pattern as KUDU-058.
- **Example:** insn `000be783`: SV `INVALID`, C `<pc> 000be783 INVALID`.
- **Impact:** an illegal-instruction trap on these encodings produces a
  malformed trace line that does not line up with the golden trace.
- **Suggested fix:** `return decode_mnemonic("INVALID", rvfi_data);`

## KUDU-067: tracer decode patterns disagree with the core decoder (SYSTEM, CHERI single-operand, fence.i)

- **Status:** Fixed in commit `0ab3b26` (the `fix067.patch` below, applied
  unchanged). Differential TB on the committed RTL (`$TC/b7_*`): 0 SYSTEM,
  `fence.i` or CHERI single-operand mismatches. The new patterns were checked
  against riscv-opcodes and cheriot-sail (`cheri_insts.sail:1013-1026`).
- **Not fixed (follow-up):** both tracers still decode `CH.cgetsealed`
  (rs2 = 0x05, `fe50005b`) and `CH.cjalr` (rs2 = 0x0c, `fec0005b`).
  - Neither instruction exists in cheriot-sail or `ir_decoder.sv`, which
    rejects both as illegal; CHERIoT's `cjalr` uses the standard JALR opcode
    (`ir_decoder.sv:193`).
  - Locations: SV `rtl/tracer_pkg.sv:353,376`, C `rtl/tracer_dpi.cpp:98,104`.
  - The two tracers agree, so the differential TB does not flag these.
The reference is what `rtl/ir_decoder.sv` accepts. A tracer should name an
encoding only if the core executes it, and print `INVALID` otherwise.

| Instruction(s) | Core decoder (`ir_decoder.sv`) | C pattern / mask (`tracer_dpi.cpp`) | SV pattern (`tracer_pkg.sv`) | Wrong side | Example insn |
|---|---|---|---|---|---|
| `ecall`, `ebreak`, `mret`, `dret`, `wfi` | exact funct12 **and** `instr[19:7] == 0` (`:436-460`); anything else is illegal | `:155-157,176,259`, `0xfff000ff`: ignores rd[3:0], funct3, rs1 | exact (`:63-67`) | C | `00090e73` (C `ecall`, core: illegal) |
| CH single-operand ops (`cgetperm/type/base/len/tag/sealed/addr`, `ccleartag`, `cmove`, `crrl`, `cram`, `cjalr`) | full 5-bit rs2/imm5 field checked (`:532` onward) | `:89-105`, `0xfef0707f`: ignores bit 24 | exact (`:346-376`) | C | `ff0b055b` (C `CH.cgetperm`, core: illegal) |
| `fence.i` | only `funct3 == 001` checked (`:418-425`); imm/rs1/rd ignored, as the Zifencei spec requires | `:159`, `0x0007f7ff`: requires rd[3:0], rs1[3:0] = 0, ignores imm, rd[4], rs1[4] | `:307` requires imm/rs1/rd = 0 | **both** | `0180180f` (core executes `fence.i`; SV prints `INVALID`) |
| `lr.w`, `sc.w`, `amoswap.w` | — | see KUDU-064 | — | C | `1102222f` |

- In C, `CH.cgettop` (rs2 = 0x18) still decodes correctly only because it is
  tested before `CH.crrl` (0x08), whose mask would otherwise match it.
- **Impact:** low (trace only).
  - The SYSTEM/CHERI encodings trap as illegal in the core, but their trap
    line shows a valid mnemonic in DPI traces.
  - A `fence.i` with non-zero reserved fields executes in the core, but its
    line reads `INVALID` in SV traces.
- **Suggested fix** (verified with the differential TB: every KUDU-067
  mismatch removed, no new mismatch classes, CHERIoT and RV32 builds); patch
  in `/home/scratch/fortress/kunyanliu/tracer_cmp_20261106_023805/fix067/fix067.patch`:
  - `tracer_dpi.cpp`: CH single-operand masks `0xfef0707f` → `0xfff0707f`;
    `ecall/ebreak/mret/dret/wfi` masks `0xfff000ff` → `0xffffffff`;
    `INSN_FENCEI` mask `0x7f7ff` → `0x707f`.
  - `tracer_pkg.sv:307`: `INSN_FENCEI = { 17'h?, 3'b001, 5'h?, {OPCODE_MISC_MEM} }`.

## KUDU-068: unnamed CSR / SCR operands are formatted differently

- **Status:** Fixed in commit `0ab3b26`. C now matches SV: `fmt("0x%03x")`
  (`rtl/tracer_dpi.cpp:619`) and `fmt("scr%2u")` (`:372`); SV unchanged.
  Differential TB on the committed RTL (`$TC/b10_*`): 12 (CHERIoT) / 6 (RV32)
  mismatches remain, all `c.ebreak` (KUDU-058).
- **Location:**
  - SV `$sformatf("0x%x", csr_addr)` (`rtl/tracer_pkg.sv:705`) zero-pads the
    12-bit value (`0x006`). C `fmt("0x%x")` (`rtl/tracer_dpi.cpp:619`) does not
    (`0x6`).
  - SV `$sformatf("scr%d", scr_addr)` (`:457`) space-pads the 5-bit value
    (`scr 4`). C `fmt("scr%u")` (`:372`) does not (`scr4`).
- **Impact:** cosmetic. It only affects CSR/SCR addresses with no name in the
  tables, but every such line diffs between SV and DPI traces.
- **Suggested fix:** pick one form, e.g. `0x%03x` in C and `scr%0d` in SV.

## KUDU-069: vcscomp `-trace_dpi` is silently dropped when combined with `-nowave` or `-dw`

- **Location:** `sim/run/vcscomp:26-35`.
  - `-dw` sets `VlogArg3="+define+KUDU_DW_MULT=1"`;
  - `-trace_dpi` sets `VlogArg3="+define+TraceDPI"`;
  - `-nowave` sets `VlogArg3="+define+NO_FSDB"`.
- **Effect:** only the last of these flags takes effect:
  - `./vcscomp -trace_dpi -nowave` builds the SV tracer with no warning;
  - `-dw -nowave` loses `KUDU_DW_MULT` (the `kudu_dw.vcs.f` file list is still
    selected).
- **Suggested fix:** give each flag its own variable (e.g. `VlogArg4` for
  `-trace_dpi`, `VlogArg6` for `-nowave`).
- **Status:** Fixed in commits `ff98820` (`vcscomp`) and `774ec06`
  (`kudu_dw.vcs.f` repair below).
  - `vcscomp` now gives each flag its own variable: `-dw` → `VlogArg3`,
    `-dii` → `VlogArg4`, `-trace_dpi` → `VlogArg5`, `-nowave` → `VlogArg6`.
  - `-cov` is added via `InputArgs`.
  - A new `-outdir=<dir>` option builds outside `sim/run`.
  - `kudu_dw.vcs.f` was also repaired: `-dw` builds failed because it lacked
    `kudu_cfg_pkg.sv` and listed the deleted `tb/instr_mem_model.sv`.
- **Verification** (scratch: `/home/scratch/fortress/kunyanliu/vcscomp069_20261106_220405/`):
  - **Defines:** every VCS command line contains all the requested defines
    for these builds:
    - `-trace_dpi -nowave`;
    - `-cov -dii -trace_dpi -nowave`, which also gets the fcov list and `-cm`;
    - `-dw -nowave -trace_dpi`;
    - `-trace_dpi -nowave -cov` without `-outdir`, built in a mirrored tree.
  - **DPI:** the DPI import is present in `vc_hdrs.h` for every `-trace_dpi`
    build.
  - **Runs:** `isa_test1` and `coremark.cheriot` (DW multiplier) pass, and no
    build writes an fsdb.
  - **Trace check:** the DPI and SV traces of `isa_test1` are byte-identical.
