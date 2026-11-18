<!--
Copyright Microsoft Corporation
Licensed under the Apache License, Version 2.0, see LICENSE for details.
SPDX-License-Identifier: Apache-2.0
-->

# Functional coverage vs. RTL bug cross-check

Status: implemented on 2026-11-14 (see §7 for what was built and how it
differs from the proposals below). §1–§6 are kept as the original review.

Scope: the bind-based functional coverage model in `sim/fcov` at HEAD c708e3c,
checked against every bug in `bug_logs.md`, `bug_logs_2.md`, `bug_logs_3.md`
and `debug_bugs.md` (KUDU-001 .. KUDU-074).

The question asked of each bug: *had this coverage model been run on a
regression that fills every bin, would the stimulus that exposes the bug
necessarily have been generated?* Coverage only proves stimulus; detection still
comes from the checkers (trace diff against cheriot-ibex / Sail, self-checking
tests, SVA). Where a bin can also act as a tripwire (a "correct-outcome" bin
that cannot fill while the bug exists, or an `illegal_bins` + SVA pair), that is
noted.

Design rule followed throughout: **minimise changes to existing code.** Every
proposal below is either (a) a new coverpoint/cross added inside an existing
covergroup, or (b) one new covergroup in an existing file. New signals come in
through the existing `.*` binds by declaring ports whose names already exist in
the bound RTL scope, so most proposals need no bind edits at all.

---

## 1. Prerequisite: the model does not currently compile

The fcov model fails to elaborate on HEAD, in every configuration. Nothing else
in this document matters until this is fixed.

| Tool | Result on HEAD |
|---|---|
| `check_syntax.py --matrix` (pyslang, KuduCfg1/1x/2/3 × CHERIoT 0/1) | 4 errors in all 8 configurations |
| `vcscomp -cov -nowave` (VCS Y-2026.03-SP1) | `Error-[IIPCNDI]` × 2, no `simv` built |

Errors:

1. `kudu_fcov_bind.sv:121` — the issuer bind uses `.*`, but
   `kudu_fcov_issue` still has ports `debug_single_step_i` and
   `single_step_trap_q`. Commit 127aade (2026-11-09) renamed the issuer port
   `debug_single_step_i` → `debug_step_i` and replaced the internal
   `single_step_trap_q` with `step_req_q`. This is exactly the failure mode the
   `.*` rule is meant to catch, so the rule worked; the model was simply not
   rebuilt after that RTL change. Coverage databases produced after 127aade
   cannot have come from HEAD RTL.
2. `kudu_fcov_if.sv:473` — `coverpoint pdt_pc_set iff pdt_en_i {` is missing the
   parentheses required by the LRM (`iff (pdt_en_i)`). VCS accepts it; pyslang
   (and likely other simulators) do not.

Minimal fix (verified in a scratch copy: pyslang matrix 0 errors in all 8
configurations, VCS `-cov -nowave` builds both `simv` and `simv32` with 0
errors, and `isa_test1`, `cheri_test1`, `dbg_test1` pass on the rebuilt
`simv` with no `illegal_bins` hit; scratch area
`/home/scratch/fortress/kunyanliu/kudu_temp/fcov_review_20261114_144820`):

```systemverilog
// kudu_fcov_bind.sv, issuer bind — append to the explicit connections
  .irq_fast             (irqs_i.irq_fast),
  .debug_single_step_i  (debug_step_i),   // renamed in issuer.sv (127aade)
  .single_step_trap_q   (step_req_q)      // replaces single_step_trap_q (127aade)
);

// kudu_fcov_if.sv:473
    cp_pdt_pc_set: coverpoint pdt_pc_set iff (pdt_en_i) {
```

(Renaming the two ports inside `kudu_fcov_issue.sv` and dropping the explicit
connections is equally valid and avoids the comments; it touches four lines
there plus `tb_fcov_frontend_temporal.sv`, which also uses
`single_step_trap_q`.)

Add `check_syntax.py --matrix` to whatever runs after an RTL change (it needs
no licence and takes a few minutes), so a port rename cannot silently disable
coverage again.

### 1.1 Mislabelled / stale points found during the review

| Location | Problem | Fix |
|---|---|---|
| `kudu_fcov_issue.sv:1016` `cp_dbg_entry_src` | Bin `ebreak` samples `ir0_dec.is_brkpt`, which is the **trigger** match (`ir_decoder.sv:115`, `ir_stage.sv:328-335`), not ebreak. The ebreak entry term `ebreak_enter_debug` is not sampled at all. | Rename bin to `trigger`; add `ebreak_enter_debug` (see §3.2). |
| `kudu_fcov_issue.sv:1016` `cp_dbg_entry_src` | `multiple` lumps every combination; the step+ebreak, step+trigger and step+haltreq races (KUDU-030/040/071) are indistinguishable. | Split (see §3.2). |
| `kudu_fcov_issue.sv:1025-1034` `cp_dbg_cause_sel` comment | Refers to "finding F-06" (HALTREQ during step → STEP). That is KUDU-040, fixed in d290cd0. `none` is now the documented KUDU-073 waiver. | Update comment only. |
| `kudu_fcov_issue.sv:1060-1068` `cp_sleep_wake` comment | "by_debug expected unreachable, see F-02". F-02 = KUDU-003, fixed in 802d481; the bin is now an ordinary goal. | Update comment only. |
| `kudu_fcov_csr.sv:208-211` `cp_step_with_ie` | `dcsr.stepie` is hardwired to 0 (`cs_registers.sv:703`, KUDU-029 fix), so the bin can never fill. | Mark `ignore_bins`/`option.weight = 0` with a KUDU-029 comment, or remove. |
| `kudu_fcov_issue.sv` `sample_cheri_dep` (~1102) | `consumer_class` is in the event struct and has a coverpoint (`cp_consumer_class`, l.367) but the CHERI_DEP sample never fills it. | Fill it (see §3.5). |

---

## 2. Cross-check summary

Legend:
**C** = covered by an existing bin (stimulus guaranteed);
**P** = partial — the individual features are covered but not the
combination that exposed the bug;
**G** = gap — nothing in the model forces the stimulus;
**N/A** = not a stimulus problem (lint, tracer, testbench, flow, by-design) —
needs a checker, lint rule or test, not coverage.

| Totals | C | P | G | N/A |
|---|---|---|---|---|
| 74 bugs | 9 | 18 | 25 | 22 |

The pattern is consistent: almost every escaped functional bug lives at the
**intersection of two separately-covered features** — trap cause × mode,
debug × exception, single-step × next instruction, bus error × CHERI check,
split store × forwarding. The model covers the marginals well and the
crosses poorly. The recommendations therefore add crosses, not new
infrastructure.

| Bug | Title | Status | Existing point / proposed addition (§) |
|---|---|---|---|
| 001 | MTVEC/MEPC CSR set/clear corruption | C | csr `x_csr_addr_op` |
| 002 | Store bus error reported as load fault | C | lsu `cp_out_mcause` store_fault bin (tripwire) |
| 003 | WFI not woken by halt request | C | issue `cp_sleep_wake.by_debug` (tripwire; comment stale §1.1) |
| 004 | DRET outside debug mode → CHERI fault | G | §3.1 `x_trap_sysctl_mode` (dret × ~debug_mode) + `x_cause_class` |
| 005 | ECALL writes mtval = PC | G | §3.1 `x_cause_mtval` (tripwire bin ecall × mtval==pc) |
| 006 | Reserved R-type accepted as rev8 | G | §3.7 decoder near-miss bins |
| 007 | Misaligned AMO/SC do not trap | C | lsu `cp_atomic_align_fault_*` |
| 008 | AMO bus error → load access fault | P | §3.4 `x_amo_err_cause` |
| 009 | trvk range check off by one | C | lsu `cp_range_boundary` |
| 010 | MRET without ASR wrong CHERI mtval | G | §3.1 `x_trap_sysctl_mode` (mret × ~ASR) + `x_cause_mtval` |
| 011 | JAL no redirect with predictor off | G | §3.7 if `x_jal_pdt_off` |
| 012 | Interrupts taken in debug mode | G | §3.1 `ill_irq_in_dm` illegal bin + SVA |
| 013 | Fetch error on second word lost | C | if/id fetch_err word bins |
| 014 | Failed SC forwards uncommitted data | G | §3.4 dcache `x_sc_fail_fwd` |
| 015 | Misaligned cap access stale mtval | P | §3.1 `x_cause_mtval` (stimulus only; value needs checker) |
| 016 | Store vs stale MSHWM after csrw | G | §3.4 `cp_mshwm_wr_to_store` |
| 017 | Counter writes allowed without ASR | P | §3.6 `x_csr_asr` |
| 018 | Unimplemented CSR w/o ASR → CHERI fault | P | §3.6 `x_csr_asr` |
| 019 | minstret never increments | G | §3.6 `cp_minstret_inc` (tripwire) |
| 020 | misa bits 31:9 set | N/A | reset-value check / directed test |
| 021 | ebreak in debug mode re-entry | G | §3.1 `x_trap_dm` + §3.2 entry src |
| 022 | Exceptions in debug mode → mtvec | G | §3.1 `x_trap_dm`; §3.6 `ill_mcause_wr_in_dm` |
| 023 | Illegal CSR does not trap in debug mode | G | §3.1 `x_trap_dm` (illegal_insn × debug) |
| 024 | CLC no clrperm in debug mode | P | §3.4 `x_clrperm_dm` |
| 025 | csrw dpc/dscratch dropped at PMODE=1 | P | §3.6 `x_dbg_csr_pmode` |
| 026 | Halt with empty IR saves stale dpc | P | issue `x_cp_irq_valid` exists for IRQ only; §3.2 `x_dbg_ir_valid` |
| 027 | Debug entry overwrites MEPC | G | §3.6 `ill_mcause_wr_in_dm` covers the mcause/mepc side |
| 028 | Stepping a trapping insn runs handler insn | G | §3.1 `x_step_trap` |
| 029 | Interrupts taken while stepping | G | §3.1 `ill_irq_in_step` illegal bin + SVA |
| 030 | Stepped ebreak reports STEP | P | §3.2 split `cp_dbg_entry_src` × `cp_dbg_cause_sel` |
| 031 | Misaligned LR/SC/AMO on RV32 build | C | lsu `cp_atomic_align_fault_*` (needs run on simv32, §4) |
| 032 | Trapping AMO overwrites rd | P | §3.4 `x_amo_err_cause` (value needs checker) |
| 033 | Stale load after 2-word store | P | §3.4 dcache `x_split_store_then_load` |
| 034 | U-mode MRET/WFI not privileged | G | §3.1 `x_trap_sysctl_mode` (sysctl × priv × TW) |
| 035 | ECALL in debug mode → mtvec | G | §3.1 `x_trap_dm` |
| 036 | Trapping AMO saves MPIE = 0 | G | §3.1 `x_trap_mie` (amo × MIE) |
| 037 | Successful SC.W does not update MSHWM | G | §3.4 `cp_sc_ok_mshwm` |
| 038 | M-irq blocked in U-mode with MIE = 0 | G | §3.1 `x_irq_priv_mie` |
| 039 | Odd mepc/dpc after JALR to odd target | P | ex `cp_jalr_target_low` exists; §3.1 `x_trap_after_odd_jalr` |
| 040 | Halt during step reports STEP | P | §3.2 split `cp_dbg_entry_src` |
| 041 | Illegal CSR access mtval = 0 | G | §3.1 `x_cause_mtval` (illegal_insn × mtval==0 tripwire) |
| 042 | mstatush not implemented | G | §3.6 `cp_csr_addr` add mstatush bin (tripwire, Open) |
| 043 | CDBG_CTRL no effect (deferred) | N/A | feature not implemented; directed test when it is |
| 044 | ALT tag fields X with predictor off | N/A | X-propagation / lint |
| 045 | alt_err_event unused | N/A | lint |
| 046 | flush_alt no default | N/A | lint |
| 047 | alt_seq never driven | N/A | lint |
| 048 | conf2 RA predicted-PCC undriven | P | existing RA points, but only if fcov runs on conf2 (§4) |
| 049 | RA predictor reg resets outside range | G | §3.7 `cp_ra_pred_before_x1_wr` |
| 050 | dcache stale after cap/misaligned store | P | §3.4 dcache `x_split_store_then_load` |
| 051 | LR/SC skip load-barrier hazard after CLC | P | §3.5 `cp_consumer_class` fill + cross |
| 052 | Split access 2nd-half error wrong mtval | P | §3.4 `x_split_err_phase` × mtval class |
| 053 | mult set_bounds_comb latches | N/A | lint/synthesis |
| 054 | fetch_fifo64 ALT drops align64 | N/A | ALT feature not enabled in configs; lint/directed |
| 055 | AMO rd = x0 in trace/RVFI | N/A | tracer |
| 056 | tracer CLC/trvk matching after irq | N/A | tracer |
| 057 | amoand.w disassembled INVALID | N/A | tracer |
| 058 | c.ebreak trace line no PC | N/A | tracer |
| 059 | +CAP_ERR_RATE no effect | N/A | testbench |
| 060 | CLC revocation sees younger store | N/A | not a bug |
| 061 | AMO LD-only authority wrong cause | P | §3.4 `x_amo_err_cause` (perm class) |
| 062 | MEPCC loses B/T bits, exp ≥ 24 | N/A | waived (metadata only) |
| 063 | TB memory writes tag on failed SC | N/A | testbench |
| 064–068 | tracer disassembly/format issues | N/A | tracer |
| 069 | vcscomp -trace_dpi dropped | N/A | flow |
| 070 | Fetch error near PCC top → bounds fault | G | §3.3 `x_hdrm_fetch_err` in `cg_ir_decoder` |
| 071 | Step completion reports EBREAK/TRIGGER | G | §3.2 split entry src (step_req × ebreak/trigger) |
| 072 | IRQ withdrawn → mcause machine timer | P | waived; §3.1 `cp_irq_cause_vs_line` (documents the waiver) |
| 073 | Withdrawn debug req → cause 0 | C | issue `cp_dbg_cause_sel.none` (waived, comment §1.1) |
| 074 | RVFI irq record stale pc | C | issue `x_cp_irq_valid` (ir_valid = 0 × handle_irq) |

---

## 3. Recommendations

Ordered by bug yield per line of change. All sketches are illustrative: check
widths and enum names against `super_pkg.sv` / `csr_pkg.sv` when implementing,
and run `check_syntax.py --matrix`, `check_binds.py` and `count_cov.py`.

### 3.1 New covergroup `cg_ma_trap_ctx` in `kudu_fcov_issue.sv` (highest value)

Covers 004, 005, 010, 012, 015, 021, 022, 023, 028, 029, 034, 035, 036, 038,
039, 041 (16 bugs).

One new covergroup sampled once per **trap-or-debug-entry decision** in the
issuer, i.e. on the cycle the issuer drives `csr_save_cause_o`, plus a few
pre-decision qualifiers. Everything it needs is either already a port of
`kudu_fcov_issue` or is a signal of the same name in `issuer.sv`, so `.*`
picks it up with **no bind change**:

New ports (all exist in `issuer.sv` under these names):

```systemverilog
  input priv_lvl_e   priv_mode_i,        // issuer.sv port
  input logic        csr_mstatus_tw_i,   // issuer.sv port
  input logic        debug_step_i,       // issuer.sv port (also fixes §1 if preferred)
  input logic        step_req_q,         // issuer.sv internal
  input logic        ebreak_enter_debug, // issuer.sv internal
  input logic        ir0_mode_err,       // issuer.sv internal
  input logic [17:0] irqs_i,             // issuer.sv port (or the irqs_t struct)
```

Covergroup sketch:

```systemverilog
  typedef enum logic [3:0] {
    TC_IRQ, TC_DBG, TC_ECALL, TC_EBREAK, TC_ILLEGAL, TC_CHERI, TC_FETCH_ERR,
    TC_MODE_ERR, TC_LSU_ERR, TC_OTHER
  } trap_class_e;

  trap_class_e tc;          // computed in the sampling always block
  logic [1:0]  mtval_cls;   // 0: zero, 1: ==pc, 2: ==insn, 3: other

  covergroup cg_ma_trap_ctx with function sample(trap_class_e tc, logic [1:0] mtval_cls);
    option.per_instance = 1;

    cp_tc:     coverpoint tc;
    cp_dm:     coverpoint debug_mode_q;
    cp_priv:   coverpoint priv_mode_i { bins m = {PRIV_LVL_M}; bins u = {PRIV_LVL_U}; }
    cp_mie:    coverpoint csr_mstatus_mie_i;
    cp_tw:     coverpoint csr_mstatus_tw_i;
    cp_step:   coverpoint debug_step_i;
    cp_pmode:  coverpoint cheri_pmode_i;
    cp_mtval:  coverpoint mtval_cls;
    cp_sysctl: coverpoint {ir0_dec.sysctl.mret, ir0_dec.sysctl.dret,
                           ir0_dec.sysctl.wfi,  ir0_dec.sysctl.ecall,
                           ir0_dec.sysctl.ebrk} {
      bins mret = {5'b10000}; bins dret = {5'b01000}; bins wfi = {5'b00100};
      bins ecall = {5'b00010}; bins ebrk = {5'b00001};
    }

    // 004, 021, 022, 023, 035: every synchronous trap class inside and outside debug mode
    x_trap_dm:   cross cp_tc, cp_dm {
      ignore_bins irq_dm = binsof(cp_tc) intersect {TC_IRQ} && binsof(cp_dm) intersect {1};
    }
    // 004, 010, 034: privileged sysctl x priv x TW x debug x ASR/pmode
    x_trap_sysctl_mode: cross cp_sysctl, cp_priv, cp_tw, cp_dm, cp_pmode;
    // 005, 010, 015, 041, 052: what was written to mtval for each trap class
    x_cause_mtval: cross cp_tc, cp_mtval {
      // Tripwires: these stay empty while the corresponding bug is absent.
      // Kept as ignore_bins + a matching SVA rather than illegal_bins until
      // the mtval policy for each class is ruled on.
    }
    // 036, 038: trap / interrupt vs MIE and privilege
    x_trap_mie:      cross cp_tc, cp_mie, cp_priv;
    // 028: a stepped instruction that itself traps
    x_step_trap:     cross cp_tc, cp_step;

    // 012 / 029: structural invariants — must pair with SVA (README §Illegal bins)
    ill_irq_in_dm:   coverpoint (handle_irq & debug_mode_q)  { illegal_bins hit = {1'b1}; }
    ill_irq_in_step: coverpoint (handle_irq & debug_step_i)  { illegal_bins hit = {1'b1}; }
  endgroup
```

Sampling: in the existing `always @(posedge clk_i)` block, when
`csr_save_cause_o`, or when `handle_irq | handle_debug | ir0_trap_event`
(so that 012/029 are seen at the request, not only at commitment). Compute
`tc` from `special_case_q`, `cmt_err_i`, `ir0_dec.errs` and `ir0_dec.sysctl`;
compute `mtval_cls` from `csr_exc_info_o.mtval` against `csr_exc_info_o.pc`
and `ir0_dec.insn`.

Additional single points in the same group:

- `x_irq_priv_mie` (038): `cross handle_irq_raw, cp_priv, cp_mie` sampled when
  `irq_pending_i`, so the "U-mode, MIE = 0, interrupt must be taken" corner is
  a goal.
- `x_trap_after_odd_jalr` (039): register a one-cycle flag from the existing
  ex-side `cp_jalr_target_low` odd condition (expose as a port through the ex
  bind is a bigger change; the cheaper option is `csr_exc_info_o.pc[0]` /
  `ir0_dec.pc[0]` here, and an SVA that mepc[0] is never 1).
- `cp_irq_cause_vs_line` (072, waived): `{irq_pending_i, |irqs_i}` at the
  `CSM_ISSUE_SPECIAL & IRQ` cycle. Bin `withdrawn = {2'b?0}` documents the
  integration requirement (INT-1, [integration_issues.md](integration_issues.md))
  in the coverage report; not a goal.

SVA to add next to the illegal bins:

```systemverilog
  a_no_irq_in_dm:   assert property (@(posedge clk_i) disable iff (!rst_ni)
                                     !(handle_irq && debug_mode_q));
  a_no_irq_in_step: assert property (@(posedge clk_i) disable iff (!rst_ni)
                                     !(handle_irq && debug_step_i));
```

Both already hold by construction (`issuer.sv:736-737`), which is what makes
them legitimate illegal bins.

### 3.2 Split `cp_dbg_entry_src` (issuer) — 026, 030, 040, 071

Replace the 3-bit tuple with the four real entry terms of `handle_debug`
(`issuer.sv:739-740`) and enumerate the pairwise races explicitly. This is a
one-coverpoint edit plus one new port (`ebreak_enter_debug`, via `.*`):

```systemverilog
    cp_dbg_entry_src: coverpoint {step_req_q, ebreak_enter_debug,
                                  (ir_valid_i[0] & ir0_dec.is_brkpt), debug_req_i}
                      iff (event_kind == ISSUE_CYCLE && handle_debug) {
      bins req            = {4'b0001};
      bins trigger        = {4'b0010};
      bins ebreak         = {4'b0100};
      bins step           = {4'b1000};
      bins step_req       = {4'b1001};   // 040
      bins step_trigger   = {4'b1010};   // 071
      bins step_ebreak    = {4'b1100};   // 030, 071
      bins ebreak_req     = {4'b0101};
      bins trigger_req    = {4'b0011};
      bins trigger_ebreak = {4'b0110};
      bins other_multiple = {[0:15]} with ($countones(item) > 2);
    }
    // 030 / 040 / 071: cause selected for each source combination
    x_dbg_src_cause: cross cp_dbg_entry_src, cp_dbg_cause_sel;
    // 026: halt request with and without a valid IR0
    x_dbg_ir_valid:  cross cp_handle_debug, cp_ir_valid;
```

Note that `cp_dbg_cause_sel` is sampled in `CSM_ISSUE_SPECIAL`, one or more
cycles after `handle_debug`. For the cross to be meaningful, latch the entry
source on `handle_debug` and sample the cross with the latched value in the
`ISSUE_SPECIAL & DEBUG` cycle (the same latch pattern already used by
`dbg_req_len`).

### 3.3 `cg_ir_decoder` (kudu_fcov_id.sv) — 070

`cg_ir_decoder` already taps the PCC headroom terms (`hdrm_ge2`, `hdrm_ge4`,
`hdrm_ok`). KUDU-070 needs the combination *headroom 2–3 bytes* × *first-word
fetch error* × *compressed vs. 32-bit*. Add three hierarchical taps in the same
style as the existing ones (`ir_reg_i.errs.fetch_err`, `ir_reg_i.ferr2w`,
`ir_reg_i.is_comp`) and:

```systemverilog
    cp_ferr_word: coverpoint {fetch_err_tap, ferr2w_tap} {
      bins none = {2'b00}; bins first = {2'b10}; bins second = {2'b11};
    }
    x_hdrm_fetch_err: cross cp_hdrm, cp_ferr_word, cp_is_comp iff (cheri_pmode_i) {
      // goal: hdrm 2-3 bytes x first-word fetch error x 32-bit instruction
    }
```

### 3.4 LSU / dcache / complex-unit crosses — 008, 014, 016, 024, 032, 033, 037, 050, 052, 061

All in existing covergroups, using signals already ported:

| Proposal | File / group | Bugs |
|---|---|---|
| `x_amo_err_cause: cross cp_read_err/cp_write_err, cp_out_mcause` (AMO phase × reported cause, incl. CHERI perm class) | lsu `cg_ma_lsu` (cmplx error flags via existing ex taps, or `is_amo` already in lsu) | 008, 032, 061 |
| `x_clrperm_dm: cross x_resp_clrperm, cp_debug_mode` | lsu `cg_ma_lsu` (both points exist) | 024 |
| `x_split_store_then_load`: store class {cap, misaligned/split, word} × next-load-same-line within 0–2 cycles × {forward, bypass, miss} | dcache group (`cp_unaligned`, `cp_byp_good` exist) | 033, 050 |
| `x_sc_fail_fwd`: SC result {fail, ok} × subsequent load forwards from the SC address | dcache group | 014 |
| `cp_mshwm_wr_to_store`: cycles from csrw MSHWM to next store {0,1,2,≥3} | lsu `cg_ma_lsu` (needs one CSR-write strobe port via `.*`) | 016 |
| `cp_sc_ok_mshwm`: successful SC.W × mshwm_update | lsu `cg_ma_lsu` | 037 |
| `x_split_err_phase × mtval class` (first/second half) | lsu, extend existing `x_split_err_phase` | 052 |

### 3.5 CHERI dependence consumer class — 051

`sample_cheri_dep()` (~l.1102) builds an event without `consumer_class`, so
`cp_consumer_class` never sees CHERI_DEP events. Fill it from the same decode
fields used in the ISSUE_OPERAND sampler and add:

```systemverilog
    x_cheri_dep_consumer: cross cp_cheri_temporal_outcome, cp_consumer_class
                          iff (event_kind == ISSUE_CHERI_DEP);
```

LR.W/SC.W/AMO as consumers of a just-loaded capability is then an explicit goal.

### 3.6 CSR group (kudu_fcov_csr.sv) — 017, 018, 019, 022, 025, 027, 042

- `x_csr_asr` (017, 018): `cross cp_csr_addr_class {counter, unimplemented,
  debug, cheri-sensitive, other}, cp_pcc_asr, cp_illegal`. `pcc_asr` is one new
  `.*` port (`cs_registers` already has it for the ASR check).
- `x_dbg_csr_pmode` (025): `cross {dpc, dscratch0, dscratch1} writes,
  cheri_pmode, debug_mode_i`.
- `ill_mcause_wr_in_dm` (022, 027): `coverpoint (csr_save_cause_i &
  debug_mode_i & mcause_en)` as illegal bin + SVA. `cs_registers.sv:763-786`
  guarantees `mcause_en` stays low on an exception in debug mode, so this is a
  true invariant. Add the matching goal `cp_exc_in_dm: (csr_save_cause_i &
  debug_mode_i & ~debug_csr_save_i)` so the scenario itself is required.
- `cp_minstret_inc` (019, Open): bin on `minstret` write-enable from retirement.
  Stays empty while KUDU-019 is open — it is a tripwire, so exclude it from the
  closure target until the fix lands.
- `cp_csr_addr` (042, Open): add an `mstatush` (0x310) bin. Same tripwire
  treatment.
- `cp_step_with_ie`: see §1.1.

### 3.7 Front-end / decoder small additions — 006, 011, 049

- 011: if `cg_ma_if` — `x_jal_pdt_off: cross {is_jal}, pdt_en_i` (pdt_en_i is
  already a port; JAL decode is visible as a hierarchical tap like the existing
  ones).
- 049: issue `cp_ra_update_jalr` already exists; add a bin for "RA prediction
  used before the first write to x1 since reset" (one sticky flag).
- 006: id `cg_ma_id` — near-miss bins for the decoder: funct7/funct3 patterns
  one bit away from each B-extension single-operand encoding (rev8, orc.b,
  zext.h, sext.b/h), crossed with `illegal_insn`. Cheapest form is a small
  `bins[]` list on `ir0_dec.insn` masked to opcode|funct3|funct7|rs2.

---

## 4. Run-configuration recommendations (no code change)

1. Run the fcov build on all four pipeline configurations and on both `simv`
   and `simv32`. KUDU-031 (RV32 build) and KUDU-048 (conf2 only) were invisible
   to a conf1/CHERIoT-only coverage run. `count_cov.py` already supports per-
   config counting.
2. Merge the coverage from `sim/tests_2` (`run_all`) into the regression
   database. The 56 reproducers are by construction the stimulus for the
   crosses above and will fill many of the new bins immediately; holes that
   remain afterwards are the real gaps for the random/DII flow.
3. Keep tripwire bins (§3.6 019/042, §3.1 `x_cause_mtval` corners) out of the
   closure percentage — they are bug detectors, not goals — and list them in
   `sim/fcov/README.md`.

## 5. What coverage cannot do for these bugs

22 of the 74 bugs (tracer, testbench, lint, flow, by-design, waived metadata)
are not stimulus problems. The right controls are:

- **Lint / synthesis checks** (044–047, 053, 054): enable latch and
  undriven/unused warnings as errors in the Verilator lint pass.
- **Tracer self-consistency** (055–058, 064–068): a decoder/tracer equivalence
  check, e.g. disassemble every `cp_*` ISA bin's encoding through both the RTL
  decoder and the tracer, and diff.
- **Testbench sanity** (059, 063): plusarg-effect assertions in the TB.
- **Value checks** (015, 032, 052 partly): coverage guarantees the scenario,
  but only the trace/RVFI diff checks the written value.

## 6. Suggested order of work

1. §1 compile fix plus stale comments (minutes; unblocks everything).
2. §3.1 `cg_ma_trap_ctx` (16 bugs, one new group, no bind edit).
3. §3.2 debug entry split (4 bugs, one coverpoint edit).
4. §3.3 KUDU-070 cross (1 open bug).
5. §3.4–§3.6 crosses in existing groups.
6. §4 run-configuration changes.
7. §3.7 small additions.

---

## 7. Implementation status (2026-11-14)

All of §1, §1.1 and §3 were implemented in `sim/fcov`; §4 is a run-flow
recommendation and is not automated. The README section "Bug-driven coverage"
in [sim/fcov/README.md](../fcov/README.md) lists every new point, the weight-0
tripwires and the new illegal bins with their assertions; section 21 of
[COVERAGE_CHANGES.md](../fcov/COVERAGE_CHANGES.md) records the change.

Totals: 46 coverpoints, 19 crosses and 9 SVAs added, no new covergroup.

| File | Points | Crosses | SVAs |
|---|---:|---:|---:|
| kudu_fcov_issue.sv | 20 | 10 | 3 |
| kudu_fcov_lsu.sv (cg_ma_lsu + cg_ma_dcache) | 12 | 6 | 4 |
| kudu_fcov_csr.sv | 7 | 1 | 1 |
| kudu_fcov_id.sv | 4 | 1 | 1 |
| kudu_fcov_if.sv | 3 | 1 | 0 |

Differences from the proposals:

| Proposal | Implemented as | Bugs |
|---|---|---|
| §1 compile fix | As proposed (explicit renames in the issuer bind, `iff (pdt_en_i)`) | — |
| §3.1 new `cg_ma_trap_ctx` | Points inside `cg_ma_issue`, guarded by `event_kind == ISSUE_CYCLE && csr_save_cause_o`: `cp_tc`, `x_trap_dm`, `x_trap_mie`, `x_step_trap`, `x_cause_mtval` | 004, 005, 015, 021–023, 028, 035, 036, 041 |
| §3.1 `x_trap_sysctl_mode` | `cp_sysctl*`, `x_sysctl_mode`, `x_wfi_tw`, `cp_mret_asr` | 004, 010, 034, 035 |
| §3.1 `ill_irq_in_dm`, `ill_irq_in_step` | `cp_irq_block` illegal bins `in_debug` / `stepping` + `AssertNoIrqInDebug` / `AssertNoIrqWhileStepping` | 012, 029 |
| §3.1 `x_trap_after_odd_jalr` | `cp_trap_pc_odd` illegal bin + `AssertTrapPcEven` | 039 |
| §3.1 `cp_irq_cause_vs_line` | `cp_irq_withdrawn`, weight 0 (KUDU-072 waived) | 072 |
| §3.1 mtval tripwires | `cp_mtval_unexpected`, weight 0 | 005, 010, 041 |
| §3.2 split `cp_dbg_entry_src` | Four-term source with pairwise race bins; `x_dbg_ir_valid`; `cp_dbg_src_q` × `cp_dbg_cause_sel` (`x_dbg_src_cause`, weight 0) | 026, 030, 040, 071 |
| §3.3 `x_hdrm_fetch_err` | As proposed, with `cp_hdrm_win`, `cp_ferr_word`, `cp_ferr_is_comp` | 070 |
| §3.4 `x_amo_err_cause` | `x_amo_bus_err_cause` (illegal `lr_store`, `rmw_load` + `AssertAmoBusErrCause`) and `cp_amo_cheri_cause` | 008, 032, 061 |
| §3.4 `x_split_store_then_load`, `x_sc_fail_fwd` | One dcache cross over the in-flight request class {word store, partial store, load, misaligned, cap, SC} × word relation {same, next, other} × hit: `x_inflight_fwd`, `x_inflight_cap`; forwarding behind misaligned/cap/SC is illegal + `AssertNoFwdBehindRiskyReq` | 014, 033, 050 |
| §3.4 `cp_mshwm_wr_to_store` | In the CSR group (`kudu_fcov_csr.sv`), where the MSHWM write enables live | 016 |
| §3.4 `cp_sc_ok_mshwm` | `cp_mshwm_upd_src` {store, sc, amo_w} in `cg_ma_lsu` | 037 |
| §3.4 `x_split_err_phase` × mtval | `cp_split_bus_err_phase/mtval`, `x_split_err_mtval` + `AssertSplitErrMtval` | 052 |
| §3.6 `x_csr_asr` | In `cg_ma_lsu` (the LSU executes CSR instructions and makes the ASR check): `cp_csr_noasr_cls` × `cp_csr_noasr_out` + `AssertCsrNoAsrOutcome` | 017, 018 |
| §3.6 `ill_mcause_wr_in_dm`, `cp_exc_in_dm` | `cp_dm_trap_m_write` (illegal `written`, also covers mepc) + `AssertNoMTrapCsrWriteInDebug`; `cp_save_kind` {m_trap, dbg_entry, exc_in_dm} | 022, 027 |
| §3.6 `cp_minstret_inc`, mstatush bin | `cp_minstret_inc`, `cp_mstatush`, both weight-0 tripwires | 019, 042 |
| §3.7 `cp_ra_pred_before_x1_wr` | `cp_ra_pdt_fresh` in `cg_ma_if` (weight `PredictRA`) | 049 |
| §3.7 near-miss bins | `cp_b_near_miss0` + `AssertBNearMissIllegal` | 006 |

Verification: pyslang matrix 0 errors in all 8 configurations;
`check_binds.py` 49 connections, 0 unresolved; VCS `-cov -nowave` builds
`simv` and `simv32` without warnings. Smoke tests and all `sim/tests_2`
reproducers (138 runs: 116 PASS, 11 XFAIL, 11 DEFER, 0 FAIL) ran on the
coverage build with no illegal-bin or FCOV assertion hit; the four stub
regressions (`run_lsu_semantics.py`, `run_fcov_accuracy.py`,
`run_frontend_temporal.py`, `run_issue_sampling.py`) pass. `test_checkers` still has 3 failures that predate this change
(`test_actual_discard_count_and_fsm_widths` for KuduCfg1/KuduCfg2 and
`test_rtl_only_errors_fail`).

Open bugs show up as follows: KUDU-019 and KUDU-042 as empty tripwires,
KUDU-071 as `step_ebreak` / `step_trigger` cells reporting EBREAK / TRIGGER in
the weight-0 `x_dbg_src_cause`. For KUDU-070 the `x_hdrm_fetch_err` goal
guarantees the stimulus; the wrong cause is caught by the trace diff.

## 8. Formal verification of the fcov SVAs (2026-11-14)

The SVAs added here were proven with JasperGold through the new
[fv/fv_kudu_fcov.tcl](../../fv/fv_kudu_fcov.tcl) flow (see
[sim/fv/README.md](../fv/README.md)).
It found two RTL bugs, logged in [bug_logs_3.md](bug_logs_3.md) with
directed reproducers in `sim/tests_2`:

| Assertion | Bug | Reproducer |
|---|---|---|
| `AssertTrapPcEven` (§3.1, KUDU-039) | KUDU-075: odd mepc/dpc after an RA-predicted return | `rtl_bug_ra_pred_odd_epc` |
| `AssertCsrNoAsrOutcome` (§3.6) | KUDU-076: stale `bus_err_q` turns a failing CSR access into a bus-error trap | `rtl_bug_csr_stale_bus_err` |
| `AssertTrapPcEven` (after the KUDU-075 fix, 2026-11-15) | KUDU-077: an odd DEPCC address is not legalized in CHERIoT mode | `rtl_bug_depcc_odd` |

KUDU-075 is fixed; the FPV rerun on the fixed RTL no longer finds the
RA-predictor path, but finds KUDU-077 for the same assertion. KUDU-077 is
also fixed, and `AssertTrapPcEven` is now proven (51 of 52 assertions
proven; only `AssertCsrNoAsrOutcome`, KUDU-076, fails). After the
KUDU-076 fix (2026-11-15), all 52 assertions are proven.

It also found three checker bugs, now fixed: `AssertCjalrPredictOneHot`
(`cp_cjalr_predict_ok` now uses `s1_wr_valid`, since the RTL blocks slot 1
behind a slot-0 CJALR) and `AssertExCategory` for ALU pipelines 0/1 (the
category ignores `is_brkpt`, which stays set for trigger matches in debug
mode). The fixed model passes the pyslang matrix (0 errors),
`check_binds.py` (49 connections, 0 unresolved) and a VCS `-cov` build with
isa_test1, cheri_test1 and dbg_test1.
