# CHERIoT-Kudu RTL bug log — review rounds 4–6 (asynchronous-event stress)

This review targeted behaviour under asynchronous events. It used the
testbench's random interrupt, debug-request and bus-error generators
(`+INTR_RATE`, `+DBG_REQ_RATE`, `+INSTR_ERR_RATE`, `+DATA_ERR_RATE`,
`+INSTR_ERR_ADDR`, `+DATA_ERR_ADDR`) together with random wait states. IDs
continue from `bug_logs_2.md` (KUDU-001..069).

- **RTL reviewed:** `c708e3c` ("updated testbench to support random
  interrupt/debug requests"). The RTL and TB md5s are the same in all three
  scratch areas below.
- **History.**
  - Round 4 (2026-11-13) found FE4-1, DBG-A and IRQ-1.
  - Round 5 started the stress campaign. Its host (gem-cl03-fe-328) went down
    mid-run, and its two orphaned farm jobs (526490378, 526490449) were
    stopped.
  - Round 6 (2026-11-14) re-reproduced FE4-1 and DBG-A, then resumed all six
    areas from the round-5 state.
- **References:** CHERIoT Sail
  (`/home/scratch/fortress/kunyanliu/kudu_temp/cheriot_sail_dii_20261013_155851`),
  cheriot-ibex (`sim/run_ibex`), the RISC-V privileged spec 1.12, and the
  RISC-V Debug spec 0.13.2. The self-checking tests compare each stimulus run
  with a clean, stimulus-free run of the same program.
- **Scratch areas:**
  - `$R4` = `/home/scratch/fortress/kunyanliu/kudu_temp/review4_20261113_185621`
    (round 4: `frontend/`, `irq/`, `debug/`, `lsu/`, `fuzz/`).
  - `$R5` = `/home/scratch/fortress/kunyanliu/kudu_temp/review5_20261113_222116`
    (round 5). Its builds `$R5/build_c{1,2,3}/{simv,simv32}` (KuduCfg1/2/3,
    `-nowave`) were reused read-only in round 6. Shadow-TB builds live under
    `$R5/<area>/build_*`.
  - `$R6` = `/home/scratch/fortress/kunyanliu/kudu_temp/review6_20261114_005942`
    (round 6). Each area's raw report is `$R6/<area>/REPORT.md` and its model
    `MODEL.md`, for the areas chaos, cherierr, collide, dbgsuite, lsuirq and
    rtlreview. The coordinator's re-runs are in `$R6/repro/` and
    `$R6/verify/`.
- **FPV of the fcov SVAs (2026-11-14):** KUDU-075 and KUDU-076 were found by
  proving the assertions of the functional coverage model with JasperGold
  (`fv/fv_kudu_fcov.tcl`, see `sim/fcov/README.md`). They are counterexamples
  of `AssertTrapPcEven` and `AssertCsrNoAsrOutcome`; both were confirmed in
  simulation with directed tests in `sim/tests_2`. KUDU-077 is the
  `AssertTrapPcEven` counterexample left after the KUDU-075 fix
  (2026-11-15).

## Summary

| ID | Status | Severity | Area | Location | Summary | Reproducer |
|---|---|---|---|---|---|---|
| KUDU-070 | Fixed | Low (CHERI fault reporting) | Fetch / IR decode | `rtl/ir_decoder.sv:571`, `rtl/fetch_fifo64.sv:286-304`, `rtl/issuer.sv:983-992` | A fetch bus error 2–3 bytes below the PCC top is reported as a PCC bounds fault (mcause 0x1c, MEPCC untagged) instead of an access fault | `$R6/repro/fe4` (`fe4_pcc`, `+INSTR_ERR_ADDR=80001998`) |
| KUDU-071 | Fixed | Low (debugger-visible) | Debug | `rtl/issuer.sv:968-975`, `:729`, `:739-740` | A completed single step reports dcsr.cause EBREAK/TRIGGER instead of STEP when the next instruction is an ebreak or trigger match, including stepping an ecall or other trap into a handler that starts with one | `$R6/repro/dbgA` (`dbgr_rv`/`dbgr_ch`, cases 33/34) |
| KUDU-072 | Waived | Low | Interrupts | `rtl/issuer.sv:835`, `:948-952`, `:1004-1018` | An interrupt whose line withdraws between the decision and the trap is still taken, with mcause = machine timer (even with MTIE=0) | `$R4/irq/M/tests/irq_drop`, `$R6/collide` `col_irqx_pulse` |
| KUDU-073 | Waived | Low–medium | Debug | `rtl/issuer.sv:968-975` | A debug_req that withdraws between the decision and entry still halts the hart, with reserved dcsr.cause = 0 (or STEP if dcsr.step=1) | `$R6/collide/repro_dbgnone` |
| KUDU-074 | Fixed | Low (verification) | Tracer | `rtl/tracer.sv:100-102` | The RVFI `intr=1` record carries a stale pc/insn from IR0 when IR0 is invalid (after mret/dret, redirect, drain); 46 % of interrupt records | `$R6/lsuirq/repro/T1_tracer_intr_pc` |
| KUDU-075 | Fixed | Medium | Branch prediction / traps | `rtl/branch_predict.sv:344-369`, `rtl/branch_unit.sv:90`, `rtl/issuer.sv:876-899` | After a return predicted from an odd ra/cra, an interrupt or debug entry saves an odd mepc/dpc (gap in the KUDU-039 fix) | `sim/tests_2/rtl_bug_ra_pred_odd_epc` |
| KUDU-076 | Fixed | Low | LSU / CSR | `rtl/load_store_unit.sv:379`, `:420`, `:588-613`, `:644` | A first-half bus error of a split access leaves `bus_err_q` set, so the next failing CSR/SCR access traps with that bus-error cause and mtval instead of illegal instruction / CHERI ASR | `sim/tests_2/rtl_bug_csr_stale_bus_err` |
| KUDU-077 | Fixed | Low (debugger-visible) | CSR / debug | `rtl/cs_registers.sv:1659-1661`, `:1741-1743` | In CHERIoT mode a DEPCC write with an odd address keeps bit 0 (not legalized like MEPCC or the RV32 dpc); dret then resumes at the odd address and a trap there saves an odd mepc | `sim/tests_2/rtl_bug_depcc_odd` |

KUDU-072 and KUDU-073 have the same root cause and fix. The issuer latches
`special_case_q` at the WAIT_CMT0 decision, but re-derives the cause from live
inputs one cycle later in CSM_ISSUE_SPECIAL. Both are waived (design owner,
2026-11-14): interrupt lines and debug_req are not expected to withdraw
without acknowledgement. The behaviour is documented as integration
requirements INT-1 and INT-2 in [integration_issues.md](integration_issues.md).

No architectural-state corruption was found under any stimulus in rounds
4–6. No instruction was lost or executed twice, and no register, memory or
capability was corrupted. All three functional bugs from those rounds report
a wrong cause; mepc, dpc and the resume point are correct. The later FPV run
found KUDU-075, which does save an odd mepc/dpc, and KUDU-076, another
wrong-cause bug. After the KUDU-075 fix it found KUDU-077, where an odd
DEPCC written by the debugger survives to dret (since fixed).

---

## KUDU-070: fetch bus error near the PCC top is reported as a PCC bounds fault

- **Status:** Fixed (2026-11-15) in the working tree. Found in round 4
  (`$R4/frontend/REPORT.md`, BUG-FE4-1). Re-reproduced in round 6.
  - `rtl/ir_decoder.sv:571-576`: `hdrm_valid = ~fetch_err | ferr2w`, and
    `hdrm_ok = allow_all || ((~hdrm_valid || is_comp) ? hdrm_ge2 : hdrm_ge4)`.
    When the first parcel errored, its length bits are garbage, so only
    pc+2 <= T is checked (the access fault wins). When only the second parcel
    errored (ferr2w), the instruction length is valid and pc+4 <= T still
    applies (the bounds fault wins), as in Sail.
- **Fix verification** (`/home/scratch/fortress/kunyanliu/kudu_newrtl2_20261115_164135`):
  - `rtl_bug_fetch_err_pcc_top`, extended to 13 runs (first- and
    second-parcel errors, direct entry at T-2, and errored words at or after
    T reached by jal, branch, cjr, cjal and direct entry): all PASS. HEAD
    fails err1/err37; the inverted `hdrm_valid` polarity fails bnd0/bnd37;
    waiving the ge2 check on fetch_err fails bnd32/34/35/36/39.
  - The round-5 Sail-checked fetch sweep (gen_pcc5/chk_pcc5, 738 runs, c1/c2/c3,
    w0-w2, real/garbage error data, irq/debug scheduled around the fault):
    738/738 equal to Sail (the 9 pu_none w2 runs with `--rnddbg`, as in
    round 6).
  - All of `sim/tests_2` on KuduCfg1: 130 PASS, 11 XFAIL, 11 DEFER, 0 FAIL
    (before the test was extended).
  - `run_full_regression.py` on KuduCfg1: 296 PASS, 11 XFAIL, 0 FAIL.
- **Severity:** low. It needs PMODE=1, a bus error on the first fetch word,
  and an instruction 2–3 bytes below the PCC top. The handler then sees a
  non-recoverable CHERI fault: MEPCC is untagged, and an in-bounds
  instruction is reported as a bounds violation.
- **Configs:** c1, c2 and c3, with any wait state. PMODE=1 only.
- **Location:**

  | Location | Role |
  |---|---|
  | `rtl/fetch_fifo64.sv:251-259` | sets `first_word_err` / `fetch_err` |
  | `rtl/fetch_fifo64.sv:286-304` | `out_is_comp` is derived from the errored data |
  | `rtl/ir_decoder.sv:571` | `hdrm_ok = allow_all \|\| (ir_reg_i.is_comp ? hdrm_ge2 : hdrm_ge4)` |
  | `rtl/ir_decoder.sv:575` | `cheri_bound_vio = cheri_pmode & ~debug_mode_i & (~base_ok \| ~hdrm_ok)` |
  | `rtl/issuer.sv:983-992` | trap priority perm > bound > fetch_err |

- **Description:** the IR stage chooses the 2- or 4-byte headroom check from
  `is_comp`, which is decoded from the data of the fetch that returned a bus
  error.
  - If the errored halfword at pc has `[1:0] == 2'b11`, the 4-byte check is
    applied and fails.
  - `bound_vio` then wins over `fetch_err`.
- **Expected (Sail, `riscv_fetch.sail`):** check `pc+2 <= top`, then read the
  first parcel. A bus error there is final: mcause 1 (instruction access
  fault), mtval = pc, MEPCC tag kept. The length, and the `pc+4` check, are
  only used after a successful read of a 32-bit parcel.
- **Exact affected set:** measured by cherierr over 1476 + 96 sims and about
  400 k cases (`$R6/cherierr/REPORT.md`, "FE4-1 characterisation").
  - Headroom `top - pc` must be 2 or 3.
  - The error must be on the fetch word that holds the halfword at pc (W0 or
    both words). An error on the second word only is unaffected, and is
    correctly a bounds fault for a 32-bit instruction at T-2.
  - The errored halfword at pc must satisfy `[1:0] == 3`. With garbage data
    this hits 16-bit instructions too. With all-zero error data it never hits.
  - All 10 entry paths are affected (sequential, BHT/ALT loop, BTB, RA
    prediction, mret), independent of prediction.
- **Observed:** `fe4_pcc` with `+INSTR_ERR_ADDR=80001998`, case `A32@T-2/t2`
  (32-bit addi at 0x80001998, PCC top 0x8000199a):
  `c=0x1c v=0x401 tag=0`. Sail gives `c=1 v=0x80001998 tag=1`. The control run
  `+INSTR_ERR_ADDR=80001a98` (case `Bc@T-2/t2`, 16-bit instruction) gives
  mcause 1 correctly.
- **Reproducer:** run from `$R6/repro/`. `run_all.sh` runs this and KUDU-071 on
  c1/c2/c3.
  ```
  mkdir x && cd x && ln -s $R6/repro/fe4/bin bin
  submit -i $R5/build_c1/simv +TEST=fe4_pcc +PMODE=1 +INSTR_ERR_ADDR=80001998 +TIMEOUT=2000000
  ```
  The test's self-check encodes the HEAD behaviour. Cases 43/44/47/48/51/52
  (`J*@S-2`) always print FAIL, on HEAD and on the fix. This is a test
  artefact: `csetaddr` below base gives an unrepresentable capability, and
  the following cjr takes a tag fault.
- **Fix (validated):** `$R5/cherierr/src_f/rtl/ir_decoder.sv:571`, built as
  `$R5/cherierr/build_f{1,2,3}`:
  ```systemverilog
  assign hdrm_ok = allow_all || ((ir_reg_i.is_comp || (fetch_err && ~ferr2w)) ? hdrm_ge2 : hdrm_ge4);
  ```
  - `ferr2w` means only the second word errored.
  - The whole topic-1 suite (1362 runs plus 96 reruns) matches Sail on the
    fixed build.
  - With the fix, `fe4_pcc` changes in exactly one case per config
    (`A32@T-2/t2` → mcause 1, mtval 0x80001998, tag 1). All other cases are
    identical.

## KUDU-071: single-step completion reports EBREAK/TRIGGER instead of STEP

- **Status:** Fixed (2026-11-15) in the working tree. Found in round 4
  (`$R4/debug/REPORT.md`, BUG A). Re-reproduced in round 6, and extended by
  dbgsuite and collide to step × trap.
  - `rtl/issuer.sv:920-922`: `step_req_q` is set from the current state
    (`ctrl_fsm_cs[CSM_CMT_FLUSH] | ctrl_fsm_cs[CSM_ISSUE_SPECIAL]`) and
    `special_case_q != DEBUG`, so a stepped ebreak, which enters debug
    itself, does not also arm a step request.
  - `rtl/issuer.sv:970-977`: the TRIGGER and EBREAK causes are gated by
    `~step_req_q`, followed by HALTREQ, then STEP (the suggested fix,
    keeping haltreq > step for KUDU-040).
- **Fix verification** (`/home/scratch/fortress/kunyanliu/kudu_newrtl_20261115_163153`
  and `/home/scratch/fortress/kunyanliu/kudu_newrtl2_20261115_164135`):
  - `rtl_bug_step_ebreak_cause`: all 3 runs PASS (cases 33/34 now halt with
    cause STEP first, then EBREAK/TRIGGER on the next resume).
  - No regression of the earlier debug-cause bugs: `rtl_bug_issuer_debug`
    (KUDU-030, including the stepped ebreak) and `rtl_bug_halt_step_cause`
    (KUDU-040) PASS.
  - All of `sim/tests_2` on KuduCfg1: 130 PASS, 11 XFAIL, 11 DEFER, 0 FAIL.
  - `run_full_regression.py` on KuduCfg1: 296 PASS, 11 XFAIL, 0 FAIL.
- **Severity:** low. No architectural state is corrupted, but the debugger is
  given the wrong halt reason.
  - OpenOCD/GDB treat the halt as a breakpoint hit, not a completed step.
  - For an ebreak they typically skip it. The round-4 ROM does exactly that,
    so the step halt is lost.
  - For a trigger they report a hardware breakpoint that has not happened yet.
- **Configs:** all 18. That is c1/c2/c3 × {simv32, simv +PMODE=0,
  simv +PMODE=1} × {w0, 3/3/3/3 wait states}.
- **Location:** `rtl/issuer.sv`:
  - `:729` `ebreak_enter_debug` is not qualified by `step_req_q`.
  - `:739-740` `handle_debug` ORs `step_req_q` with the ebreak and trigger
    terms.
  - `:968-975` cause chain: TRIGGER > EBREAK > HALTREQ > STEP.
- **Description:** after the stepped instruction retires, `step_req_q` forces
  the DEBUG special case. The entry is taken with IR0 holding the *next*
  instruction, which has not been attempted yet. The cause chain evaluates
  that instruction's ebreak (ebreakm=1) or trigger term before the step.
  - The ebreak half is a regression from the KUDU-030 fix (`d290cd0`, "fixed
    single step debugging"). `debug_bugs.md` ("Combined cause-priority fix")
    already warned about it.
  - The trigger half predates `d290cd0`.
- **Step × trap (round 6):** stepping a trapping instruction lands on the
  handler's first instruction. If that is an ebreak/c.ebreak (ebreakm=1) or
  matches an execute trigger, the same wrong cause appears.
  - Trapping instructions tested: ecall, illegal, load/store/fetch bus fault,
    ebreak with ebreakm=0, misaligned, and CHERI faults.
  - dbgsuite cases 110–116 and 120–126, and collide `stepx`, show this.
  - mepc, mcause and dpc are correct, and no instruction is lost or
    duplicated. These are new instances of KUDU-071, not a separate bug.
  - Stepping over ecall, ebreak, illegal, faults, mret, wfi, dret or AMOs is
    otherwise clean.
- **Expected:** Debug spec 0.13.2 §4.4. After a step the hart re-enters
  debug mode with cause 4. A trigger or ebreak "at the new address does not
  fire until the hart actually attempts to execute that instruction". The
  cause priority applies to causes on the *same* instruction. The next resume
  then reports cause 1 or 2 at the same dpc.
- **Observed** (`$R6/repro/dbgA/runs/*/sim.log`): cases 33 and 34 fail on all
  9 coordinator combinations.
  - Case 33 (step `addi`, next is `ebreak`): `dcsr=0x40008047`, cause 1.
  - Case 34 (step `addi`, next matches tdata2): `dcsr=0x40008087`, cause 2.
  - Expected cause 4 in both.
- **Reproducer:**
  ```
  mkdir x && cd x && ln -s $R6/repro/dbgA/bin bin
  submit -i $R5/build_c1/simv +TEST=dbgr_rv +PMODE=0 +DBGROM=dbgrom_rv +TIMEOUT=2000000   # "DBGT DONE fails=2"
  submit -i $R5/build_c1/simv +TEST=dbgr_ch +PMODE=1 +DBGROM=dbgrom_ch +TIMEOUT=2000000
  ```
- **Suggested fix:** make step completion override the next-instruction
  causes, keeping haltreq > step (KUDU-040).
  ```systemverilog
  if (~step_req_q & ir_valid_i[0] & ir0_dec.is_brkpt) debug_cause_o = DBG_CAUSE_TRIGGER;
  else if (~step_req_q & ebreak_enter_debug)          debug_cause_o = DBG_CAUSE_EBREAK;
  else if (debug_req_i)                               debug_cause_o = DBG_CAUSE_HALTREQ;
  else if (debug_step_i)                              debug_cause_o = DBG_CAUSE_STEP;
  ```
  - `step_req_q` is 0 when the stepped instruction itself is an ebreak or
    trigger match, so KUDU-030 is unaffected.
  - Option: collide notes that reporting TRIGGER for step plus
    trigger-on-next is arguably allowed by the priority table. The ebreak
    variant is clearly wrong.

## KUDU-072: interrupt trap with mcause = machine timer when the pending line withdraws

- **Status:** Waived (design owner, 2026-11-14). Interrupt lines are not
  expected to deassert without an acknowledgement; this is documented as
  integration requirement INT-1 in [integration_issues.md](integration_issues.md).
  - Mentioned in `bug_logs.md:1258` as "not a bug", without a reproducer.
  - Re-raised in round 4 (`$R4/irq/REPORT.md`, IRQ-1), because the reported
    mcause names an interrupt that is disabled in mie.
  - Confirmed deterministically in round 6 by collide.
- **Severity:** low. It needs a level interrupt source that deasserts without
  a CPU acknowledgement, within a one-cycle window. The error is silent:
  software dispatches to the timer handler although MTIP=0, and even with
  MTIE=0.
- **Configs:** c1, c2 and c3; simv32 and simv +PMODE=0. PMODE=1 uses the same
  path.
- **Location:** `rtl/issuer.sv`:
  - `:835` `special_case_q <= IRQ` latches the decision at WAIT_CMT0.
  - `:1004-1018`: CSM_ISSUE_SPECIAL recomputes mcause from the live `irqs_i`.
    The final `else` gives `EXC_CAUSE_IRQ_TIMER_M` unconditionally.
  - `:948-952` `mfip_id` is also live.
- **Expected:** Priv §3.1.9 and §3.1.15. The trap must either not be taken,
  as in ibex, which re-checks in IRQ_TAKEN, or report the line that was
  decided on. Sail selects the cause from `mip & mie` at the trap.
- **Observed:**
  - Round 4 (`$R4/irq/runs/drop_s1_32`): `mie = 0x00010000` (fast0 only), the
    handler reads `mcause = 0x80000007` and `mip = 0`. Bad traps: c1 80/154,
    c2 90/175, c3 73/149.
  - Round 6 (`$R6/collide/runs/irqx_pulse_*`): 438–610 bad traps per run,
    6/6 configs, on every line (external, software, all fast lines). All are
    mcause 0x80000007 with `irqs_i == 0`.
- **Reproducer:** the stock TB cannot hit the window, because a line only
  drops after an ack store, which commits before the decision. Shadow TBs are
  therefore used.
  - Round 4: `+INTR_SELFCLR=N` in `$R4/irq/src/sim/tb/data_mem_model.sv`
    deasserts the line randomly, and the IRQMON monitor flags the bad traps.
    ```
    cd $R4/irq && BUILD=$R4/irq/build_s1 NOCHK=1 tools/run1.sh drop_s1_32 1 simv32 irq_drop +INTR_RATE=7 +INTR_SELFCLR=2 +TIMEOUT=2000000
    ```
  - Round 6: collide's deterministic event scheduler (`0x8380_0160`) pulses
    one line for 1–4 cycles. Test `col_irqx_pulse`, run with
    `$R5/collide/build_c{1,2,3}/simv32` and bin `$R6/collide/bin`.
- **Suggested fix:** latch the cause together with `special_case_q <= IRQ`.
  This is a priority encoder of `irqs_i` at WAIT_CMT0 exit, held in a
  register. Alternatively, abort to DECODE in ISSUE_SPECIAL when no line is
  still pending. The first option is simpler, and also fixes KUDU-073.

## KUDU-073: a withdrawn debug request still enters debug mode, with dcsr.cause = 0

- **Status:** Waived (design owner, 2026-11-14). debug_req is not expected
  to withdraw before the hart halts; this is documented as integration
  requirement INT-2 in [integration_issues.md](integration_issues.md). New in round 6 (collide). It was also visible in the
  round-5 `dbg_pulse` runs, but was not analysed before the crash. It is not
  in `bug_logs.md`, `bug_logs_2.md`, `debug_bugs.md` or the round-4 reports.
- **Severity:** low–medium.
  - A DM that clears `dmcontrol.haltreq` in the 2-cycle window after the core
    decided to halt gets a spurious halt.
  - The cause it reports is reserved: Debug 0.13.2 §4.8.1 allows only 1–5.
  - With `dcsr.step=1`, the halt is reported as STEP instead of HALTREQ.
- **Configs:** c1, c2 and c3 × {simv32 w0, simv +PMODE=0 w2}. All 6 tested
  combinations are affected.
- **Location:** `rtl/issuer.sv:968-975`. `special_case_q = DEBUG` is latched
  at the WAIT_CMT0 decision, then the cause is derived from live inputs in
  ISSUE_SPECIAL. With `debug_req_i` gone and nothing else true, the chain
  leaves `debug_cause_o` at 0, yet debug mode is still entered.
- **Observed** (`$R6/verify/dbgnone_c{1,2,3}/sim.log`, coordinator re-run):
  - A 1-cycle pulse is ignored, which is acceptable.
  - A 2-cycle pulse enters debug mode with cause 0 at all 12 delays (12/12).
    For example: `COLMON> 414 DBG pc=80001044 cause=0 req=0 step=0`, then
    `COLMON-ERR> 414 DBGNONE: debug entry with dcsr.cause=0`.
  - A pulse of 3 cycles or more gives cause 3 correctly (24/24).
  - The results are identical on c1/c2/c3.
  - Random stress (`dbg_pulse`) gives 750–850 DBGNONE entries per run on every
    config, and collide's random mix hit it in 16 of 60 runs.
- **Reproducer** (shadow TB with scheduler and COLMON, `$R5/collide/src`):
  ```
  mkdir x && cd x && ln -s $R6/collide/bin bin
  submit -i $R5/collide/build_c1/simv32 +TEST=dbgnone +DBGROM=col_rom +TIMEOUT=200000
  ```
  Source: `$R6/collide/repro_dbgnone/dbgnone.S` and `README.md`.
- **Suggested fix:** the same as KUDU-072. Latch the debug cause at the
  decision, or re-check in ISSUE_SPECIAL and fall back to NULL if the request
  has gone.

## KUDU-074: RVFI interrupt record reports a stale pc/insn

- **Status:** Fixed (2026-11-14) in the working tree after `c708e3c`:
  `rtl/tracer.sv:100` now sets
  `pc_rdata = ir_valid_i[0] ? ir0_dec.pc : ir0_nxt_pc_q`, the same mux the
  issuer uses for mepc. New in round 6 (lsuirq, T1). It is not in earlier
  logs: `bug_logs_2.md` assumes the record "carries the ir_dec of the
  instruction it displaced".
- **Resolution:** only pc_rdata of an `intr=1` record is meaningful. Its
  insn, pc_wdata and mem masks are don't-care, so they are still taken from
  ir0_dec and may be stale. `sim/tests_2/rtl_bug_rvfi_intr_stale_pc` checks
  pc_rdata only and passes (err: 205 interrupt records, noerr: 174, no
  stale pc; before the fix 108 and 63 were stale).
- **Severity:** low, verification only. The architecture is correct:
  `issuer.sv:1006` saves `mepc = ir_valid_i[0] ? ir0_dec.pc : ir0_nxt_pc_q`,
  and every handler mret returns to the right pc. Any RVFI consumer
  (`rvfi_gdiff.py`, DII flows, RVFI checkers) sees a wrong "displaced
  instruction".
- **Location:** `rtl/tracer.sv:100-102`. `pc_rdata = ISSUER_PATH.ir0_dec.pc`
  and the insn/mem masks also come from ir0_dec, even when IR0 is not valid.
- **Observed:** the record is stale when IR0 is invalid.
  - After an mret or dret, the record shows the fall-through pc, e.g.
    0x84000068 in the debug ROM.
  - After a redirect or drain, it shows an already-retired instruction, or a
    debug-ROM instruction from an earlier debug visit.
  - Example: `rvfi_kudu_core.log` pkt 1169 `sw @80001666` retires; pkt 1171
    `intr=1 pc=80001666 insn=00e52823 wmask=0f`; the handler mret returns to
    0x8000166e.
  - Campaign rate: 190,578 of 414,868 interrupt records (46 %) are stale, in
    2423 of 3159 runs, on every cfg and mode.
  - Coordinator re-run (`$R6/verify/T1`): 59 of 138 records mismatch, with
    the same pkt 1171 example.
- **Reproducer:**
  ```
  mkdir x && cd x && ln -s $R6/lsuirq/M/run/bin bin
  submit -i $(cat $R6/lsuirq/repro/T1_tracer_intr_pc/cmd)
  python3 $R6/lsuirq/repro/T1_tracer_intr_pc/intrpc3.py .
  ```
- **Suggested fix:** in the intr record use the core's mux,
  `pc_rdata = ir_valid_i[0] ? ir0_dec.pc : ir0_nxt_pc_q` (or
  `csr_exc_info_o.pc`), and zero insn and the mem masks.

## KUDU-075: odd mepc/dpc after a return predicted from an odd ra

- **Status:** Fixed (2026-11-15) in the working tree:
  `rtl/branch_predict.sv:344`, `:350`, `:360` and `:369` now predict
  `{cur_ra32_i[31:1], 1'b0}`. Found by FPV of `AssertTrapPcEven`
  (`sim/fcov/kudu_fcov_issue.sv:1514`, 13-cycle counterexample) and
  confirmed in simulation. It is a gap in the KUDU-039 fix (`546cc56`,
  `bug_logs_2.md`), which made the computed jalr target even but not the
  RA-predicted one.
- **Fix verification** (`/home/scratch/fortress/kunyanliu/kudu075_fix_20261115_011928`):
  - `rtl_bug_ra_pred_odd_epc`: all 6 runs PASS on KuduCfg1, and on KuduCfg3
    with `rtl_bug_jalr_odd_epc` and `rtl_bug_jal_pdt_off`.
  - All of `sim/tests_2` on KuduCfg1: 122 PASS, 15 XFAIL, 11 DEFER, 0 FAIL.
  - `run_full_regression.py` on KuduCfg1 (mini, riscv and bug suites): 286
    PASS, 15 XFAIL. Its 2 FAILs were `isa_test2a` timeouts caused by a stale
    `sim/run/bin/isa_test2a.vhx` that predates the `intr_mask` testbench
    change (`c708e3c`); the pre-fix build hangs the same way, and the
    rebuilt image passes on KuduCfg1 and KuduCfg3.
  - FPV: the original counterexamples (odd ra/cra through the predictor)
    are gone. `AssertTrapPcEven` still fails, through a different path,
    logged as KUDU-077.
- **Performance note:** the fix keeps the comparisons in
  `ir_stage.sv:441-444` (`cjalr_predict_ok`) and `branch_unit.sv:90` against
  the raw ra, so every return through an odd ra/cra is now a mispredict
  (the computed, even target is correct). Comparing with bit 0 masked would
  recover the prediction.
- **Severity:** medium. mepc/dpc must be even (IALIGN = 16), but an
  interrupt or debug entry can save an odd pc. In RV32 mode, mret/dret
  then returns to the even address, which is correct only by accident. In
  CHERIoT mode the saved MEPCC/DEPCC address is odd, and the handler sees an
  illegal value. Any handler that inspects or advances mepc (e.g. emulation,
  context switch) is affected. It needs software that returns through an ra
  with bit 0 set. This is legal (jalr ignores bit 0), and CHERIoT sentries
  use odd addresses for compressed code.
- **Configs:** every config with `PredictRA = 1` (KuduCfg1, KuduCfg1x,
  KuduCfg3); not KuduCfg2. All modes: simv32, simv with PMODE=0, and simv
  with PMODE=1.
- **Location:**

  | Location | Role |
  |---|---|
  | `rtl/branch_predict.sv:344-369` | for a return through ra (`dec_jalr_ra`), `predict_target` / `ptarget` = `cur_ra32_i`, bit 0 not cleared |
  | `rtl/ir_stage.sv:198-208`, `:442-444` | `update_cjalr_instr` sets `ptarget = cur_ra` when `cjalr_predict_ok` (CHERIoT) |
  | `rtl/branch_unit.sv:65-72` | `compute_jalr_target` clears bit 0, but only for the computed target |
  | `rtl/branch_unit.sv:90` | `get_mispredict_cause` compares `ptarget` with the raw rs1, so the odd prediction is accepted and no mispredict is raised |
  | `rtl/issuer.sv:876-899` | `resolve_nxt_pc` / `ir0_nxt_pc_q` latch the odd predicted target |
  | `rtl/issuer.sv:~966`, `:~1006`, `rtl/cs_registers.sv:1676`, `:1746` | an IRQ or debug entry with IR0 empty saves `ir0_nxt_pc_q` into mepc/dpc unchanged |

- **Description:** a `ret` (or `c.jr ra`, `jalr x0, 0(ra)`, `cret`) whose
  ra is odd is predicted to the odd ra. Fetch uses the even address, so the
  program runs correctly. But the issuer's next-pc register holds the odd
  value until the next instruction reaches IR0. An interrupt or debug
  request taken in that window, with IR0 empty, saves the odd value.
- **Expected:** mepc/dpc = target & ~1 (the address of the instruction that
  would have executed next).
- **Observed:**
  - FPV: cra = 0x8001b705 (tagged), cret predicted from it, debug_req at
    cycles 10–11, dpc = 0x8001b705.
  - Simulation (`rtl_bug_ra_pred_odd_epc`, default build, 4000 iterations
    of `ret` through ra = target + 1, all wait states 0–3):

    | Run | Entries | Odd mepc/dpc | First odd |
    |---|---|---|---|
    | rv32_irq (simv32) | 902 irq | 114 | 0x80000679 |
    | rv32_dbg (simv32) | 1067 debug | 120 | 0x80000679 |
    | pmode0_irq (simv, PMODE=0) | 902 irq | 114 | 0x80000679 |
    | pmode0_dbg (simv, PMODE=0) | 1067 debug | 120 | 0x80000679 |
    | cheri_irq (simv, PMODE=1) | 903 irq | 87 (MEPCC) | 0x800005f1 |
    | cheri_dbg (simv, PMODE=1) | 1089 debug | 105 (DEPCC) | 0x800005f1 |

    All six runs reported XFAIL (KUDU-075 Open, before the fix) in
    `/home/scratch/fortress/kunyanliu/tests2_new3_20261114_222728`.
- **Reproducer:** `sim/tests_2/rtl_bug_ra_pred_odd_epc` (see
  `direct_tests.md`):
  ```
  cd sim/tests_2
  ./common/run_all.py --tests rtl_bug_ra_pred_odd_epc --work /home/scratch/fortress/kunyanliu/<dir>
  ```
  The earlier KUDU-039 test (`rtl_bug_ra_pred_conf2`) runs only KuduCfg2,
  where PredictRA = 0, so it could not see this path.
- **Suggested fix:** clear bit 0 of the RA prediction in
  `branch_predict.sv` (`predict_target` / `ptarget` from `{cur_ra32_i[31:1],
  1'b0}`) and of `cur_ra` in `ir_stage.sv:update_cjalr_instr`. The branch
  unit then needs to compare `ptarget` with `rs1 & ~1` (as
  `compute_jalr_target` does), or every odd-ra return becomes a mispredict.
  Alternatively, clear bit 0 when `ir0_nxt_pc_q` is loaded.

## KUDU-076: a stale bus error turns a failing CSR access into a bus-error trap

- **Status:** Fixed (2026-11-15) in the working tree:
  `rtl/load_store_unit.sv:376` clears `bus_err_d` when `csr_go` starts a CSR
  access (the suggested fix). Found by FPV of `AssertCsrNoAsrOutcome`
  (`sim/fcov/kudu_fcov_lsu.sv:808`, 16-cycle counterexample: an SCR access
  after a load bus error trapped with mcause 7) and confirmed in simulation.
- **Fix verification** (`/home/scratch/fortress/kunyanliu/kudu076_fix_20261115_165952`):
  - `rtl_bug_csr_stale_bus_err`: all 4 runs PASS.
  - All of `sim/tests_2` on KuduCfg1: 144 PASS, 7 XFAIL, 11 DEFER, 0 FAIL.
  - `run_full_regression.py` on KuduCfg1: 310 PASS, 7 XFAIL, 0 FAIL.
  - FPV (`fv/fv_kudu_fcov.tcl`, 300 s per property): 52 asserts, all 52
    proven, including `AssertCsrNoAsrOutcome`.
- **Severity:** low. The trap is taken and mepc is correct, but mcause and
  mtval are wrong. It needs a split (misaligned) load/store whose first half
  takes a bus error, followed by a failing CSR/SCR access before any other
  load or store. A handler that dispatches on mcause sees an access fault at
  the old data address instead of an illegal instruction (mcause 2) or a
  CHERI ASR violation (0x1c), so CSR emulation breaks.
- **Configs:** all configs and modes (simv32, PMODE=0, PMODE=1).
- **Location:**

  | Location | Role |
  |---|---|
  | `rtl/load_store_unit.sv:420` | `bus_err_d = data_err_i \| pmp_err_q` in WAIT_RVALID_MIS (first half of a split access) |
  | `rtl/load_store_unit.sv:379` | the only clear: in IDLE when a new non-CSR request starts; `csr_go` does not clear it |
  | `rtl/load_store_unit.sv:644` | `data_or_pmp_err` includes `bus_err_q` |
  | `rtl/load_store_unit.sv:588-613` | `lsu_err_mcause` tests `data_or_pmp_err` before `csr_err` |

- **Description:** after the split access traps, `bus_err_q` stays set. The
  next LSU operation is the CSR access. `lsu_resp_err` is still correct
  (`csr_go_q ? csr_err : ...`), so only a failing CSR access is affected,
  but its cause is taken from the stale bus error, with mtval =
  `addr_last_q`.
- **Expected:** mcause 2 and mtval = instruction bits (or 0x1c and the CHERI
  ASR mtval in PMODE=1).
- **Observed** (`rtl_bug_csr_stale_bus_err`, all 4 runs identical):

  | Case | First trap (mcause, mtval) | Second trap | Result |
  |---|---|---|---|
  | C0 illegal csrr 0x5c0 only | — | 2, 0x5c0022f3 | PASS |
  | C1 misaligned lw at 0x7ffffffd, then csrr | 5, 0x7ffffffd | **7, 0x7ffffffd** | FAIL |
  | C2 misaligned sw, then csrr | 7, 0x7ffffffd | **7, 0x7ffffffd** | FAIL |
  | C3 misaligned lw, then csrw mvendorid | 5, 0x7ffffffd | **7, 0x7ffffffd** | FAIL |
  | C4 misaligned lw, a good lw, then csrr | 5, 0x7ffffffd | 2, 0x5c0022f3 | PASS |

  The second trap's cause is always 7 (store access fault), whatever the
  first access was. All four runs report XFAIL (KUDU-076 Open) in
  `/home/scratch/fortress/kunyanliu/tests2_new3_20261114_222728`.
- **Reproducer:** `sim/tests_2/rtl_bug_csr_stale_bus_err`:
  ```
  cd sim/tests_2
  ./common/run_all.py --tests rtl_bug_csr_stale_bus_err --work /home/scratch/fortress/kunyanliu/<dir>
  ```
- **Suggested fix:** clear `bus_err_d` when `csr_go` starts a CSR access
  (`load_store_unit.sv:379`), or gate the bus-error term of `lsu_err_mcause`
  with `~csr_go_q`.

## KUDU-077: an odd DEPCC address is not legalized in CHERIoT mode

- **Status:** Fixed (2026-11-15) in the working tree:
  `rtl/cs_registers.sv:1661` now passes
  `rv32_mepc_wr | rv32_depc_wr | cheri_mepcc_wr | cheri_depcc_wr` as is_mepcc
  to `legalize_scr` (the suggested fix). Found by FPV of `AssertTrapPcEven`
  after the KUDU-075 fix (16-cycle counterexample) and confirmed in
  simulation.
- **Fix verification** (`/home/scratch/fortress/kunyanliu/kudu077_fix_20261115_044716`):
  - `rtl_bug_depcc_odd`: all 4 runs PASS on KuduCfg1; the cheri runs read
    back 0x80000256 / 0x80000250 with the tag cleared.
  - All of `sim/tests_2` on KuduCfg1: 126 PASS, 15 XFAIL, 11 DEFER, 0 FAIL.
  - `run_full_regression.py` on KuduCfg1 (mini, riscv and bug suites): 292
    PASS, 15 XFAIL, 0 FAIL.
  - FPV (`fv/fv_kudu_fcov.tcl`, 300 s per property): 52 asserts, 51 proven,
    1 CEX. `AssertTrapPcEven` is now proven; the only CEX is
    `AssertCsrNoAsrOutcome` (KUDU-076, open).
- **Severity:** low, debugger-visible. It needs the debugger (debug ROM or
  program buffer) to write DEPCC with an odd address. dret then resumes
  with the odd address in PCC, and a trap taken there saves an odd MEPCC,
  the same illegal state as KUDU-075.
- **Configs:** all configs; simv with PMODE=1 only. The RV32 dpc path
  (simv32, PMODE=0) is legalized.
- **Location:**

  | Location | Role |
  |---|---|
  | `rtl/cs_registers.sv:1652` | `cheri_depcc_wr` = cspecialw to SCR 24 in debug mode |
  | `rtl/cs_registers.sv:1659-1661` | `legalize_scr(is_mtcc, is_mepcc, ...)` gets `rv32_mepc_wr \| rv32_depc_wr \| cheri_mepcc_wr`, without `cheri_depcc_wr` |
  | `rtl/cheri_pkg.sv` `legalize_scr` | for is_mepcc, clears address bit 0 and the tag of an odd, sealed or non-executable value; otherwise passes the value through |
  | `rtl/cs_registers.sv:1741-1743` | `depc_d = scr_wdata_legalized` on `cheri_depcc_wr` |

- **Description:** every other xEPC write (MEPCC, RV32 mepc, RV32 dpc) is
  legalized as an EPCC: bit 0 is cleared and an odd, sealed or
  non-executable value loses its tag. A CHERIoT DEPCC write is stored as
  written. cheriot-ibex has the same behaviour
  (`ibexc_local/rtl/ibex_cs_registers.sv:1066` stores `cheri_csr_wdata_i`
  unmasked, while its RV32 dpc path at `:623` clears bit 0), so the golden
  trace diff does not flag it; the Sail model has no debug mode.
- **Expected:** DEPCC read back with bit 0 clear, as for MEPCC.
- **Observed:**
  - FPV: debug entry at cycle 4, `cspecialw` DEPCC with address 0xffffffff
    at cycle 9, dret; the fetch at 0xffffffff traps and saves mepc =
    0xffffffff (`csr_exc_info_o.pc[0] = 1`).
  - Simulation (`rtl_bug_depcc_odd`, KuduCfg1, random debug requests):

    | Run | Written | Read back | Result |
    |---|---|---|---|
    | cheri_default (simv, PMODE=1) | 0x80000257 | 0x80000257 (tag 1) | FAIL |
    | cheri_waits (simv, PMODE=1, wait states) | 0x80000251 | 0x80000251 (tag 1) | FAIL |
    | rv32 (simv32) | 0x8000017b | 0x8000017a | PASS |
    | pmode0 (simv, PMODE=0) | 0x8000017b | 0x8000017a | PASS |

    With the suggested fix applied to a scratch copy of the RTL, all 4 runs
    pass; the cheri runs read back 0x80000256 / 0x80000250 with the tag
    cleared, as for an odd MEPCC write
    (`/home/scratch/fortress/kunyanliu/kudu075_fix_20261115_011928/k077_fix`).
- **Reproducer:** `sim/tests_2/rtl_bug_depcc_odd`:
  ```
  cd sim/tests_2
  ./common/run_all.py --tests rtl_bug_depcc_odd --work /home/scratch/fortress/kunyanliu/<dir>
  ```
- **Suggested fix:** add `cheri_depcc_wr` to the is_mepcc argument at
  `rtl/cs_registers.sv:1661`:
  `(rv32_mepc_wr | rv32_depc_wr | cheri_mepcc_wr | cheri_depcc_wr)`.

---

## Code-review notes and observations (no architectural effect observed)

- **O-1 (cherierr), MSHWM on a bus-errored CSC.** MSHWM is not lowered when
  a store or CSC below it takes a bus error.
  - Sail lowers it in `ext_check_phys_mem_write`
    (`cheri_addr_checks.sail:233-241`), before the write.
  - Nothing is written, so this is safe. The spec does not define
    bus-errored stores. It is noted for the spec owners.
- **S2 (rtlreview), branch prediction on errored fetch data.**
  `rtl/branch_predict.sv:188-195` does not gate `is_jal` / `is_jalr_ra` with
  the fetch error. A garbage jal can cause a wrong-path prefetch, which is
  flushed by the trap. **Not a bug**: the designer classifies prediction on
  errored fetch data as a don't care (2026-11-15).
- **Misspelt declarations (rtlreview).** `rtl/cs_registers.sv:1641-1642`
  declare `cheri_mpecc_wr` / `rv32_decc_wr`, but `:1650-1651` use
  `cheri_mepcc_wr` / `rv32_depc_wr`, which become implicit nets. It is
  functionally fine, but should be fixed. `` `default_nettype none `` would
  catch it.

## FV counterexamples (not numbered)

These came from the JasperGold run of the merged SVA review checkers
(`sim/fcov`, KuduCfg1, `fv/fv_kudu_fcov.tcl`, 300 s per property), snapshot
`/home/scratch/fortress/kunyanliu/fvall_20261115_171802` (`p{0,1}_<area>/res.log`).
None is an open bug, and none has a KUDU number.

- **Resolved, not a bug: front end, `AssertNoPredictOnFetchErr`**.
  - 4-cycle CEX at both pmode 0 and pmode 1 (`p0_front`, `p1_front`).
  - `rtl/branch_predict.sv:188-195` masks `is_branch` with `errs.fetch_err`,
    but not `is_jal` or `is_jalr_ra`, so garbage data from an errored fetch
    can be predicted taken (code-review note S2).
  - The designer classifies this as a don't care: the fetch-error trap
    flushes the wrong path. The assertion was removed from
    `sim/fcov/kudu_fcov_if.sv`.
- **Waived, integration item: LSU, `AssertEarlyLoadSplitInRegion`**
  (`sim/fcov/kudu_fcov_lsu.sv`).
  - 7-cycle CEX at both pmode 0 and pmode 1 (`p0_lsu`, `p1_lsu`).
  - The early-load region is decoded from the base address only, so the
    second beat of a split load can leave the region while still issued
    as an early load.
  - Waived by the design owner (2026-11-15). See integration requirement
    INT-3 in [integration_issues.md](integration_issues.md). The assertion is kept and listed in
    `fcov_expected_cex` (`fv/fv_kudu_fcov.tcl`), so FV reports it as an
    expected CEX.
- **Not an RTL issue, `AssertSvaMultDiv`** (`sim/fcov/kudu_fcov_ex.sv:1746`).
  - 44-cycle CEX at pmode 0 only.
  - Cause: JasperGold automatically black-boxes the 32-bit `/` and `%`
    operators of the assertion's reference model (WNL032/WNL033/WNL064), so
    the expected value is unconstrained. In the waveform the RTL result is
    correct (DIV 0/1 = 0).
  - Proposed fix: elaborate with `-bbox_div` / `-bbox_mod`. This is under
    trial in `/home/scratch/fortress/kunyanliu/multdiv_cex_20261115_180613`
    (`cex.vcd`, `div0.log`, `div1.log`).

## TB / test issues found

| Item | Description |
|---|---|
| R4 T1 | The instruction-fetch side of `data_mem_model.sv:672` aliases DRAM at 128 KB |
| R4 T2 | On an instruction bus error the TB returns real memory data. Garbage data is needed to expose KUDU-070 on 16-bit instructions (cherierr added `+FE_ERR_DATA` / `+FE_ERR_RAND` in its shadow TB) |
| Stock TB | Interrupt lines only drop after an ack store, and debug_req has no pulse mode, so KUDU-072/073 (waived) cannot be reached. Consider merging collide's deterministic scheduler (`0x8380_0160`) and COLMON, or `+INTR_SELFCLR` |
| dbgsuite T1 | Debug-ROM MMIO stores lowered `mshwm`, failing `isa_test_csr`. Fixed in the scratch ROM by save/restore |
| chaos G6/G7 | Fuzzer generator bugs: untagged mepcc in the CHERI irq handler, and `e_mdchain` clobbering ra. Fixed in the scratch `tfz.py` |
| Timeouts | All timeouts were starvation or slowness under maximum stimulus. One example is INTR 2–3 with DBG_REQ 5–7 and no throttle: every mret is followed immediately by the next interrupt. All were confirmed by same-seed re-runs or with a longer timeout. No hang was found |

## Round 6 coverage of the campaign

| Area | Focus | Sims | Result |
|---|---|---|---|
| dbgsuite | random debug requests over the whole corpus (riscv-tests, mini, coremark, csr), plus a directed step/trigger suite including step × trap | 6056 | KUDU-071 instances only |
| lsuirq | fetch/LSU in-flight transactions under maximum interrupt, debug and bus-error rates with asymmetric wait states | 6106 | 0 RTL failures; KUDU-074 |
| cherierr | CHERIoT under bus error, interrupt and debug: fetch near bounds, CLC/CSC, MSHWM, sentries, ID/IE regions, cap fuzz | 2650 | KUDU-070 characterised and fix validated; O-1 |
| chaos | all-stimulus transparency fuzz (signature equal to the clean run), with ibex/Sail references | 2383 + 163 ref | clean |
| collide | deterministic trap/interrupt/debug collision scheduler, plus step × trap | ~224 | KUDU-073 new; KUDU-072, KUDU-071 confirmed |
| rtlreview | line-by-line asynchronous-event review of `rtl/*.sv`, plus targeted stress | 59 | no new bug; S2 and implicit-net notes |
| coordinator | re-runs of KUDU-070/071/073/074 | 22 | all reproduced |

The total is about 17,500 simulations over c1/c2/c3 × {simv32, simv +PMODE=0,
simv +PMODE=1} × wait-state profiles.

## Areas checked clean (with evidence in `$R6/<area>/REPORT.md`)

- **Interrupt transparency:** all 18 lines at the maximum rate, across
  loads/stores/AMOs/LR/SC/CLC/CSC in flight, misaligned split accesses,
  mult/div, branches and jumps, fence.i, wfi and mret. Signatures matched the
  clean runs (chaos, lsuirq).
- **Bus errors:** instruction and data errors at random rates and fixed
  addresses gave the correct mcause/mtval/mepc, retry and resume. This held
  for split misaligned accesses, store→load forwarding, TSRAM/bitmap stores
  and AMOs, apart from KUDU-070 (lsuirq, cherierr).
- **Debug requests:** haltreq on any instruction, including during traps,
  interrupt entry, mret and wfi; nested with interrupts; ROM transparency
  over the full regression corpus; haltreq > step (KUDU-040). Apart from
  KUDU-071 and KUDU-073 (dbgsuite, collide), everything was clean.
- **Single step:** stepping over ecall, ebreak (ebreakm=0/1), c.ebreak,
  illegal, bus faults, misaligned, fetch fault, CHERI faults, mret, wfi, dret
  and AMOs executes exactly one instruction. The only wrong cause is the
  KUDU-071 next-instruction case (dbgsuite, collide).
- **CHERIoT under stimulus:** interrupts and debug requests next to cjalr to
  ID/IE/inheriting sentries (exact MIE window), ecall from ID/IE regions,
  auipcc, csetbounds, mtdc/mtcc and cjal. CLC/CSC/CSW/CSB with errors and
  misaligned CLC/CSC were also clean (cherierr).
- **Front end under errors:** all branch-prediction and ALT paths around
  errored fetches flush correctly. S2 is a prefetch only (rtlreview).
