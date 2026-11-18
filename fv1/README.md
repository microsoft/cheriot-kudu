# Formal verification of cheriot-kudu

All Kudu formal work is formal property verification (FPV) with Cadence
JasperGold 2024.03. The scripts, file lists and FV-only SystemVerilog are in
**fv/**. This document describes the flows; the per-bug results are in
**sim/testplan/bug_logs_3.md** and **sim/testplan/fcov_bug_crosscheck.md**.

| Flow | Script | Properties | File list |
|---|---|---|---|
| Design-assertion groups | **fv/fv_kudu.tcl** | **fv/module_fv_ext.sv**, one **KUDU_FORMAL_G*** group per run | **fv/kudu.jp.f** |
| Coverage-model SVAs | **fv/fv_kudu_fcov.tcl** | every SVA of the functional coverage model (**sim/fcov**), plus its FV helper lemmas | **fv/kudu_fcov.jp.f** |
| Block level | **fv/fv_*_fifo.tcl**, **fv/fv_lsu_if.tcl** | the **FORMAL**-guarded properties inside single RTL modules | inline **analyze** |

The two top-level flows prove on **kudu_top** with **KuduCfg1** and
**CHERIoTEn = 1** only. Cfg1x/2/3, the DesignWare multiplier and
CHERIoTEn = 0 hardware have never been checked formally. Neither flow is the
end-to-end Sail equivalence proof described at the end of this document.

## Running JasperGold

JasperGold needs a licence, which is only reachable from the LSF farm, so
every run goes through **submit -i**. Interactive (GUI), from **fv/**:

```
cd fv
./run_jg                  # submit -ig jg -fpv -allow_unsupported_OS
source fv_kudu.tcl        # or fv_kudu_fcov.tcl
```

Batch, with the project directory on the scratch disk so that
**fv/jgproject** is not touched:

```
cd fv
submit -i -m 32 -t <minutes> /home/cad/tools/cadence/jasper/jasper_2024.03/bin/jg \
    -batch -fpv -allow_unsupported_OS -proj <scratch>/jgproj <scratch>/w.tcl > <scratch>/jg.out 2>&1
```

**w.tcl** sources one of the scripts, calls a run procedure and ends with
**exit**. The scripts use paths relative to **fv/** (**../rtl**, **../sim**),
so always launch from there. The clean coverage-model run takes several hours
per pmode; run pmode 0 and 1 as two concurrent jobs.

## How the helper lemmas work

Many properties are true but not inductive: a k-induction or IC3 engine
finds unreachable start states that break them and never converges. A
**helper lemma** is an extra assert that states an invariant about such
internal state, for example that a counter equals the number of valid FIFO
entries. Each helper is small enough to prove on its own. Once proven it is
converted into an assumption (**assume -from_assert -remove_original**),
which removes those unreachable states for every later proof. Chains of
helpers let the hard targets close in seconds instead of staying
undetermined for hours.

The soundness rules both flows follow:

- A property is assumed only after it was proven **in the same session**.
  Nothing is assumed from an earlier run, so a stale or circular lemma cannot
  hide a bug.
- A CEX is never assumed.
- **prove -all** does not reliably reuse properties proven earlier in the same
  call, so the flows prove one property at a time, in dependency order.
- Assumptions are global: an **assume** in any bound module constrains every
  property of the design. Environment assumptions therefore live in their own
  files or ifdef groups, never next to coverage or design assertions.

## Flow 1: design-assertion groups (fv_kudu.tcl)

**fv/module_fv_ext.sv** binds one **<module>_fv_ext** extension into each
major RTL module (issuer, committer, prefetch_buffer64, ls_pipeline,
mult_pipeline, alu_pipeline, dcache, kudu_top). Its asserts are split into
groups, each enabled by a define, so every group is a separate, small proof
session:

| Define | Module | Scope |
|---|---|---|
| **KUDU_FORMAL_G0_0** | kudu_top_fv_ext | register-file read data at the IR stage (AltEnable forced to 0) |
| **KUDU_FORMAL_G0_1** | kudu_top_fv_ext | top-level bus assumptions only (AltEnable forced to 0) |
| **KUDU_FORMAL_G0_Long** | kudu_top_fv_ext + fv_long_help_* | forwarding, PCC and complex-unit targets that need helper lemmas |
| **KUDU_FORMAL_G1_0** | issuer_fv_ext | issue validity and dequeue |
| **KUDU_FORMAL_G1_1** | issuer_fv_ext | interrupt issue |
| **KUDU_FORMAL_G2** | committer_fv_ext | commit cases and dequeue |
| **KUDU_FORMAL_G3** | prefetch_fv_ext | fetched instruction PCs and data |
| **KUDU_FORMAL_G4_0** | ls_pipeline_fv_ext | LSU request/response sequencing |
| **KUDU_FORMAL_G4_1** | ls_pipeline_fv_ext | trap-pending behaviour (AssertTrapPendingAll is split into provable parts) |
| **KUDU_FORMAL_G5** | mult_pipeline_fv_ext | progress, sequencing and forwarding |
| **KUDU_FORMAL_G6** | alu_pipeline_fv_ext | forwarding and capability tags |
| **KUDU_FORMAL_G7** | dcache_fv_ext | update legality |

Procedures:

- **run_fv <defines>** analyzes **kudu.jp.f** with the given defines and runs
  **prove -all**.
- **run_fv_long** runs G0_Long. It proves the helper lemmas of the
  **fv_long_help_cmplx**, **fv_long_help_fwdact** and **fv_long_help_pcc**
  modules (end of **module_fv_ext.sv**) one by one in the listed dependency
  order, assumes each proven one, then runs **prove -all** on the targets.
  All 68 helpers and the 5 targets prove in about 6 minutes.
- **run_all** runs G0_0, G1_0 to G7 and G0_Long in sequence into
  **jp_out.log**.

Environment: **kudu.jp.f** defines **CHERIoT**, **SYNTHESIS** and
**KUDU_FORMAL_RTL**. Each group adds its own assumptions. Some assumptions
are outside any group and therefore apply to every group:

- **ls_pipeline_fv_ext**: **AssumeDataGnt0/1** and **AssumeDataValid** (data
  grant in the request cycle or the next, response the cycle after the grant).
- **kudu_top_fv_ext**: **AssumeKTopCfgCheriMode** (**cheri_pmode_i = 1**) and
  **AssumeKTopCfgBootAddr** (0x8000_0000).

## Flow 2: coverage-model SVAs (fv_kudu_fcov.tcl)

JasperGold reads the fcov files unchanged and proves their SVAs (the
illegal-bin companions and the standalone invariants in the kudu_sva_*
modules) on **kudu_top**, KuduCfg1, CHERIoT enabled, with the configuration's
ALT fetch logic (no AltEnable override). Covergroups are skipped (VERI-9060).

| File | Purpose |
|---|---|
| **fv/fv_kudu_fcov.tcl** | **fcov_setup**, **run_fcov_clean**, **run_fcov**, **run_fcov_all**, **fcov_cex_vcd**, and the expected-CEX list **fcov_expected_cex**, which maps open or waived bugs to their assertions |
| **fv/kudu_fcov.jp.f** | RTL without **SYNTHESIS** (the binds use simulation-only RTL signals), tracer, **module_fv_ext_fcov.sv** (empty; used instead of **module_fv_ext.sv**), **fv_fcov_env.sv**, then the fcov files with **kudu_fcov_bind.sv** last. **kudu_fcov_isa.sv** is left out (no SVAs; it binds into the RVFI tracer) |
| **fv/fv_fcov_env.sv** | the only environment assumptions (below) |
| **fv/fcov_order_p0.txt**, **fv/fcov_order_p1.txt** | proof order for **run_fcov_clean** |

### Environment (fv_fcov_env.sv)

- Boot address 0x8000_0000.
- Bus protocol: grant only with a request; instruction grant within 4 cycles
  and data grant within 2 cycles of the request (counting the request cycle);
  exactly one response, the cycle after the grant.
- Bus errors only with rvalid.
- Interrupt lines and debug_req held until taken (the KUDU-072/073 integration
  requirement), unless **FCOV_FV_FREE_REQ** is defined.
- **AssumeFcovPmode**, added by **fcov_setup**: **cheri_pmode_i** equals the
  pmode argument (1 CHERIoT, 0 RV32 compatibility). Run both pmodes.

**fcov_setup** elaborates with **-bbox_a 4096 -bbox_mul 256** by default, so
JasperGold does not black-box the multiplier partial-product array and the
SVA reference multiply operators; black-boxed, they give spurious CEXs on the
multiplier data checks. **run_fcov_clean** also passes **-bbox_div 64
-bbox_mod 64** for the divider checks.

### FV helper lemmas (KUDU_FV_HELPERS)

Most fcov asserts prove directly. The rest, mostly scoreboard, forwarding,
reservation, PC and CSR-capability invariants, only prove with helper
lemmas. The helpers are part of the coverage model, but are compiled only
with **+define+KUDU_FV_HELPERS**, which only **run_fcov_clean** sets:
simulation never sees them. Each fcov file ends with its helper module,
after the coverage and assertion modules; the binds are in a
**KUDU_FV_HELPERS** block at the end of **kudu_fcov_bind.sv**.

| Module (instance) | File | Supports |
|---|---|---|
| **kudu_fvh_csr** (u_fvh_csr) | kudu_fcov_csr.sv | MEPCC/DEPCC/PCC tag legality, special-case CSR state |
| **kudu_fvh_front_pc** (u_fvh_front_pc) | kudu_fcov_if.sv | IF/IR stage PC chain and the IR stage-0 FIFO contents |
| **kudu_fvh_issue_fwd** (u_fvh_issue_fwd) | kudu_fcov_issue.sv | operand forwarding, complex-unit and AMO sequencing |
| **kudu_fvh_wrsv** (u_fvh_wrsv) | kudu_fcov_issue.sv | register-write and load-filter reservations against in-flight writers |
| **kudu_fvh_issue_ctrl** (u_fvh_issue_ctrl, in issuer) | kudu_fcov_issue.sv | issuer FSM, special cases, trap/return targets, debug step, interrupts |
| **kudu_fvh_ex_lsu** (u_fvh_ex_lsu) | kudu_fcov_ex.sv | branch-prediction target, mult scoreboard, LSU fault/alignment/tag checks |
| **kudu_fvh_backend** (u_fvh_backend) | kudu_fcov_cmt.sv | program order between scoreboard entries and the EX pipelines |
| AssertHelpWt* (in kudu_sva_wt_fifo) | kudu_fcov_top.sv | wt_fifo against its reference model; inside kudu_sva_wt_fifo because they need its own **u_ref** |

Helpers bound in **kudu_top** reach the design and other fcov instances with
hierarchical references (for example
**kudu_top.mult_pipeline_i.u_fcov_sva_mult.sb_q**). A rename of a referenced
RTL signal or fcov instance breaks elaboration of the helper flow only, so
run **check_syntax.py --matrix --fv-helpers** (see **sim/fcov/README.md**)
after such changes. The helper modules and their binds are also guarded by
**CHERIoT** and **KUDU_FCOV_OFF**, like the binds they depend on; they were
only proven with CHERIoTEn = 1.

### Procedures

- **run_fcov_clean** {log pmode short long order maxpass}: the full clean run.
  All fcov asserts and all helpers are proved in one session, with nothing
  assumed except **fv_fcov_env.sv** and the pmode. Properties are proved one
  at a time in the order of **fcov_order_p<pmode>.txt** (names relative to
  kudu_top; properties missing from the file go last). Each proven property is
  assumed for the rest of the session. Passes over the undecided ones repeat
  with the **short** limit (2 m) while they make progress, then once with the
  **long** limit (15 m). The log (default **jp_fcov_clean_p<pmode>.log**) is
  written as the run progresses: one **RES** line per attempt (pass, status,
  trace length, seconds, name), then **FINAL_CEX**/**FINAL_OPEN** lines and a
  summary ending in **FCOV FV PASS** when every CEX is listed in
  **fcov_expected_cex**.
- **run_fcov** {Vdef limit pattern pmode}: proves the matching fcov asserts
  with **prove -property** and a per-property time limit, without helpers.
  Quick checks of one instance; hard asserts stay undetermined.
- **run_fcov_all** {log limit pmode}: **run_fcov** on every fcov assert.
- **fcov_cex_vcd** {property file}: saves a CEX trace as VCD.

Batch wrapper for one pmode:

```
source ./fv_kudu_fcov.tcl
run_fcov_clean <scratch>/fcov_clean_p1.log 1
exit
```

The order file is the order in which properties were proven by the last
complete clean run. Regenerate it from a new run log after adding asserts
or helpers (proven properties in **RES** order). A new property that needs
a helper has to come after it; an unordered property is still proved, only
later.

### Adding or changing a helper

1. Add the assert to the **kudu_fvh_*** module of the area, or a new
   **kudu_fvh_<area>** module at the end of the relevant fcov file, with its
   bind in the **KUDU_FV_HELPERS** block of **kudu_fcov_bind.sv**.
2. A helper must be an invariant of the design under **fv_fcov_env.sv** only.
   Never add an **assume** to a helper module.
3. Prove it with **run_fcov_clean**.
4. Update the order file.

### Results history

The first run (2026-11-14) found two RTL bugs, KUDU-075 (**AssertTrapPcEven**,
odd mepc/dpc after an RA-predicted return) and KUDU-076
(**AssertCsrNoAsrOutcome**, stale bus error on a failing CSR access), and
three checker bugs, fixed in the model:

- **AssertCjalrPredictOneHot** (**kudu_fcov_id.sv**) used **s0_rd_valid**; the
  RTL blocks slot 1 behind a slot-0 CJALR through **s1_wr_valid**, which the
  checker now uses.
- **AssertExCategory** for ALU pipelines 0/1 (**kudu_fcov_ex.sv**): in debug
  mode a trigger match leaves **is_brkpt** set but the instruction executes
  normally, so the category is computed with **is_brkpt** cleared.

With the fixed model all 52 assertions of that time were decided in about
10 minutes: 50 proven and 2 expected CEXs. After the KUDU-075 fix
(2026-11-15), **AssertTrapPcEven** still failed through a different path,
KUDU-077 (an odd DEPCC written in debug mode, not legalized in CHERIoT mode).
After the KUDU-077 and KUDU-076 fixes all 52 assertions were proven.

The SVA set has since grown to about 690 asserts per pmode, plus the helper
lemmas. The current expected CEX is **AssertEarlyLoadSplitInRegion**
(waived, INT-3, **sim/testplan/integration_issues.md**).

## Block-level flows

**fv/fv_ir_dual_fifo.tcl**, **fv_sbd_dual_fifo.tcl**, **fv_stage_fifo.tcl** and
**fv_wt_fifo.tcl** prove the **FORMAL**-guarded properties inside
**dual_fifo.sv**, **stage_fifo.sv** and **wt_fifo.sv** in the configurations
used by the IR stage and the scoreboard, with an 8-bit data width to keep the
runs short. **fv_lsu_if.tcl** elaborates **-top lus_if**, which does not
match the **lsu_if** module, and **lsu_if.sv** has no FORMAL properties; it is
not a working flow.

## Limits of the current evidence

- Only KuduCfg1 with CHERIoTEn = 1 is proven (both pmodes for the fcov flow,
  pmode 1 only for **fv_kudu.tcl**).
- The bus assumptions bound the grant latency and fix the response timing;
  longer stalls are covered only by simulation.
- An undetermined property is not a proof. Check each run summary for
  **FINAL_OPEN** lines.
- Proven asserts are safety properties; there is no liveness proof.

## End-to-end formal verification (planned)

Use the CHERIoT-Ibex formal flow as the reference for a Kudu end-to-end FV
environment. The objective is architectural trace equivalence between Sail and
RTL, allowing RTL implementation cycles with no architectural event.

The public [CHERIoT-Ibex formal documentation][ibex-formal] describes
**psgen**-generated proof SystemVerilog, a Sail-to-SystemVerilog translation,
and JasperGold. It explicitly labels the flow work in progress, with no
current liveness proof. Its documented restrictions include **ResetAll = 1**,
disabled clock gating, and exclusions for stack zeroing and
reservation/revocation. These are limitations to review when planning Kudu
work, not assumptions that may silently be transferred to a Kudu sign-off.

**Development status supplied for this plan:** this end-to-end FV work is
currently under development by **SCI Semiconductors**. Kudu adoption, proof
scope and completion must be tracked explicitly; this document does not claim
that an end-to-end Kudu proof already exists. The SCI development assignment
is project-provided status; the public upstream documentation independently
supports the work-in-progress assessment, not that assignment or a completion
claim.

For Kudu, the proof plan must define:

| Obligation | Kudu-specific concern |
|---|---|
| Initial-state correspondence | Reset, integer/capability registers, PCC, CSRs, memory and tags |
| Architectural step correspondence | Correctly order both issue/retirement slots and variable-latency results; distinguish stuttering from missing or duplicated events |
| Instruction semantics | Enabled RV32 and CHERIoT operations, compressed aliases, capability bounds, permissions and sealing |
| Memory correspondence | Loads/stores, tags, LR/SC, AMO multi-step implementation, revocation and memory errors |
| Control-flow correspondence | Branch/JAL/CJALR, prediction recovery, faults, traps, debug and interrupts within the supported model |
| Precise side effects | Killed instructions must not update architectural state; exceptions must identify the correct instruction |
| Progress | State environmental fairness assumptions and distinguish safety proofs from liveness/progress proofs |
| Configuration coverage | Record exactly which parameter sets, ISA features and modes each proof covers |

The formal harness must constrain only legitimate environmental behavior.
Audit reset assumptions, memory abstractions, black boxes, cut points and
unreachable-state claims. Check assertion activation and cover witnesses to
avoid vacuous proofs. A bounded result, timeout or unproven partition is not
an unbounded equivalence proof. The FPV flows above are complementary
assertion evidence, not Sail-to-Kudu trace equivalence.

[ibex-formal]: https://github.com/microsoft/cheriot-ibex/blob/main/dv/formal/README.md
