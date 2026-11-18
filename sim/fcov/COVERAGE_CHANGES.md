# Functional coverage changes

## Scope and outcome

Implemented the source-backed coverage corrections and added instruction-context
crosses, with code and documentation changes confined to `sim/fcov`. Existing
dirty edits were retained. No RTL, test programs, existing coverage databases,
or existing simulation results were changed. No commit was created.

The model now tracks logical IR-slot instruction categories, valid ALU0/ALU1
and MULT stages, WAW-tracked LSU entries, and active complex AMOs. These
residents are crossed with instructions issuing on the current edge and with
selected special-case events. The implementation deliberately distinguishes
pipeline residency from the live decode inputs and from architectural retirement.

Following feedback, instruction-context shadow FIFOs were replaced by direct
hierarchical observations and minimal missing category metadata. Section 1
describes the simplified implementation; section 6 distinguishes its validation
from the original FIFO-based implementation.

Not every proposed expansion was implemented. The final section identifies
work deferred because it requires additional transaction provenance, an
architectural decision, or a broader reachability audit.

The subsequent hierarchical submodule expansion is documented in section 8.
The configuration-bin warning cleanup is documented in section 9.
The subsequent full-model vector-width audit is documented in section 10.

## 1. Instruction-context tracking and crosses

New file: `kudu_fcov_context.sv`.

### Instances and residency

| Instance | Resident definition | Tracking |
|---|---|---|
| `FC_MA_CONTEXT.ir0` | Valid older logical IR instruction | Issuer's age-ordered `ir0_dec` |
| `FC_MA_CONTEXT.ir1` | Valid younger logical IR instruction | Issuer's age-ordered `ir1_dec` |
| `FC_MA_CONTEXT.alu0` | Valid registered EX2/WB contents | Category-only tags, RTL stage enables/valids |
| `FC_MA_CONTEXT.alu1` | Valid registered EX2/WB contents | Category-only tags, RTL stage enables/valids |
| `FC_MA_CONTEXT.mult` | Valid EX2/WB contents | Saved RTL instruction, CHERI operation and CJALR flag |
| `FC_MA_CONTEXT.lsu` | Normal WAW FIFO entries plus active complex AMO | RTL-indexed category tags; complex-unit saved instruction/FSM |

The wrapper uses direct hierarchy, rather than additional observation ports
or independently maintained pipeline FIFOs. ALU stages do not save the opcode,
so only its category is retained in `kudu_fcov_alu`, synchronized with actual
EX2/WB register enables. No coverage-owned stage-valid state is needed.
Bypassed ALU EX2 is excluded because it is the current issue, not an older
instruction. MULT needs no category storage.

The existing LSU WAW FIFO already tracks normal accepted instructions through
result release, including request buffering, memory wait and pending writeback.
Its six-bit records store reservation eligibility and destination register,
not the opcode. A category-tag array uses the FIFO's `wr_data_en` and
`wr_mem_addr`; sampling uses its `rd_mem_addr` and `cur_rd_depth`. No duplicate
FIFO pointers/counts or push/pop model remain. A startup assertion checks
depth agreement and the expected non-write-through configuration. Clearing
the WAW reservation bit does not invalidate a resident category.

Complex AMOs do not enter that FIFO. Their saved instruction and active
complex-unit FSM supply one context over the read/write sequence, including
the transition between halves, rather than separately tracking each accepted
half. LR/SC still use normal WAW entries. This changes AMO observation counts,
not the category or cross definitions.

All resident sampling precedes the current edge's stage/FIFO updates and flush.
This is important when an older instruction leaves while a newer one enters:
the cross describes the older resident versus the new issue, not a self-cross
of the newly accepted instruction.

Reset and flush use RTL validity/occupancy; stale tags are ignored. The former
context queue overflow/underflow and PC-matching machinery was removed.
Unexpected routed categories remain explicit fatal monitor errors. The bus
timing queues are unchanged: unlike instruction context, response latency
requires matching accepted requests to later responses.

### Cross definitions

`x_resident_issued` crosses:

1. Resident instruction's reduced category.
2. Currently issued instruction's reduced category.
3. Issued logical slot.

Both actual issue strobes are observed independently. IR0 crosses issue1 only;
IR1 crosses issue0 only. This avoids redundant diagonal self-crosses. A bad
younger IR instruction can still be observed while the older instruction
issues; a bad older instruction cannot coexist with issue1. The bin filters
preserve this asymmetry.

`x_resident_special` crosses:

1. Resident instruction's reduced category.
2. Selected special case: EXEC fault, SYSCTL, CMPLX, IRQ or DEBUG.
3. Event phase:
   - Drain: DECODE transitions to WAIT_CMT0.
   - Execute: the controller is in ISSUE_SPECIAL.
   - Flush: the controller enters CMT_FLUSH, explicitly classified as EXEC.

Drain-entry samples capture older execution context before the issuer waits
for it to finish. Execute-phase samples are IR-only: older execution
instructions have already drained. Flush samples use the pre-flush residents.
Raw `handle_*` requests are not misrepresented as selected special cases.

The full 19-category taxonomy remains visible in ordinary coverpoints. Crosses
use the existing eight-class reduced taxonomy to limit Cartesian growth.
Routing and feature filters exclude reviewed inapplicable categories. Empty
slots and idle pipelines do not become pseudo-instructions.

Counts are per resident instruction/event pairing, not cycle counts. Two
residents in the same category can each contribute a sample. Internal
`issue_samples` and `special_samples` counters support directed accounting tests.

## 2. ISA classification and encoding coverage

Files: `kudu_fcov_isa.sv`, `kudu_fcov_pkg.sv`.

- Made compressed encoding sets disjoint, including C.NOP/C.ADDI,
  C.ADDI16SP/C.LUI, C.JR/C.MV and C.EBREAK/C.JALR/C.ADD.
- Excluded reserved encodings and HINT forms from the named instruction sets,
  except the explicitly covered canonical C.NOP.
- Qualified mode-dependent aliases with decode metadata saved in the same
  tracer FIFO entry. AUIPC/AUIPCC and compressed integer/capability aliases
  no longer depend solely on the build width. No live retirement-time pmode
  input or new ISA bind port was introduced.
- Corrected the fast-interrupt cause range to `6'h30` through `6'h3e`.
- Corrected ANDN, ORN and XNOR classification to `IC_BITMANIP`.
- Classified CSCRRW before generic CSR handling. The RTL sets `is_csr` for
  CSCRRW, so the previous precedence hid `IC_SCR`.
- Stopped using `ir_dec.is_cheri` as an ISA-family test. In this RTL it is a
  capability-dependency marker asserted for ordinary JAL/JALR/LOAD/STORE too.
  Classification instead uses actual CHERI operation bits.
- Retained the pre-existing shared `tracer_pkg::instr_trace_t` integration
  and added a width assertion. The old README/private-mirror description was
  obsolete; the shared type was not newly moved out of RTL by this task.

The saved-metadata qualification intentionally trusts the decoder for
mode-dependent interpretation. It is not an independent decoder-conformance
oracle.

## 3. Bus timing, response attribution and LSU coverage

Files: `kudu_fcov_bus_timing.sv` (new), `kudu_fcov_bus.sv`,
`kudu_fcov_lsu.sv`.

### Queued timing monitor

Replaced the single-pending-bit response monitors with a shared, in-order
timestamp/metadata queue, instantiated separately for instruction and data
buses. It handles:

- Multiple accepted outstanding requests.
- Simultaneous grant and response, including a full queue with a simultaneous pop.
- A response in the same cycle as its own acceptance when the queue is empty.
- Grant waiting, including cancellation of an unaccepted request.
- Reset of outstanding monitor state.

Acceptance is `req && gnt`. A grant while idle does not create a transaction.
The former assertions forbidding every idle grant were removed rather than
promoting the testbench's grant-generation policy into a core invariant.

Delay means **extra wait**: the next-cycle response has delay zero. A same-edge
response also has delay zero and is distinguished by a separate coverpoint.
Timestamps/delays are 64-bit. Orphan responses, queue overflow, timestamp
overflow and grant-wait overflow terminate explicitly instead of wrapping or
silently dropping coverage. The default safety bound is 64 outstanding requests.

### Response and access coverage

- Data-bus scalar and timing measurements now have one owner, BUS, rather than
  duplicate LSU/BUS goals.
- Queued request metadata associates SC responses and capability-load tags
  with the original accepted request, not a later live LSU decode.
- SC bins now label zero as success and one as failure; fault responses do
  not receive successful/failed-SC credit.
- LSU alignment uses original effective request addresses, including access
  size and capability alignment, rather than already-aligned external addresses.
- Bus alignment bins reflect the RTL's word/eight-byte alignment. Relevant
  configuration parameters are passed through the bind.
- Split-access byte-enable combinations are explicit scoring bins.
- Duplicate revocation enable/outstanding observations were consolidated.
- Fatal-error coverage now observes quiet, raised, sticky and reset-recovery
  behavior instead of asserting the obsolete assumption that the output is
  undriven. This group is instantiated only for CHERIoT-enabled hardware.

## 4. Commit, execution and front-end corrections

### Commit

File: `kudu_fcov_cmt.sv`.

- Captured the faulting slot mask at the same event that captures the error
  information, rather than sampling a newer combinational mask under an old
  latched error.
- Qualified reservation-clear observations with effective register write enables.
- Replaced meaningful default combination bins with explicit scoring values.
- Removed the impossible slot-1-only availability target.
- Restricted concurrent write-count coverage to the two-write maximum implied
  by the two retire slots, despite the existence of three physical write ports.
- Removed constant error-info fields from normal coverage goals.

### Execution

File: `kudu_fcov_ex.sv`.

- ALU/MULT output errors are invariant violations, not normal coverage goals.
  Matching assertions remain in place.
- Removed MULT error-type/mcause targets whose sampling guard is tied false.
- Excluded unsupported MULT signed mode `2'b10`.
- Sampled latched MULT/DIV flags with EX2 validity, not the unrelated current
  input-valid strobe.
- Added explicit accepted-input category bins for the MULT pipeline.
- Disabled scoring of bypassed ALU EX2-only observations and excluded
  SingleStage-inapplicable forwarding bins. Removed constant two-cycle and
  ALU/MULT capability-output targets.
- Corrected the complex-unit coverage FSM to the actual four states:
  IDLE=0, AMO_WAIT_RD=1, AMO_WRITE=2, AMO_WAIT_WR=3. The previous model
  included a removed AMO_READ state and consequently mislabeled later states.

### IF, ID and ISSUE

Files: `kudu_fcov_if.sv`, `kudu_fcov_id.sv`, `kudu_fcov_issue.sv`.

- Removed the duplicate IF predictor-initialization coverpoint.
- Bounded IF occupancy by configured FIFO depth; applied alternate-path and
  instruction-buffer applicability controls.
- Removed the undriven ID `fifo_mema_is0` tap and disabled scoring for reviewed
  bypassed/undriven observations.
- Wired IF `AltEnable`/`InstrBufEn` and ID
  `StageBypass`/`CHERIoTEn`/`PredictRA` parameters into the binds.
- Made forwarding-source and simultaneous special/debug-source combinations
  explicit scoring bins instead of default bins.
- Qualified the stored special-case coverpoint by ISSUE_SPECIAL so stale
  controller values do not count as executed special cases.

## 5. Integration, documentation and checkers

- `kudu_fcov.f`: added the timing helper and context modules in dependency order.
- `kudu_fcov_bind.sv`: added context wiring, parameter forwarding, and corrected
  obsolete implicit-net, tracer-type and automatic-port-audit comments.
  Same-name signals continue to use `.*`.
- `README.md`: documents current groups, event semantics, configuration,
  corrected tracer integration, checker usage and database compatibility.
- `check_syntax.py`: consumes the real filelist, checks all four configurations
  with both CHERIoT build settings, supports coverage-off checks, and fails on
  total elaboration errors rather than only diagnostics originating in fcov.
- `check_binds.py`: handles nested explicit connections and clearly reports
  its source-root-check limitation. It does not replace full elaboration.
- `count_cov.py`: separates source types/new declarations, coverpoints,
  automatic-bin coverpoints, crosses, and regular/illegal/ignore declarations.
  It does not claim these are expanded simulator bins or instances.
- Added `test_checkers.py`, `check_isa_encoding_sets.py`,
  `check_flow_bus_timing.py`, `tb_flow_bus_timing.sv`, and `tb_fcov_context.sv`.

Before the submodule expansion: 15 covergroup types, 426 coverpoint declarations and two
cross declarations. The context type is instantiated six times, giving twelve
context-cross instances. Bin declaration counts are not comparable to the old
regex counter's advertised "bin total".

## 6. Validation and observed context coverage

### Simplified hierarchical implementation

Fresh outputs are under
`sim/fcov_validation_20260912_VhF3M4/simplified_final_Jac8eA/` and
`sim/fcov_validation_20260912_VhF3M4/simplified_context_JmcuuM/`.

- All eight coverage-on configurations elaborate with zero errors; pyslang
  reports expected upward-hierarchy warnings, explicitly permitted by the
  checker. All other coverage diagnostics and all elaboration errors still
  fail. All eight coverage-off configurations also elaborate.
- The simplified bind has 57 explicit connections with zero unresolved roots.
  All nine checker regressions pass, including valid hierarchical observations
  and rejection of a misspelled hierarchical signal.
- Native VCS compilation resolves the direct hierarchy and bound ALU tags.
- Rewritten directed tests cover valid-stage gating, simultaneous EX2/WB
  contexts, IR counterpart-only crosses, a bad younger IR slot, drain/flush
  events, stale-tag exclusion after validity clears, and reset.
- Native `isa_test1`, `cheri_test1`, and RV32-mode `rv32ua-p-amoadd_w`
  complete at 15,172, 1,384, and 183 cycles respectively; the AMO test reports
  `RISCV Test passed`. Seed/delays match the original runs.
- The simplified coverage-on ISA instruction trace is byte-identical to the
  retained coverage-off reference.

### Original FIFO-based implementation (historical evidence)

The checks and measured cross counts below describe the initial implementation,
not a rerun of every check or a coverage-total claim for the simplified model.

All licensed commands used `submit -i`. Outputs are isolated under:

`sim/fcov_validation_20260912_VhF3M4/`

No existing database was merged, replaced or deleted. Newly generated helper
test artifacts and the temporary pyslang installation were moved out of the
fcov source directory into this validation directory without discarding them.

| Check | Result |
|---|---|
| Pyslang, KuduCfg1/1x/2/3, CHERIoT on/off | All eight elaborate with zero fcov diagnostics and zero total errors |
| Same matrix with `KUDU_FCOV_OFF` | All eight pass |
| Explicit bind-root audit | 64 connections, zero unresolved |
| Checker regressions | Eight pass with pyslang available |
| Compressed encoding enumeration | All 65,536 words in both alias modes; 33 named bins checked |
| Actual SV helper evaluation | 23 category cases, 19 coarse mappings, eight saved-metadata qualifiers pass |
| Timing helper tests | Normal ordering, orphan response, queue overflow, timestamp overflow and grant-wait overflow pass |
| Native directed context test | Invalid-slot gating, no self-cross, stalled category retention, simultaneous enqueue/dequeue, bad younger slot, special drain, flush and reset pass |
| Final native KuduCfg1 ISA smoke | `isa_test1`, UART stop at 15,172 cycles |
| Final native KuduCfg1 CHERIoT smoke | `cheri_test1`, UART stop at 1,384 cycles |
| Final native RV32-mode AMO smoke | `rv32ua-p-amoadd_w +PMODE=0`, explicit `RISCV Test passed`, 183 cycles |
| Behavioral non-interference | Final coverage-on `isa_test1` instruction trace is byte-identical to the coverage-off build under identical delay/seed settings |

Native smoke tests used seed 1, instruction/data grant maxima 3 and response
maxima 4. Final native build: `final_cfg1_JJSro1`; final directed test:
`final_context_test_AHZ5lv`. An earlier integrated KuduCfg2 CHERIoT smoke also
completed; the final source/configuration combinations are covered by the
elaboration matrix above, not a claim of a full native regression.

The initial native smoke attempt could not load the images because the
non-DII path uses `./bin`, not `+BINDIR`. Those timed-out attempts were rejected
as validation evidence. Subsequent runs used read-only `bin` symlinks in fresh
run directories. Exit status alone was not accepted as success.

Native URG output is in `final_context_report/`. The following are **covered
cross bins / total cross bins from the single final isa_test1 run**, not a
coverage-closure claim:

| Context | Resident x issued | Resident x selected special |
|---|---:|---:|
| IR0 | 21 / 49 | 9 / 88 |
| IR1 | 25 / 56 | 9 / 88 |
| ALU0 | 24 / 42 | 4 / 18 |
| ALU1 | 21 / 42 | 4 / 18 |
| MULT | 13 / 42 | 0 / 18 |
| LSU | 15 / 42 | 2 / 18 |

The different IR0/IR1 issue totals are intentional: a bad younger instruction
can remain present while the older instruction issues.

VCS reports exclusions for some parameter-filtered bins with empty value sets;
these are reviewed applicability exclusions, not unexplained lost bins.
Pre-existing RTL-only elaboration warnings remain. This task does not claim
lint-clean RTL or exhaustive configuration reachability.

### Re-running the source checks

From `sim`, with pyslang installed or the retained dependency directory on
`PYTHONPATH`:

```sh
python3 fcov/check_syntax.py --matrix
python3 fcov/check_syntax.py --matrix --coverage-off
python3 fcov/check_binds.py
python3 fcov/check_isa_encoding_sets.py --classifiers
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s fcov -p test_checkers.py
python3 fcov/check_flow_bus_timing.py
python3 fcov/count_cov.py
```

The timing checker creates a new UUID-named output directory on each invocation.
For `tb_fcov_context.sv`, compile the RTL packages, `kudu_fcov_pkg.sv`,
`kudu_fcov_context.sv` and the testbench with VCS in a fresh directory, select
`-top tb_fcov_context`, and invoke both compile and simulation via `submit -i`.

## 7. Deferred work and remaining limitations

- Pipeline context observes registered ALU/MULT stages, normal LSU WAW
  residency and the active complex AMO sequence. It does not distinguish
  internal LSU substages or establish producer/consumer data dependence
  merely because two categories coexist.
- No full 19-by-19 cross product or speculative blanket reachability exclusions
  were added. The remaining cells still require scenario-specific closure work.
- The pre-existing ISA retirement tap samples before tracer `fill_cmt_info`,
  suppresses commit-error cycles and does not follow the final temporal-safety
  output FIFO. Its operand/result/tag coverage is therefore not upgraded here
  to an independently verified architectural-completion oracle.
- Broad operation x operand/result, capability bounds/permission/sealing, and
  prediction-to-resolution/revocation-to-final-tag temporal crosses were not
  added without reliable matching provenance. Adding same-cycle crosses would
  falsely imply that unrelated samples describe the same instruction.
- The source-backed exclusions are not an exhaustive audit of every old bin.
  In particular, architecture-facing fault goals were not removed merely
  because the current RTL does not appear to produce them.
- Store-access cause bins remain. The current LSU's handling of some store
  bus faults warrants separate RTL/specification review; this coverage-only
  change does not hide it by removing the goal or modifying RTL.
- The new schema must use fresh coverage databases. Neither unchanged
  instance names nor successful elaboration establishes compatibility with
  older merged coverage data.

## 8. Hierarchical submodule expansion

Added **28 coverpoint declarations** in four existing files. There are no new
coverage modules, covergroup types, binds, ports or FIFO tracking models.
`kudu_fcov_bind.sv` and `kudu_fcov.f` are byte-for-byte unchanged from the start
of this expansion. The source census is now 15 covergroup types, 454 coverpoints
and the existing two cross declarations; these are not expanded bin counts.

### Added observations

| File / existing group | Coverpoints | Purpose |
|---|---|---|
| `kudu_fcov_if.sv` / `cg_ma_if` | `cp_prefetch_capacity`, `cp_prefetch_redirect_request` | Request capacity and held/new request arbitration during redirects |
| Same | `cp_fifo_clear_level`, `cp_fifo_word_flow`, `cp_fifo_empty_bypass` | Registered words encountered on clear, word arrival/pop, and instruction transfer from an empty FIFO |
| Same | `cp_fifo_instr0_alignment`, `cp_fifo_instr1_alignment`, `cp_fifo_aligner_offset` | Instruction length at each PC halfword offset, plus effective aligner selection |
| Same | `cp_fifo_pair_lengths`, `cp_fifo_advance_pop` | All four dual-instruction length pairs and seven legal byte-advance/word-pop cases |
| Same | `cp_fifo_tail_ready`, `cp_fifo_split_second_source`, `cp_fifo_word_errors` | Tail waits, arriving/buffered second words, and first/second-word errors |
| Same | `cp_fifo_alt_restore_level`, `cp_fifo_alt_save_pop` | Restored word count and preservation of the second instruction during ALT capture |
| `kudu_fcov_id.sv` / `cg_ma_id` | `cp_s0_stored`, `cp_s0_read_source`, `cp_final_fifo_full_exchange` | Configured FIFO occupancy, accepted read source, and full-stage replacement |
| `kudu_fcov_ex.sv` / `cg_ma_alu` | `cp_compare_path`, `cp_shift_amount` | Integer comparison decisions and shift boundaries inside `rv32_alu` |
| `kudu_fcov_lsu.sv` / `cg_ma_lsu` | `cp_lsif_hold_capture`, `cp_lsif_delayed_backlog` | Actual hold-register capture source and buffered work at held-request completion |
| Same | `cp_wb_storage_flow`, `cp_waw_resident_head_cancel` | Empty/stored writeback FIFO transfers and cancellation of a still-resident reserved head |
| Same | `cp_lsu_start_blocker`, `cp_split_load_capture` | Outstanding-response/downstream start blockers and successful first-word capture for split loads |
| Same / `cg_ma_dcache` | `cp_waw_read_source` | Stored versus write-through reservation reads from the cache's WAW FIFO |
| Same / `cg_ma_trvk` | `cp_saved_range` | Eligibility of the valid saved capability under the actual range/sealing predicate |

The existing unconditional fetch FIFO occupancy point was retained rather than
duplicated. Each new instruction-alignment point has eight bins: 16/32-bit
instructions at byte offsets 0, 2, 4 and 6 within a 64-bit word. These sample
accepted, nonfaulting FIFO outputs before predictor substitution. Word-flow
observations exclude clears; clear/ALT observations have their own event guards.
ALT-only additions have zero instance weight when ALT is disabled.

The ID observations select the appropriate named FIFO hierarchy for
`StageBypass`, with depth-specific bin filtering. Other data observations use
accepted transfers or valid saved descriptors. No new illegal bins or speculative
structural assertions were introduced.

The ALU comparison point samples signed/unsigned selection, the XOR of operand
sign bits, and greater-or-equal result for accepted SLT/SLTU operations. Its
eight combinations are reachable: the sign-difference bit does not identify
which operand is negative, so swapping operands permits either result.

### Validation of this expansion

All artifacts are isolated under `sim/fcov_submodules_20260913_4SjOxC/`.
Existing user databases/results were not replaced or merged.

| Check | Result |
|---|---|
| Coverage-on and coverage-off elaboration matrices | All 16 combinations pass; only permitted upward-name warnings in coverage sources |
| Bind audit and structure hashes | 57 explicit connections resolve; bind/file-list hashes unchanged |
| Checker regressions / whitespace | Nine tests pass; `git diff --check` passes |
| Native KuduCfg1, zero-wait `isa_test1` | UART stop at 7,026 cycles; trace byte-identical to a fresh coverage-off reference |
| Native KuduCfg1, delayed `isa_test1` / `cheri_test1` | UART stops at 15,119 / 1,399 cycles |
| Native KuduCfg1, delayed RV32 AMO test | `rv32ua-p-amoadd_w +PMODE=0 +RISCV_TEST_SUITE`: explicit pass at 174 cycles |
| Native KuduCfg2 / KuduCfg3, delayed `isa_test1` | UART stops at 13,466 / 15,285 cycles; exercises alternate FIFO/bypass hierarchies |
| Native URG, KuduCfg1 delayed ISA | Both alignment points hit 8/8 bins; advance/pop hits 7/7; tail readiness hits 2/2 |
| Native URG, ID FIFO cases | KuduCfg1 stored/read-source/exchange hits 4/4, 4/4, 2/2; KuduCfg2 hits 3/3, 1/1, 2/2 |

Final builds are `final_cfg1_isOomA`, `final_cfg2_npiwSj` and
`final_cfg3_17hreY`; reports are `final_report_cfg1_qATqAk/report` and
`final_report_cfg2_lJHw8b/report`. Final coverage-enabled simulations use a
separate `run.vdb` in each fresh run directory. Licensed commands ran through
`submit -i`. Delayed runs use seed 1, grant maxima 3 and response maxima 4.

Same-seed random-wait coverage-on/off traces were not byte-identical, so those
runs are not claimed as bitwise non-interference evidence. The zero-wait
comparison removes randomized memory delays and is byte-identical, including
cycle fields. No testbench or RTL changes were made to force a comparison pass.

### Limits

This is a targeted next-level expansion, not closure of all submodule behavior.
The ISA smoke does not hit the new split-load capture bins and only lightly
exercises comparator/shift boundaries; these remain test-generation goals.
Native hits demonstrate sampling, not exhaustive functional correctness.

`mult_pipeline` places `multdiv32` in an unnamed generate scope. Its internal
points were deferred rather than retaining fragile `genblk3` paths, relaxing
the checker, changing RTL or adding a bind. `cmplx_unit` has no child module.
RV32B and CHERI ALU internals were not expanded speculatively.

## 9. Configuration-bin warning cleanup

Removed the configuration-dependent **FCVWCS**, **FCWCIEFF**, **PSBU** and
runtime **FCPSBU** warnings without suppressing diagnostics. Changes are
limited initially to bin definitions in **kudu_fcov_id.sv**,
**kudu_fcov_ex.sv** and **kudu_fcov_context.sv**, plus documentation.
The subsequent TRVK bind guard is described below.

VCS diagnoses a named bin whose configuration filter removes every value.
An explicit `item` predicate removes the missing-item warning but does not
solve the empty-bin problem. Returning an empty value queue merely changes
the warning to **FCEBR**. The retained implementation uses filtered array
bins over sets containing at least one applicable value instead.

| Coverpoint | Applicable values after cleanup |
|---|---|
| ID **cp_s0_stored** | 0 empty, 1 one, 2 intermediate, 3 full; intermediate is omitted for the same bypass/depth conditions as before |
| ID **cp_s0_read_source** | 0 stored, 1 empty/one, 2 empty/two, 3 stored/input; only 0 outside the stage-0-bypassed configuration |
| ALU **cp_is_cheri** | 0 integer; 1 capability only in CHERI builds |
| ALU **cp_fwd** | 0 none, 1 EX2, 2 WB, 3 both; only 0 and 2 for a single-stage ALU |
| MULT **cp_input_category** | MUL/DIV, plus the same three CHERI categories when enabled |
| Context **cp_special** | EXEC/SYSCTL/IRQ/DEBUG, plus CMPLX when RV32A is enabled |
| Context **cp_special_phase** | Drain/execute/flush for IR; drain/flush for pipeline residents |

ALU **cp_ex2_waw_match** is a whole disabled coverpoint in a single-stage
configuration. It keeps its ordinary hit bin and existing zero instance
weight instead of constructing an empty bin. Its raw bin count consequently
changes from zero to one in that configuration, but it remains excluded from
the instance's weighted score.

The context cross exclusion now selects phase/event values rather than the
renamed individual bins. Non-EXEC flush combinations remain excluded. Some
bin names change to indexed array names; start a fresh coverage database.
Coverpoints, covergroup types, binds and RTL are otherwise unchanged.

### Validation

Outputs are isolated under **sim/fcov_warning_cleanup_20260913_uxHzNT/**:

- CHERI KuduCfg1/2/3 builds have zero VCS-coded compile warnings and no
  coverage-bin initialization warnings. Native ISA traces are byte-identical
  to the corresponding pre-cleanup delayed runs.
- Native URG comparisons for KuduCfg1/2 show identical expected, uncovered
  and covered counts for all changed active ID/ALU/MULT coverpoints and both
  context crosses in every context instance.
- A non-CHERI build has no configuration-bin warnings, retains only the
  integer/MUL/DIV goals in the affected coverpoints, and passes the AMO smoke.
- All eight coverage-on and eight coverage-off pyslang configurations pass;
  nine checker regressions and the native directed context test pass.
- Bind/file-list hashes and the 454-coverpoint source count are unchanged.
  No existing user database, log or result was replaced.

Final native builds: **clean_cfg1_qdtxLb**, **clean_cfg2_QeFTu0**,
**clean_cfg3_O3xIWT**, and **clean_rv32_fM4v8k**. Each has its own
**report/grpinfo.txt**. The directed context output is **context_test_A7AqUH**.

The initial warning cleanup left **BTNL** for the non-instantiated TRVK
target in non-CHERI builds. A follow-up now guards that existing bind with
the **CHERIoT** build define, after verifying that **tb_kudu_top** and
**check_syntax.py** set it consistently with **CHERIoTEn**, and that
**kudu_top** passes **CHERIoTEn** to both LS-pipeline enable parameters.
Thus the bind is retained in CHERI-capable builds, including runtime RV32
mode, and omitted from non-CHERI builds. No bind, module or warning
suppression option was added. Custom testbenches must keep the define and
DUT parameter consistent. Pyslang's intentional upward-name diagnostics
remain visible.

The bind follow-up was validated in **sim/fcov_trvk_bind_20260913_YvdIMa/**:
both native builds have zero VCS-coded compile warnings and pass the AMO
smoke with unchanged traces. Native reports confirm TRVK coverage is absent
in the non-CHERI build and present in the CHERI-capable build even with
**PMODE=0**. Both configuration matrices and all nine checker regressions
also pass.

## 10. Discard bitmap fix and coverage-wide width audit

### Corrections

**kudu_fcov_if.sv / cp_discard:** replaced the explicit OR reduction with the
complete **{branch_discard_q, discard_req_q}** expression. The old expression
was a valid two-bit summary, not an implicit truncation, but it collapsed
one, two and three pending branch discards into the same bin. It also had a
misleading response-event comment despite sampling every cycle.

The corrected point has **PrefetchDepth + 1** bits. Normal bins distinguish
every legal bitmap and held-request discard flag:

- Depth 2: encoded states 0, 1, 2, 3, 6, 7.
- Depth 3: encoded states 0, 1, 2, 3, 6, 7, 14, 15.

The bitmap is a low-order prefix because older outstanding requests are marked
first. OR-ing the RTL's existing prefix, redirect-marked outstanding prefix
and accepted-cancelled-request prefix preserves this form; shifting on a
response also preserves it. A **non_prefix** illegal bin and matching
**AssertDiscardPrefix** make that invariant explicit rather than silently
ignoring malformed masks.

**kudu_fcov_if.sv / kudu_fcov_bind.sv:** removed the four-bit narrowing of
FIFO occupancy. It was sufficient for the current depths, but would truncate
counts of 16 or more. The coverage port and connection now retain the unsigned
32-bit count.

**kudu_fcov_ex.sv / kudu_fcov_bind.sv:** matched the complex-unit FSM's actual
two-bit RTL type instead of widening it to four bits. Current/next-state
concatenation is now four bits, not eight. State and transition constants
follow the same width; the impossible 4-through-15 illegal-state bin was
removed. The existing state assertion remains.

### Audit scope and retained intentional summaries

Reviewed all 454 coverpoint declarations and the associated input declarations,
bind transformations, helper functions and explicit bin ranges across the
coverage sources:

| Sources | Width/reduction review |
|---|---|
| IF, bind and context | Discard bitmap and occupancy fixes above; scalar stage-valid bits and logical issue slots retained; saved instruction categories remain enums |
| ID, ISSUE, EX, LSU and CMT | FSM width fix above; slot/hazard/handshake vectors, pipeline selections, write-port masks and sysctl concatenations checked |
| ISA and system coverage | Saved instruction/operand metadata, memory masks, interrupt vectors, permission/tag fields and scalar predicates checked |
| Bus and bus-timing helper | Byte enables, AMO flags, data framing, 64-bit delay/count arithmetic and response qualifiers checked |
| Shared package | Category reductions, first-set-state decoding and low-32-bit value classification checked against their intended summaries |

The explicit forwarding-mask reductions intentionally report which pipeline
has any forwarding activity; occupancy points intentionally count set bits.
Full slot/hazard vectors and relevant mask coverage remain separate. The bus
compressed-data labels were checked and are correct: a two-bit instruction
prefix equal to 11 means **not compressed**.

No additional accidental scalarization or bin-width defect was confirmed in
the remaining reviewed code. This is not a proof of architectural coverage
completeness or of every future configuration's reachability.

### Regression protection and validation

Added an elaborated-DUT regression to **test_checkers.py**. It checks both
prefetch depths, the exact discard concatenation operands and widths, the
32-bit FIFO count, and two-bit FSM/four-bit transition widths. It would fail
if the discard bitmap were replaced by a one-bit reduction again.

Outputs are isolated under **sim/fcov_vector_audit_20260913_J5WISh/**:

- All eight coverage-on and eight coverage-off elaborations pass; all ten
  checker tests pass.
- Native KuduCfg1/2 builds and coverage initialization are warning-free.
  Delayed ISA traces are byte-identical to the pre-change references.
- Native URG reports **8/8 cp_discard bins** hit for depth 3 and **6/6**
  for depth 2, with zero non-prefix hits.
- The AMO smoke passes with an unchanged trace and visits all four complex
  FSM states; five of its six selected transition bins are hit.
- The prefetch prefix update was separately enumerated over 144 cases at
  depth 2 and 256 cases at depth 3, preserving the invariant in every case.

Final native builds are **final_cfg1_mpqUUX** and **final_cfg2_cgLp02**;
the AMO run is **final_cfg1_mpqUUX/amo_j0EHxe**. Each report is in that
build/run's **report/grpinfo.txt**. No RTL, new coverage modules or new binds
were introduced. Existing user results and databases were preserved.

## 11. Explicit decode-error category bins

### Definition and changes

The requested **cp_err0 / cp_err1** are in **kudu_fcov_id.sv**. Their
sampled signals are three-bit **fcov_err_kind_e** categories produced by
**fcov_err_kind**, not the five-bit **ir_errs_t** error masks.

Replaced automatic enum bins with these explicit bins in both slots:

| Encoding | Bin | Coverage classification |
|---|---|---|
| 0 | none | Normal |
| 1 | permission | Normal |
| 2 | bounds | Normal |
| 3 | illegal_instruction | Normal |
| 4 | illegal_compressed | Normal |
| 5 | fetch | Normal |
| 6 | multiple | Normal |
| 7 | reserved | Illegal |

An illegal instruction is a valid error-category value; it must remain a
normal coverage goal. Likewise, the decoder assigns raw error flags
independently, so simultaneous errors are not a structural violation.
The existing classifier deliberately maps all multi-flag masks to
**ERR_MULTIPLE**. Its behavior is unchanged.

Each point retains its existing slot-valid sampling guard. Added
**AssertErr0Encoding / AssertErr1Encoding** with the same guards to back
the reserved illegal bins. The coverpoint expressions pack the enum into
a three-bit vector: VCS rejects a numeric reserved value on an enum-typed
coverpoint because that value has no named enum member. Packing avoids
that restriction without widening or reducing the sampled value.

Extended **test_checkers.py** to inspect both elaborated coverpoint widths,
all eight bin names, their exact encodings, and normal/illegal status.
A separate exhaustive test evaluates the actual classifier for every
five-bit input mask: zero, each single error, and all multi-error masks.
No new coverpoints, modules, binds, or RTL changes were introduced.

### Validation and remaining unrelated blocker

Native outputs are isolated under
**sim/fcov_id_error_bins_20260913_muXqhE/**:

- KuduCfg1 CHERIoT VCS compilation and ISA simulation produced no coded
  compile/runtime warnings. The run finished by UART at 15,119 cycles.
- URG confirms seven normal bins and one reserved illegal bin per point.
  The ISA smoke hit **none** in both slots and **illegal_instruction**
  in slot 0, with zero reserved-bin hits. Other error categories were not
  exercised by this smoke; their mapping is covered by the exhaustive
  classifier regression.
- The instruction trace is byte-identical to the preceding vector-audit
  run, **final_cfg1_mpqUUX/isa_tMu8nE**.
- All 11 checker unit tests pass, as do all eight coverage-off elaborations.

The full coverage-on pyslang matrix remains blocked by an unrelated edit
in **kudu_fcov_if.sv:442**: **iff pdt_en_i** is missing parentheses.
VCS accepts that spelling, but pyslang reports two syntax errors in each
configuration. That file was left unchanged during this fix. The passing
scoped bin tests and native run do not imply that the full coverage-on
pyslang matrix passes.

The successful run is **isa_DgElEm** and its native bin report is
**report/grpinfo.txt**. The earlier failed enum-bin compilation and all
existing results/databases were preserved.

## 12. IR source addresses and write/source equality coverage

Added **19 coverpoints**, containing **248 normal bins**, inside the
existing **cg_ma_id** in **kudu_fcov_id.sv**:

| Addition | Points | Bins per point | Qualification |
|---|---:|---:|---|
| rs1 and rs2 in each logical IR slot | 4 | 32 | Slot valid and corresponding read enable |
| Each RF write-port address | 3 | 32 | Corresponding write enable |
| Each write port versus each source in each slot | 12 | 2 | Write enable, slot valid and corresponding read enable |

Each address point has one explicit array bin per five-bit address.
The source-read enable mapping is **rs1 -> rf_ren[0]** and
**rs2 -> rf_ren[1]**, matching the decoder. Slot 0 uses **ira_dec_o**;
slot 1 uses **irb_dec_o**. These are logical IR output records, not
upstream physical decoder slots.

Added five-bit **rf_waddr0_i / rf_waddr1_i / rf_waddr2_i** coverage-module
inputs. Their names match the RTL inputs, so the existing wildcard bind
connects them directly. **kudu_fcov_bind.sv** documents this mapping;
there are no new modules or binds.

The comparison family is named **cp_rf_waddrN_rsS_L**, where N is the
write port, S is source 1 or 2, and L is logical slot 0 or 1. Every point
has **same** and **different** bins. Comparisons are gated, rather than
embedding enables into the sampled Boolean: idle/disabled cycles must
not fill **different**. There are no new SystemVerilog cross declarations.
All observations retain the covergroup's reset guard.

These points include address zero and do not assert a forwarding or RAW
dependency simply because addresses match. Existing x0 summaries remain
unchanged. Write-address points intentionally sample enabled writes even
when neither IR slot is valid.

### Verification

Extended the actual-DUT regression in **test_checkers.py** for KuduCfg1
and KuduCfg2. It checks all 19 point widths and bin definitions, resolves
each write-address bind back to the correct five-bit RTL signal, evaluates
address expressions across 0 through 31 with equal and unequal operands,
and evaluates the real sampling guards for every combination of slot-valid,
read-enable and relevant write-enable bits.

All 11 checker tests pass. Native KuduCfg1 VCS compilation and ISA
simulation produced no coded warnings. The ISA run finished at 15,119
cycles, with an instruction trace identical to the preceding error-bin
run. URG reports exactly 32 bins for each new address point and two bins
for each comparison. **Both bins in all 12 comparison points were hit.**
Address coverage remains partial with this smoke workload.

Artifacts are isolated in **sim/fcov_id_registers_20260913_3W47ur/**;
the run is **isa_HZLSqn** and the native report is
**report/grpinfo.txt**. The unrelated IF syntax issue recorded in section
11 is unchanged; these results do not claim a passing full coverage-on
pyslang matrix. No RTL or existing results/databases were modified.

## 13. Branch-unit functional coverage

### Ownership and sampling

Added **cg_ma_branch** inside **kudu_fcov_alu** in **kudu_fcov_ex.sv**,
under a generate condition selecting the existing **alu0** coverage owner.
Its two instances are **FC_MA_EX.branch.ir0 / FC_MA_EX.branch.ir1**.
This adds **14 source coverpoints / 28 instantiated points** and one
covergroup type, with no new modules, binds or ports.

Observations use **kudu_top.branch_unit_i** directly. Physical A/B decode
records and forwarded operand pairs are selected using **ira_is0_i**, so
they correspond to the unit's age-ordered IR0/IR1 outputs. Misprediction,
JALR target and CJALR error results come from the actual RTL outputs rather
than a duplicate implementation of its decision functions.

Sampling occurs at the clock edge with reset released, during issuer
**DECODE**, for a valid, hazard-free branch/JAL/JALR candidate, excluding
existing decode errors and commit-error cycles. Issue is deliberately not
required: capability faults prevent issue. These points measure evaluation
opportunities, including ready candidates that stall or are later discarded,
not retired instructions. **cp_issued** distinguishes issued from held
evaluations without suppressing fault coverage.

### Added points in each logical slot

| Point | Bins / purpose |
|---|---|
| **cp_kind** | Conditional branch, JAL, JALR |
| **cp_mapping** | Both physical A/B ordering polarities |
| **cp_issued** | Evaluated candidate issued or not issued that cycle |
| **cp_branch_outcome** | Taken/not taken for BEQ, BNE, BLT, BGE, BLTU and BGEU: 12 bins |
| **cp_compare_operands** | Six feasible sign/equality combinations of the resolved 32-bit operands |
| **cp_branch_direction** | Forward/backward crossed with actual taken/not-taken |
| **cp_branch_prediction** | Predicted direction crossed with actual outcome |
| **cp_branch_target_match** | Target agreement when predicted and actually taken, with checking enabled |
| **cp_mispredict** | Full four-bit result: none, taken miss, not-taken miss, JAL target miss, JALR miss |
| **cp_jalr_prediction** | Not predicted, correctly predicted, wrong target |
| **cp_jalr_target_low** | All four raw target low-bit combinations |
| **cp_jalr_immediate** | Zero, positive, negative other than -1, and -1 |
| **cp_cjalr_check** | Whether capability checking is enabled for this evaluation |
| **cp_cjalr_errors** | All eight three-bit error-mask combinations |

The CJALR mask is **{execute permission, sealing rules, tag}**. Simultaneous
violations are legitimate outcomes. No illegal bins or new RTL invariants
were invented. JALR prediction uses the unit's actual misprediction output;
the RTL compares predicted source addresses/capabilities rather than simply
comparing against the computed address-plus-immediate result.

The JAL target-miss bin is omitted when **ChkBranchJALAddr** is false.
The branch-target-agreement point retains its bins with zero instance weight
in that configuration, avoiding empty-bin warnings. Non-CHERI builds retain
only zero-error and check-disabled CJALR bins. The raw JALR target can have
bit 0 set; any downstream masking is outside this point's scope.

### Validation and limits

The new scoped regression in **test_checkers.py** checks active ownership,
both slot instances, all point widths, physical-to-logical mapping expressions,
reset/evaluation sampling policy, output tap ordering and the complete
three-bit error range. It passes for KuduCfg1/2 with CHERIoT on and off.
This is elaborated-source inspection, not a dynamic branch truth-table test.

Native VCS compilation and simulation produced no coded warnings for:

- CHERIoT KuduCfg1: ISA and CHERI workloads, plus the eight self-checking
  **rv32ui-p-beq/bne/blt/bge/bltu/bgeu/jal/jalr** tests in runtime RV32 mode.
- Non-CHERI KuduCfg2: the self-checking AMO smoke, exercising the configuration
  with branch/JAL target checking enabled.

URG confirms separate IR0/IR1 groups and configuration filtering. The eight
branch/jump tests hit **12/12 condition/outcome bins in IR0** and **7/12 in
IR1**; operand sign/equality coverage is **6/6** and **5/6**, respectively.
Both physical ordering polarities are hit in both slots. The ISA smoke also
hits all three JALR prediction outcomes and four CJALR error masks in IR0.
These runs validate collection, not complete closure of every added bin.

The ISA smoke finishes at 15,119 cycles with a trace identical to the preceding
register-coverage run; the CHERI smoke finishes at 1,399 cycles. Existing
results were preserved. New outputs are:

- **sim/fcov_branch_20260913_EBfqzw/**: **isa_test1_ziC3yU**,
  **cheri_test1_093QIK**, and **branch_isa_uCs7hb**, each with its own report.
- **sim/fcov_branch_rv32cfg2_20260913_BQTqoi/amo_ZzDABR/**.

All eight coverage-on parser configurations still report only the unrelated
two IF syntax errors documented in section 11; the new EX hierarchy introduces
only permitted upward-name warnings. The full parser matrix is therefore not
reported as passing. User edits to ID coverage and the IF syntax were left
untouched; validation used the new branch-specific regression rather than
claiming that the older register-point regression matches the revised ID model.

## 14. PredictRA-gated ID prediction points

Patched the current **kudu_fcov_id.sv**, retaining the user's manual register
crosses, revocation bins and other edits. The snapshot comparison shows only
the new prediction tap and the adjacent prediction-coverpoint changes.

- Added a conditional hierarchical tap of the two-bit
  **ir_stage.gen_stage1.cjalr_predict_ok** signal.
- Added **cp_cjalr_predict_ok** with **none / slot0 / slot1 / both** bins.
  The full two-bit vector is retained, but invalid physical decoder slots
  are masked out using **s0_rd_valid**; entirely invalid cycles do not sample.
- Retained **cp_cjalr_pcc_set**, including its existing **hit** bin, and
  added **no_update** for the deasserted output.
- Both points use **CjalrPredictEn = PredictRA && CHERIoTEn &&
  !StageBypass[1]**. Disabled configurations neither sample nor contribute
  weight. The helper signal is tied to zero only in those disabled
  configurations, avoiding references to a nonexistent generate scope.

No new ports or bind changes were needed. Prediction eligibility and PCC
update are intentionally separate: the RTL additionally requires stage-1
valid/ready acceptance before asserting the PCC-update pulse.

Validation outputs and the pre-edit snapshot are isolated under
**sim/fcov_id_predict_20260913_1nzBJK/**. Native VCS compilation and ISA
simulation produced no coded warnings; the trace is unchanged from the
branch-coverage baseline. In **isa_eXMot4/report/grpinfo.txt**, the prediction
point has four bins (three hit; **both** remains uncovered), and the PCC
point has two bins, both hit.

Elaborated-expression checks verify widths, valid-slot masking and sampling
truth tables for normal KuduCfg1, bypassed KuduCfg2, non-CHERI KuduCfg1,
and a KuduCfg1 copy with **PredictRA=0**. The unrelated two IF parser errors
remain; no other elaboration errors were found in those checks.

## 15. CJALR source-register role

Added **cp_cjalr_rs1_0 / cp_cjalr_rs1_1** to the current ID coverage
file. Each has **ra** (**rs1 == 1**) and **other** (**rs1 != 1**,
including x0) bins. Sampling requires CHERIoT support, runtime CHERI mode,
the corresponding valid slot, **is_jalr**, and **rf_ren[0]**.
The points do not depend on **PredictRA** and have zero weight in
non-CHERI builds. These remain decode-stage observations, not retire counts.

The snapshot comparison confirms that only these two points were inserted
into **kudu_fcov_id.sv**; manual changes were preserved. Outputs are isolated
under **sim/fcov_cjalr_rs1_20260914_KzkUQn/**. Native compilation and runs
produced no coded warnings, and the CHERI-mode ISA trace was unchanged.
Both bins were hit in both slots. The separate runtime-RV32 JALR test passed
with zero hits in all four new bins, confirming that ordinary JALR does not
fill CJALR coverage.

Elaborated-expression checks cover all 32 source registers and all slot-valid,
read-enable, JALR and runtime-mode combinations in CHERI-on/off, bypassed,
and PredictRA-off configurations. Only the existing unrelated IF syntax
errors remain in those elaborations.

## 16. Bus coverage source-file merge

Moved **kudu_fcov_bus_timing** into **kudu_fcov_bus.sv** and removed the
separate **kudu_fcov_bus_timing.sv** source and its file-list entry.
Both module bodies are byte-identical to the pre-merge snapshots; module
names, ports, hierarchy, timing logic and coverage declarations are unchanged.

Updated **check_flow_bus_timing.py** to compile the merged file with
**KUDU_FCOV_BUS_TIMING_ONLY**, which excludes the covergroup owner and its
package imports for the standalone Verilator test. Normal VCS builds do
not define this macro and include both modules.

All five standalone timing scenarios pass, including expected fatal-error
cases. Full VCS compilation and ISA simulation produce no coded warnings;
the instruction trace remains byte-identical to the preceding CJALR run.
The coverage declaration census is unchanged.

Pre-merge sources and native outputs are preserved under
**sim/fcov_bus_merge_20260914_hOMWTI/**, with the ISA run in **isa_qfpRlv**.
Standalone logs are in
**sim/fcov/flow_bus_timing_runs/325683d41028446396ef902c56665728/**.

## 17. RA update with a stalled predicted CJALR

Added **cp_ra_update_jalr** in **kudu_fcov_issue.sv**, the existing issuer
coverage owner; no **fv_issuer.sv** exists in this checkout. No RTL, coverage
ports or binds were changed.

The temporal monitor captures IR1's predicted RA when an issuing IR0 writes
register 1 and the younger predicted CJALR reading register 1 is RAW-stalled.
It follows that consumer into logical IR0 and samples its resolved forwarded
RA once, after hazards clear. Both physical A/B mappings are supported.
Flushes, commit errors, mode exit and replacement consumers cancel pending
observations; a redirect caused by the resolving CJALR still permits sampling.

The three requested bins distinguish semantic equality and predicted
more/less authority using expanded bounds and permission-set inclusion.
An explicit **other** bin separates mixed/incomparable changes and
address/tag/object-type/reserved-bit differences. Expanded bounds retain the
33-bit upper limit. Non-equal untagged or inverted-bound comparisons are not
classified as more/less permissive. These are issuer evaluation events,
not retirement assertions.

The standalone **tb_fcov_issuer_ra.sv** fixture passed with eight samples.
URG reports equality **1**, predicted more permissive **2**, predicted less
permissive **2**, and other **3**. The fixture also checks delayed/one-shot
sampling, consumer promotion, both physical mappings, same-cycle redirect,
cancellation and rejection of unrelated/unpredicted pairs. Function checks
exercise the 33-bit bound and incomparable permission bit sets. Outputs are
preserved in **sim/fcov_issuer_ra_20260922_xerYUE/**.

A full cfg1 CHERI VCS build and delayed ISA simulation passed without coded
warnings. The run stopped at **15,119 cycles** and its instruction trace is
byte-identical to the bus-merge baseline. Outputs are isolated under
**sim/fcov_issuer_ra_dut_20260922_8kCSCA/isa_CBj1HG/**. The directed fixture
validates the monitor and its bins; it does not demonstrate DUT stimulus
closure of this rare corner.

All eight coverage-on pyslang configurations still report only the two
pre-existing IF syntax errors at **kudu_fcov_if.sv:442**. The new hierarchical
observations produce permitted upward-name warnings, not new elaboration
errors. The global parser matrix is therefore not reported as passing.

## 18. Top-level coverage owner and scoreboard FIFO occupancy

Renamed the bus coverage owner and source to **kudu_fcov_top** and
**kudu_fcov_top.sv**. Updated the bind instance, main/fatal group names,
file list, standalone timing checker and current ownership documentation.
The report groups are now **FC_MA_TOP** and **FC_MA_TOP.fatal**. The
**kudu_fcov_bus_timing** helper remains unchanged in the renamed file.

Added **cp_sbd_fifo_level**, observing the RTL's signed eight-bit
**kudu_top.sbd_fifo_i.fifo_level** directly, without casts or truncation.
Sampling is at each rising clock edge with reset released. The seven bins
are **0**, **1**, **2**, **3**, **4**, **5**, and **6 and above**.
The existing bus/fatal coverage is unchanged apart from naming.

The standalone **tb_fcov_top.sv** fills a real depth-eight FIFO and samples
each occupancy from zero through eight once. VCS/URG reports one hit in each
of the six individual bins and three hits in the combined **6+** bin.
Full-DUT cfg1 CHERI compilation and delayed ISA simulation also pass, with
an unchanged instruction trace and the renamed report hierarchy. This ISA
smoke hits levels zero through five but not six and above; the directed
fixture checks that bin's implementation, not DUT stimulus closure.

Native outputs are preserved under **sim/fcov_top_20260923_xhQDGX/**:
**directed_J6Ozrm/** and **dut_mZ0dT6/isa_dDvEIP/**. All five standalone
timing scenarios pass; their logs are under
**sim/fcov/flow_bus_timing_runs/ca0b2ceae0e64f33ae0115b8877043ca/**.
Use a fresh coverage database for the renamed hierarchy and new point.

## 19. Issuer per-register reservation bits and hazard crosses

Removed **cp_wrsv** and **cp_cheri_trsv**. Their population counts are replaced
by **cp_ir0_waw_st**, **cp_ir1_waw_st**, **cp_ir0_raw_st**,
**cp_ir1_raw_st**, **cp_ir0_cheri_trsv_st**, and **cp_ir1_cheri_trsv_st**.
The four RAW/WAW points each have 31 overlapping wildcard bins for bits
1 through 31; the CHERI points each have 15 for bits 1 through 15.
All six inputs preserve the RTL's 32-bit width and use the existing wildcard
bind. No RTL or bind declaration changes were needed.

Each point has an **x_cp_<signal>** cross against **cp_hazard**, reusing
its valid-masked **hazard_q** value. The six crosses contain 616 bins in
total. Multi-hot masks count every set bit; bit zero is excluded, and CHERI
bits above 15 neither add bins nor prevent lower-bit matches. CHERI points
and crosses have zero weight when CHERIoT or load filtering is absent.

The existing standalone issuer fixture now supports **+hazard_bits**.
Native VCS/URG checks verify all 154 individual bit bins have exactly five
hits and every cross bin has the expected count (two for **both**, one for
each other hazard class). The original RA prediction scenarios still pass.
The final directed outputs are in
**sim/fcov_issue_bits_20260923_KlCwu7/final_FIvfWJ/**.

A fresh full-DUT build and delayed ISA simulation pass without coded warnings,
stop at 15,119 cycles, and retain the byte-identical trace from the top-coverage
baseline. Outputs are in
**sim/fcov_issue_bits_20260923_KlCwu7/dut_4q1WSK/isa_n3qNJt/**.
Directed collection validates bin/cross semantics, not DUT coverage closure.
Explicit bin declarations preserve the existing source-census checker's
counts. Start a fresh coverage database for this schema change.

## 20. Registered reservations and forwarding/reservation pairs

Replaced the six derived per-slot state points and their crosses from section
19 with **cp_reg_wrsv_q** and **cp_reg_cheri_trsv_q**, plus
**x_cp_reg_wrsv_q** and **x_cp_reg_cheri_trsv_q** against **cp_hazard**.
The input ranges match the RTL's **[31:1]** and **[15:1]** declarations.
Zero padding preserves register numbering in the existing wildcard masks.
There are 46 set-bit bins and 184 hazard cross bins; multi-hot masks count
all reserved registers.

Added **cp_fwd_wrsv_r1** through **cp_fwd_wrsv_r31**. Each covers the
two-bit pair **{ir0_pl_fwd_act[n], reg_wrsv_q[n]}** with individual bins
for **00**, **01**, **10** and **11**, without a reservation or valid-slot
sampling gate. No register-zero pair is created.

The issuer fixture's **+hazard_bits** run verifies exact counts in every
reservation and cross bin. Its new **+forwarding_pairs** run uses unequal
counts per register and pair value, verifying all 124 pair bins, register
indexing, pair order and exclusion of forwarding bit zero. The original
RA prediction run also passes.

Native results are preserved in
**sim/fcov_issue_regs_20260923_p1YpSc/directed_Gs6WdS/**. Full-DUT cfg1
CHERI compilation and delayed ISA simulation pass without coded warnings;
the 15,119-cycle trace matches the preceding baseline byte for byte. That
run is preserved in **dut_HDO970/isa_BUtsqc/** under the same parent.
The existing wildcard bind connects the restored reservation ports without
bind changes. Other coverage and the user's edits remain intact.

## 21. Bug-driven coverage from the RTL bug cross-check

Implemented the recommendations of **sim/testplan/fcov_bug_crosscheck.md**,
which checked the model against KUDU-001..074. The per-group list, weight-0
tripwires and new illegal bins are in the README section "Bug-driven
coverage". Changes stay inside existing covergroups; no new covergroup was
created.

**Compile fixes.** The model did not elaborate on HEAD: the issuer bind now
connects **debug_single_step_i** to **debug_step_i** and **single_step_trap_q**
to **step_req_q** (renamed in 127aade), and the **cp_pdt_pc_set** guard gained
its LRM-required parentheses.

**Additions.** 46 coverpoints, 19 crosses and 9 assertions:

* **kudu_fcov_issue.sv**: 20 points, 10 crosses, 3 assertions (trap context,
  mtval class, system instructions by mode, interrupt priv/mie/blocking,
  debug-entry source and races, CHERI dependence consumer class). The trap
  context uses **ISSUE_CYCLE** guards inside **cg_ma_issue** rather than the
  separate **cg_ma_trap_ctx** first proposed.
* **kudu_fcov_lsu.sv**: 12 points, 6 crosses, 4 assertions (split-access
  bus-error mtval, CSR ASR outcome, MSHWM update source, CLRPERM in debug
  mode, AMO bus-error/CHERI cause; dcache load forwarding behind an in-flight
  request). **kudu_fcov_dcache** has four new **.*** ports.
* **kudu_fcov_csr.sv**: 7 points, 1 cross, 1 assertion (debug CSR writes by
  pmode, trap-entry kind and mcause/mepc invariant, MSHWM write-to-store
  distance, minstret and mstatush tripwires). Five new **.*** ports.
* **kudu_fcov_id.sv**: 4 points, 1 cross, 1 assertion (fetch-error headroom
  window, B-extension near-miss encodings).
* **kudu_fcov_if.sv**: 3 points, 1 cross (JAL with prediction disabled, RA
  prediction before/after an RA update). New **PredictRA** parameter and
  **cur_ra32_i** port; the bind passes **PredictRA**.

**cp_step_with_ie** is now weight 0 (unreachable, KUDU-029), and the
**cp_dbg_entry_src** ebreak bin samples the ebreak entry term instead of the
trigger match. **FC_MA_ISSUE** now has 113 points and 17 crosses; the census
in **test_issue_sampling.py** and the expected report count in
**run_issue_sampling.py** (130; the optional baseline snapshot is compared on
its own 100 points) were updated to match. The stub testbenches
(**tb_fcov_frontend_temporal.sv**, **tb_fcov_lsu_semantics.sv**,
**tb_fcov_accuracy.sv**) carry the new signals.

**Validation.** pyslang **check_syntax.py --matrix**: 0 errors in all 8
configurations, no new non-hierarchy warnings. **check_binds.py**: 49
connections, 0 unresolved. **test_issue_sampling** passes; **test_checkers**
has the same 3 failures as before this change. VCS **-cov -nowave** builds
**simv** and **simv32** with no warnings. Smoke runs (isa_test1, cheri_test1,
dbg_test1, coremark.rv32o3, cheri_test1 with memory delays and interrupts)
and all **sim/tests_2** reproducers (138 runs: 116 PASS, 11 XFAIL for open
bugs, 11 DEFER, 0 FAIL) ran on the coverage build without any illegal-bin hit
or FCOV assertion. **run_lsu_semantics.py**, **run_fcov_accuracy.py**,
**run_frontend_temporal.py** and **run_issue_sampling.py** pass. Scratch area:
**/home/scratch/fortress/kunyanliu/kudu_temp/fcov_review_20261114_144820/**
(**build_impl**, **smoke_impl**, **t2_impl**).

Start a fresh coverage database for this schema change.
