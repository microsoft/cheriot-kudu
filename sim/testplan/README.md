# CHERIoT-Kudu design-verification test plan

**Status:** Draft for review. **Baseline:** repository sources inspected on
2026-09-15, with hardware-report coverage policy refreshed on 2026-09-29
and implemented coverage goals/sampling refreshed on 2026-10-01.
Coverage targets and future automation below are proposed sign-off
requirements, not claims that verification or coverage closure is complete.

## 1. Comprehensive DV strategy

CHERIoT-Kudu verification combines three complementary methods:
coverage-driven differential simulation, end-to-end formal verification, and
FPGA/emulation-based system testing. None replaces the others.

| Method | Primary purpose | Evidence required |
|---|---|---|
| Functional-coverage-driven simulation using TestRIG and Sail | Explore architectural behavior and implementation scenarios with directed and generated programs | Matching architectural traces, checked termination, no unexpected assertions/illegal-bin hits, reproducible coverage |
| End-to-end FV: Sail/RTL architectural trace equivalence | Establish that RTL behavior refines the ISA model for all executions within explicit assumptions | Reviewed correspondence, assumptions and proof decomposition; completed proof obligations; no unexplained inconclusive results |
| FPGA/emulation platform, using CHERIoT-SAFE as an example | Exercise complete systems and realistic software over long runs with Kudu or Ibex | Repeatable boot, software and peripheral tests, core-selection records, and investigated discrepancies |

### 1.1 Coverage-driven simulation

The primary simulation loop is:

1. Derive tests and generator constraints from architectural requirements and
   uncovered functional scenarios.
2. Run identical architectural stimulus against Kudu RTL and the CHERIoT Sail
   reference model, with explicitly aligned initialization and environment.
3. Compare ordered architectural observations, not cycle timing.
4. Diagnose mismatches and assertion failures, preserve the reproducer, and
   reduce it where supported.
5. Review coverage holes; add targeted stimulus or justify an exclusion.
   Retain every resolved bug as a regression.

TestRIG supplies the differential-testing framework. Directed assembly,
archived ELFs, standard RISC-V instruction tests, CHERIoT tests and application
workloads complement generated instruction streams. Sail is the architectural
reference; Ibex comparisons provide useful additional evidence but must not
be treated as an independent specification.

Architectural checks must address instruction/PC progression, register results,
capability tags and metadata, memory side effects, exceptions, relevant CSRs,
and supported interrupt/debug behavior. Compare only fields that the selected
trace interfaces actually expose. A missing observation is an integration gap,
not an implicit pass.

Instruction and data wait states may differ from Sail's abstract timing.
Interrupts, injected errors and revocation events need a common architectural
event schedule or a separately validated checker. Merely applying an interrupt
at the same cycle number to different cores does not establish equivalent
stimulus.

### 1.2 End-to-end formal verification

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
an unbounded equivalence proof.

Existing [JasperGold scripts](../../fv/fv_kudu.tcl) and block-oriented
[formal files](../../fv/) provide complementary assertion/FIFO/LSU work.
Their presence is not evidence of completed Sail-to-Kudu trace equivalence.

### 1.3 FPGA/emulation and system software

Use [**CHERIoT-SAFE**][safe] as the example platform configurable with either
**Kudu or Ibex**. Run the same applicable software and platform configuration
with each core, recording the selected core and build revisions. FPGA
prototyping is the intended example here; no commercial emulation integration
is implied.

The platform includes TCM, an AXI fabric, debug support and peripherals.
Its [documented configurations][safe-config] and
[FPGA build selector][safe-build] provide:

| CHERIoT-SAFE selector | Core | Data-interface width |
|---|---|---:|
| Default/configuration 0 | CHERIoT-Ibex | 33 bits |
| **-conf1** | CHERIoT-Ibex | 65 bits |
| **-conf2** | CHERIoT-Kudu | 65 bits |

These are **platform selectors**, not Kudu's pipeline-configuration numbers.
The documented FPGA target is Arty A7-100T with Vivado. Match clock, UART and
firmware settings, and use the correct 33-/65-bit image format; a platform
misconfiguration must not be reported as a CPU architectural mismatch.

Planned system campaigns include boot and reset, CHERIoT RTOS applications,
compartment transitions and capability faults, allocation/revocation stress,
interrupt-heavy workloads, debug, peripheral I/O and long-duration operation.
Require observable software verdicts and preserve console output, firmware,
bitstream identity, configuration and failure context.

Compare architectural/software outcomes, not identical cycle counts or
performance. Align memory maps, ABI, enabled ISA extensions, peripherals,
firmware and interrupt behavior before attributing a difference to the core.
FPGA runs do not automatically populate the VCS covergroups; their evidence
must remain separately identified unless coverage extraction is implemented
and validated.

## 2. TestRIG and the Kudu simulation flow

### 2.1 TestRIG reference

Use the [TestRIG **dii-read-from-file** documentation][testrig] for test
generation, ELF construction, Sail reference execution and Kudu/Sail trace
comparison. Flow details,
setup instructions and file formats are maintained in TestRIG rather than
duplicated in this plan.

### 2.2 Kudu testbench organization

**tb_kudu_top** instantiates the DUT, memory model, interrupt generation and
statistics/logging infrastructure. The shared
[data memory model](../tb/data_mem_model.sv) supplies instruction and data
responses, sparse-memory access, capability tags, atomic response information,
the temporal-safety map and test termination interfaces.

| Control | Purpose |
|---|---|
| **CHERIoT**, **KUDU_PPL_CFG**, **KUDU_DW_MULT** build settings | Select architectural support, pipeline configuration and multiplier implementation |
| **+TEST**, **+BINDIR**, **+DBGROM** | Select workload and, for normal simulation, optional debug ROM |
| **+PMODE** | Choose runtime CHERI or RV32 behavior in a capable build |
| **+INSTR_GNT_WMAX / +INSTR_RESP_WMAX** | Vary instruction grant/response delay |
| **+DATA_GNT_WMAX / +DATA_RESP_WMAX** | Vary data grant/response delay |
| **+INSTR_ERR_RATE / +DATA_ERR_RATE / +CAP_ERR_RATE** | Configure memory/capability-error injection, subject to testbench enables |
| **+INTR_INTVL / +DBG_REQ_INTVL** | Configure interrupt/debug stimulus |
| **+TIMEOUT / +RVFI_MAX** | Bound cycles and, in DII mode, the emitted RVFI packet count |
| **+STAT_MCYCLE**, simulator random seed | Control statistics and reproducibility |

Delay/interval settings are four-bit values in the current testbench;
error-rate settings are three-bit values. Record effective settings printed
by the testbench, not just requested command-line values.

Normal simulation loads **./bin/TEST.vhx** and optional debug ROM data;
**BINDIR** currently affects DII ELF loading, not the normal VHX path.
Normal runs stop on the UART test-stop convention. RISC-V tests select the
tohost monitor with **+RISCV_TEST_SUITE**, whose explicit pass/fail message
must be checked. DII runs primarily stop at **RVFI_MAX**; UART output is not
their primary completion criterion.

Timeouts can end through **$finish**, so a zero simulator exit status is not
sufficient. A retirement-packet limit also proves only that a prefix ran,
not that a program completed or matched Sail.

The DII initialization includes reference-alignment forces on register/CSR
state and a Sail privilege-mode accommodation. Keep a separate reset and
privilege verification campaign that does not mistake those overrides for
verification of the DUT's natural reset behavior.

### 2.3 Comparison, reproducibility and data protection

Kudu/Sail trace comparison is covered by the [TestRIG flow][testrig].
Use its comparison results as architectural correctness evidence alongside
Kudu's functional coverage. Comparator operation and supported comparison
policies are documented in TestRIG, not in this plan.

Every result needs a manifest containing RTL/testbench/coverage/TestRIG/Sail
revisions, effective parameters, build flags, input hashes, seeds, delay/error
settings, initialization overrides, expected endpoint and comparison policy.
The replay runner's Python-generated delay choices must be recorded as well
as the simulator seed.

Run licensed VCS, simulation and URG jobs through **submit -i**. Use fresh,
isolated build/run areas and explicit per-run coverage databases.
The DII runner derives its working area from its own resolved script path and
replaces scratch input/result directories and its result archive; simply
changing the shell working directory or choosing a new **--cov_dir** does not
isolate all of its writes. Prepare an isolated workspace with the expected
relative layout before running it.

Never overwrite existing result archives, logs or databases without explicit
authorization, particularly **run_dii/cov_kudu.vdb**. Keep raw per-test coverage
where attribution is needed; URG accumulation can collapse tests into a merged
record. Do not merge different elaborations or changed coverage schemas into
an old database merely because names still match.

## 3. Coverage plan and goals

### 3.1 Campaign matrix

Kudu has **three major hardware-configuration/runtime-mode combinations**.
This axis is independent of the pipeline configuration selected by
**kudu_cfg_t**:

| Report domain | Operating mode | CHERIoTEn | cheri_pmode_i | Meaning |
|---|---|---:|---:|---|
| **RV32** | RV32-only configuration | 0 | Ignored; normally 0 | CHERIoT hardware disabled |
| **CHERIoT** | CHERIoT configuration, RV32-compatible mode | 1 | 0 | CHERIoT-capable hardware executing with CHERIoT behavior disabled |
| **CHERIoT** | CHERIoT configuration, CHERIoT mode | 1 | 1 | CHERIoT-capable hardware executing with CHERIoT behavior enabled |

Functional coverage has **two reports**, one per hardware elaboration, with
separate databases, applicable goals, exclusions and closure results.
The CHERIoT report combines PMODE=0 and PMODE=1 coverage; the RV32 report covers
CHERIoTEn=0 only. Do not combine the two hardware builds, even for RV32 tests.
The current campaign focuses on **KuduCfg1**. The eventual target is the same
two-report structure for **every supported kudu_cfg** (KuduCfg1/1x/2/3),
not a single score merged across pipelines.
Record the actual elaborated configuration, not merely a command-line label.

Within the combined CHERIoT report, all 30 ISA instruction-encoding
coverpoints are crossed with the instruction-associated **cheri_active** mode.
Shared instruction bins require hits in both modes; CHERI-only instructions
require mode 1, while AUIPC, C.ADDI4SPN and C.ADDI16SP require mode 0.
Impossible instruction/mode combinations are ignored in the crosses.
RV32-only hardware requires only mode 0. **FC_ISA_OPERANDS** has one
instruction/saved-mode cross; its other crosses omit mode. They cover only
applicable sources, immediates and capability results, pairing corresponding
CS1/CS2 and CD subfields with instruction identity. Crosses are partitioned by
arithmetic, multiply/divide, bit manipulation, control, memory, atomic, system
and CHERI instruction families. Genuine scalar values exclude capability
cursors; applicable CHERI crosses add the actual CS1 tag. No operand cross
exceeds four axes, and source-free operations never acquire dummy sources.

| Dimension | Planned coverage |
|---|---|
| Pipeline configuration | KuduCfg1 initially; eventually all supported KuduCfg1/1x/2/3 elaborations, with both hardware reports above |
| Hardware/runtime mode | Separate RV32-only and CHERIoT hardware reports; combine both runtime modes only within CHERIoT hardware, preserving instruction-associated mode information for delayed/retired events |
| Instruction set | RV32I/M/C and enabled A/B operations, CHERIoT operations and compressed forms, CSRs, legal operands and architecturally specified traps |
| Dependencies | RAW/WAW, per-register write/CHERI reservations crossed with slot hazards, forwarding/reservation bit pairs, x0, source/destination aliasing, simultaneous writes, ready/stalled pipeline combinations and both physical-to-logical slot mappings |
| Control flow | All six branch conditions, signed/unsigned boundaries, taken/not-taken, prediction direction/target errors, issued branch-misprediction events in each slot, JAL/CJALR, flush and recovery |
| Capability behavior | Tags, permissions, bounds and representability, sealing/sentry rules, capability loads/stores, temporal safety and revocation interactions |
| LSU/bus | Alignment and split accesses, byte enables, tags, LR/SC success/failure, AMO sequencing, grant/response timing, outstanding transactions, errors and cancellation |
| Asynchronous/system behavior | Interrupt classes and priority, CSR/trap state, debug entry/return/single-step, reset, fatal errors and recovery |
| Long sequences | Mixed pipelines, persistent pressure, wraparound, repeated faults, application/RTOS and long-running FPGA scenarios |

The matrix is a requirement list, not an assertion that all combinations are
supported. Record applicability and choose risk-based crosses rather than an
unbounded Cartesian product.

**Configuration selection:** the current simulation testbench selects
KuduCfg2 for selector 2, KuduCfg3 for 3, and KuduCfg1 otherwise. The default
selector 1 therefore matches the current KuduCfg1 campaign. KuduCfg1x remains
a future campaign target and needs an explicit simulation selection before
claiming its configuration closure.

CHERIoT-specific coverpoints and crosses sample only with
**CHERIoTEn == 1 && cheri_pmode_i == 1**. Saved decode/transaction metadata
additionally qualifies instruction-dependent and delayed observations; a
CHERIoT-capable bus width alone is not evidence of a CHERIoT operation.
Shared integer, trap, debug and control points remain active in all applicable
modes. Mixed points gate their CHERIoT-specific values without dropping
ordinary RV32 observations. Mode-identification points are intentionally
active across modes.

Keep the mode fixed within each sign-off run and merge only matching
**{kudu_cfg, CHERIoTEn, coverage schema}** results, combining both runtime
modes within the CHERIoT report. Mode-switch tests are a separate campaign,
not a substitute for exercising both runtime modes. CHERIoT-only goals are
**not applicable**, rather than uncovered requirements, in the RV32-only
hardware report; they remain required in the combined CHERIoT report.
The union does not license CHERI-only hits from RV32 runtime observations.
Runtime sampling guards do not remove bins from VCS's elaborated denominator;
retain raw and applicability-adjusted scores with reviewed exclusions.

The regression and DII runners separate raw collection and accumulated
databases by hardware build, not PMODE:

| Runner | CHERIoT hardware database | RV32-only hardware database |
|---|---|---|
| Regression | **cov_kudu_regr_cheriot.vdb** | **cov_kudu_regr_rv32.vdb** |
| DII | **cov_kudu_cheriot.vdb** | **cov_kudu_rv32.vdb** |

**--cov_dir** supplies a basename: **results/campaign.vdb** produces
**results/campaign_cheriot.vdb** and/or **results/campaign_rv32.vdb**.
**--cov_report** generates **urgReport_cheriot/** and/or **urgReport_rv32/**
for the builds selected. Historical unsuffixed and **_pmode0/_pmode1** databases
remain untouched: no migration and no use as merge inputs.

Regression **--build all|cheriot|rv32** defaults to **all**. Under **all**, RV32
CoreMark and RISC-V tests run with PMODE=0 on both hardware builds; CHERIoT/debug
tests run only on CHERIoT hardware with PMODE=1. Labels and artifact paths
distinguish builds. DII **--build cheriot|rv32** defaults to **cheriot**:
**--rv32** retains its runtime meaning, selecting **simv +PMODE=0** on CHERIoT
hardware instead of default **simv +PMODE=1**. **--build rv32** selects
**simv32 +PMODE=0**. The **vcscomp** scripts already build both binaries, so
**--compile** invokes compilation once. Each build uses its own design database
(**simv.vdb** or **simv32.vdb**); the regression permits **--design_vdb** overrides
only when one build is selected. Pipeline/build separation and reviewed
applicability exclusions remain necessary for sign-off.

### 3.2 Feature-to-evidence plan

| Goal | Stimulus and evidence |
|---|---|
| Every enabled instruction/format and meaningful operand class | TestRIG generation plus directed ISA/CHERIoT programs; Sail comparison and retire coverage |
| Correct behavior under microarchitectural pressure | Dependency chains, independently varied instruction/data delays, queue boundaries, pipeline mixtures and recovery; microarchitectural coverage plus architectural comparison |
| Register reservations and forwarding | Exercise each write-reservation bit 1–31 and CHERI reservation bit 1–15 with the four slot-hazard states; cover legal forwarding/reservation pairs 00, 01, 11 per register, reject illegal 10, and exercise both physical slot mappings |
| Commit writeback and destination collisions | Exercise each port's registers 1–15 in CHERI mode and 1–31 in RV32 mode; cover nonzero destination equality for port pairs 0/1, 1/2 and 0/2, including an early load suppressed by a younger writer |
| Scoreboard pressure | Reach FIFO occupancy 0, 1, 2, 3, 4, 5 and 6 or more using producer/commit pressure and delayed operations; retain architectural comparison through drain and recovery |
| LSU queue pressure | Reach WAW FIFO levels 0, 1 and 2+, and writeback FIFO levels 0 and 1+; exercise fill, drain, flush and write-through behavior without treating bypass traffic as stored occupancy |
| Branch prediction recovery | Trigger issued conditional-branch mispredictions in both logical slots; distinguish event hits from unqualified prediction evaluations and verify architectural recovery |
| CJALR corner cases | rs1 equal/not equal to c1, prediction eligibility versus actual PCC update, older IR0 updating RA while predicted IR1 CJALR stalls, immediate/target boundaries, tag/sealing/execute-permission faults, checking bypass modes |
| Accurate memory and atomic behavior | Read/write/SC/AMO/tag scenarios with delayed responses; compare architectural effects and check queued transaction attribution |
| LSU response metadata and raw capabilities | Exercise all eight legal permission-clear masks, load/store and capability classification, tagged/untagged raw memory returns, compressed exponent classes and top/base comparisons; distinguish returned transaction metadata from a newer live request |
| Split-access and capability errors | Inject valid error responses in the three selected LSU states; exercise allowed/denied CSR ASR checks, load/store CHERI faults and alignment-only versus other faults |
| Forwarding-cache match behavior | Exercise individual one-hot read/write matches and all six legal weight-2 write masks; hit invalidation and saved-unaligned cases with two write matches; retain read-weight <=1 and write-weight <=2 invariants |
| Precise exceptions and control events | Faults in each relevant slot, competing events, older in-flight work, drain/execute/flush sequencing and absence of killed side effects |
| Temporal safety | Revocation/no-revocation, outstanding capability accesses, stalls and tag clearing; observe both 0 and 1 for each map-address bit 0–9 while chip select is asserted; explicit reference/environment correspondence |
| Sound monitors and trace transport | Directed tests of sampling guards, widths, slot ordering, queues, AMO retirement, overflow/error detection and coverage-on/off non-interference |
| System operation | Same applicable firmware on Kudu/Ibex platform configurations, meaningful software verdicts and long-run failure capture |

The existing mini-regression, RISC-V suite and
[coverage regression runner](../run/run_cov_regression.py) are starting
corpora, not a complete feature plan. Maintain a directed test or documented
generator recipe for every difficult-to-hit scenario. Coverage collected from
a failing run is useful for diagnosis, but must not silently become passing
sign-off evidence.

### 3.3 Proposed closure and sign-off gates

| Area | Goal / required disposition |
|---|---|
| Architectural comparison | Zero unexplained mismatches for all required tests and reference-supported scenarios; verify nonempty traces and the agreed comparison interval |
| Functional coverage | 100% of applicable planned legal bins and required crosses per hardware build and pipeline configuration, per instance after reviewed exclusions; both runtime-mode instruction goals must close within the combined CHERIoT report |
| Code coverage | Target 100% of reachable line, branch and FSM goals; review condition/toggle coverage and justify every residual hole or exclusion, not just a global average |
| Assertions and illegal bins | Zero unexplained failures; demonstrate activation/non-vacuity for required checks; illegal bins are not hit targets |
| Formal | All release-required obligations proved within reviewed assumptions; bounded, inconclusive, waived and unsupported obligations reported separately |
| System/FPGA | All required software/platform campaigns pass on the declared Kudu configurations; investigate differences from Ibex where both are applicable |
| Reproducibility | Each failure reproducible from preserved artifacts; fixed bugs retained in the regression corpus |
| Exceptions | Every exclusion has requirement, configuration, rationale, evidence, owner and review record; no unreviewed coverage or proof holes |

These are draft gates for review. Unsupported features must be scoped out
explicitly, not made invisible by reducing a weight until a score improves.
Report raw and adjusted coverage together. A plateau or a large instruction
count is not a substitute for reaching the required scenarios.

Code coverage should be restricted to the DUT, using the flow's hierarchy
configuration. Functional coverage uses its own sampling and applicability.
Report line/condition/toggle/FSM/branch/assertion metrics separately; they do
not share one meaningful denominator with functional covergroups.

### 3.4 Coverage-model review and closure process

Before relying on coverage, review each point's requirement, sampled event,
width, legal values and configuration applicability. In particular:

* Distinguish physical A/B records from age-ordered IR0/IR1 and associate valid
  bits with the correct records. A signal's name alone is not proof of ordering.
* Preserve multi-bit masks when bit identity matters. Simultaneous legitimate
  error flags are not automatically illegal encodings.
* Qualify crosses at the intended same-cycle event. Independent coverpoint
  hits do not establish a dependency or a causal relationship.
* Do not credit idle, stale, cancelled or mode-inapplicable values accidentally.
  Document intentional coverage of evaluated-but-not-issued candidates.
* Audit the retire tap and reference trace for common omissions. Shared tracer
  types and matching widths do not prove complete architectural observation.
* Keep disabled bins and reviewed ignore/illegal bins separate from normal
  goals. Couple structural illegal-bin assumptions to assertions.

For each uncovered goal, determine whether the cause is missing stimulus,
an incorrect sampling guard, an RTL defect, an unsupported configuration,
or a genuinely unreachable state. Use waveform/trace evidence or formal
analysis where appropriate before adding an exclusion.

Proposed execution cadence is a small smoke after relevant changes, regular
directed and differential regressions, broader seeded/configuration campaigns,
and milestone closure reviews plus long-running platform tests. Automated
scheduling and dashboards are planned workflow, not a claim of an existing
CI service.

## 4. Current functional coverage organization

The model is organized under [sim/fcov](../fcov/README.md).
[kudu_fcov.f](../fcov/kudu_fcov.f) orders its sources and
[kudu_fcov_bind.sv](../fcov/kudu_fcov_bind.sv) installs the monitors.
Top-level bound owners also observe relevant child modules hierarchically;
coverage need not add one bind per child.

| Group | Current focus |
|---|---|
| **FC_ISA_INSTR** | Retirement observations; all 30 instruction-encoding points crossed with saved CHERI-active mode, result/memory attributes and control-flow/trap indicators |
| **FC_ISA_OPERANDS** | 165 instruction identities, one instruction/mode cross and 127 family-qualified operand crosses; genuine scalar operands, actual capability sources/tags and matching CS1/CS2-to-CD fields; 128 crosses, each at most four-way |
| **FC_ISA_CSR** | Architectural CSR, privilege, interrupt, trap and debug state/events |
| **FC_MA_IF** | Fetch/prefetch handshakes, outstanding/discard state, fetch FIFO occupancy and alignment, split instructions, ALT buffering and prediction |
| **FC_MA_ID** | IR storage/handshakes, decode categories and errors, register read/write address crosses, revocation, breakpoints, CJALR source role and prediction/PCC update |
| **FC_MA_ISSUE** | Issue arbitration and slot mapping; per-register reservations and hazard crosses; forwarding/reservation pairs; branch-misprediction events; stalled CJALR RA comparison; stalls, routing, special events and control sequencing |
| **FC_MA_EX** | ALU0/1, mult/div/CHERI and AMO complex-unit behavior; forwarding/WAW/handshakes; branch-unit evaluations in separate IR0/IR1 groups |
| **FC_MA_LSU** | Load/store pipeline, dcache and revocation; LSU-local FIFO occupancy, response metadata/raw capability fields, native FSM transitions and error states, CHERI response checks, cache match masks and invalidation |
| **FC_MA_CMT** | Completion/commit combinations, scoreboard/errors/flushes, mode-specific per-register write coverage and three destination-collision pairs |
| **FC_MA_TOP** | Scoreboard FIFO occupancy; instruction/data requests, data attributes, actual grant/response delays and metadata, temporal-safety map including per-bit address goals, interrupt/debug inputs and fatal-error lifecycle |
| **FC_MA_CONTEXT** | Resident instruction classes in IR/ALU/MULT/LSU crossed with current issue or selected special-event phases |

### 4.1 Important organization and sampling details

**CSR organization:** **kudu_fcov_csr.sv** separately owns **FC_ISA_CSR**;
**kudu_fcov_isa.sv** owns instruction coverage. CSR/trap/debug sampling is
unchanged by the source split. The LSU's redundant CSR/SCR access points
**cp_access**, **cp_op_en**, **cp_op**, **cp_read_only**, **cp_cheri**,
**cp_addr** and **cp_illegal**, plus their unused ports, have been removed.
LSU request classification (**cp_is_csr**), temporal-safety enable coverage,
and the LSU-local ASR-denial check remain; a denied access need not reach
the CSR block.

**Retirement:** ISA coverage follows the tracer's retirement FIFO walk and
separate AMO retirement event. It uses shared **tracer_pkg::instr_trace_t**,
not a private mirror type. Instruction encodings, including compressed forms,
are sampled from the trace; mode-specific classification uses saved decode
information rather than a live mode pin. The tap uses **fill_cmt_info()**,
including older/faulting records in commit-error cycles and first-phase AMO
errors. Operand coverage includes execute-stage faults with captured sources;
invalid records and interrupt-only packets do not fill it. Issue-side traps
fill only the instruction/mode cross, not source/immediate or CD goals.
Capability fields use **mem_cap_t**, not the internal register layout.
CD goals require a nontrapping, nonzero capability destination; integer
results such as CGETTAG's 0/1 result have no capability CD goals. Matching-field
crosses exclude impossible copies, tag creation, permission changes and
bounds exponents. Temporal-safety builds sample the tracer's final FIFO,
including the resolved revocation tag, with saved mode carried through.
Expanded instruction bits supply immediates, with signedness, scaling and
reachable classes specialized per instruction. Raw bounds-field coverage does
not imply coverage of decoded absolute bounds or representability.

**Execution:** ALU instances retain separate reports. Branch coverage is owned
once through the existing ALU0 monitor and reports **FC_MA_EX.branch.ir0/ir1**.
It samples valid, hazard-free evaluations, not only issued instructions, so
CJALR faults that prevent issue remain observable.

**Issuer:** the current **kudu_fcov_issue.sv** model uses the registered
reservation bitmaps, not the intermediate per-slot RAW/WAW/CHERI state
coverpoints and their six crosses, which were removed.

| Coverpoint / cross | Coverage meaning |
|---|---|
| **cp_reg_wrsv_q** | One overlapping set-bit bin per register 1–31 |
| **cp_reg_cheri_trsv_q** | One overlapping set-bit bin per register 1–15 |
| **x_cp_reg_wrsv_q**, **x_cp_reg_cheri_trsv_q** | Each reserved register crossed with **hazard_q** through **cp_hazard**: none, IR0, IR1 or both; 124 and 60 cross bins respectively |
| **cp_fwd_wrsv_r1** through **cp_fwd_wrsv_r31** | Each **{ir0_pl_fwd_act[n], reg_wrsv_q[n]}** pair: 00 neither, 01 reserved only, 11 both are legal; **pair_2** (10, forwarding only) is illegal and backed by an SVA; 93 legal goals plus 31 illegal bins |
| **cp_branch_mispredict_event** | Separate IR0/IR1 hit bins from the full two-bit event, already qualified by branch decode and issue in RTL |
| **cp_ira_is0** | Both physical-to-logical mappings: IRA is IR0 when 1, IRB is IR0 when 0 |
| **cp_mcause** | Issuer-generated exception/IRQ causes, each fast IRQ ID 0–14, and forwarded commit-error causes, sampled only on non-debug cause saves |

These points sample on rising clock edges outside reset. Reservation inputs
retain their **[31:1]** and **[15:1]** indexing; multi-hot bitmaps hit every
applicable set-bit bin. **hazard_q** masks invalid slots, but the reservation,
forwarding-pair and slot-mapping points intentionally include idle cycles.
The crosses show coexistence, not proof that a particular reserved register
caused the hazard. CHERI reservation coverage and its cross require CHERIoT
mode and have zero weight when CHERIoT or load filtering is compiled out.

**cp_mcause** retains all six cause bits and requires **csr_save_cause_o**
with **debug_csr_save_o** clear, excluding idle/default values and debug
entry. Its bins follow issuer cause selection, including the LSU fault causes
forwarded on commit flush; it does not count software writes to MCAUSE.

The existing **cp_ra_update_jalr** follows a predicted younger CJALR after
an issuing older instruction writes RA. It compares saved prediction and
resolved forwarded RA after the stall, with equal, predicted-more-permissive,
predicted-less-permissive and other/incomparable bins. This is an issuer
evaluation, not a retirement assertion.

**Decoder checks:** **FC_MA_ID.ir0_decoder** and **FC_MA_ID.ir1_decoder**
independently cover both values of **hdrm_ge4**, **hdrm_ge2**, **hdrm_ok**,
**base_ok**, **allow_all**, and **cheri_perm_vio**. Sample valid, nonflushed
decoder inputs in active CHERI mode outside debug, including faulting or
stalled instructions. With stage 1 bypassed, map validity to physical
mema/memb using **ira_is0_o**; otherwise use age-ordered **s0_rd_valid**.
Both groups have zero weight on RV32-only hardware. Goals include insufficient
two-/four-byte headroom, below-base PCs, full-address-space bounds (including
PC wraparound), and permission rejection, independently for each decoder.

**Context:** simultaneous pre-edge snapshots replace the former issue/event
streams. The frontend cross is **s0_rdata0 x s0_rdata1 x ir0 x ir1 x
special_event**, enabled only when **IrStageBypass[1] == 0**. Six independent
**ir0 x ir1 x special_event x ex_resident** crosses observe ALU0 WB, ALU1 WB,
LSU-interface **req_dly_q**, LSU **lsu_req_info_q**, MULT EX2 and MULT WB.
ALU categories use existing saved tags; MULT uses its saved instruction;
LSU uses valid request metadata, not WAW FIFO occupancy.

IR bins combine category with **pl_type**, distinguish faults, PC-trigger
debug, sysctl and complex AMO special instructions, and include **EMPTY**.
The event axis has overlapping **irq**, **error**, **debug**, and
**commit_error** bins (each tests only its asserted bit), plus **none** for
zero, in **{cmt_err_i, handle_debug, handle_err, handle_irq}** order.
An uncrossed **cp_special_event_value** retains all 16 exact masks in each
frontend/execution group. Feature/routing filters remove
impossible category/PL pairs and EX categories. Cross exclusions remove
younger-valid/older-empty S0/IR pairs, **error** with nonfault IR0, and
**none** with fault IR0. Other event bins retain both fault states because
they overlap masks with and without **handle_err**. A busy pipeline and a
matching IR pipeline assignment can coexist;
these are not same-instruction or producer/consumer crosses.

The **req_dly** tap excludes stale bypass copies in IDLE/DLY0_WGNT but includes
requests queued in DLY1/DLY1_WGNT, including early/CSR requests that arrive
behind delayed work. The LSU request tap uses **outstanding_resp_q**, and
AMO halves use **amo_flag** because their request record omits the opcode.
All invalid stages have an EMPTY bin. No new RTL state or decode is added.

**Top level:** the coverage owner and queued bus timing helper are in
**kudu_fcov_top.sv**, renamed from the bus owner; its single group is
**FC_MA_TOP**, including **cp_fatal_err**. Fatal state/transition coverage
retains falling-edge sampling through reset; all other points retain
rising-edge sampling outside reset. The fatal point has zero weight on
RV32-only hardware. Recompile into a fresh database for this group consolidation.
**cp_sbd_fifo_level** directly samples
the full signed eight-bit **sbd_fifo_i.fifo_level**, with separate bins for
**0 through 5**, plus **6 and above**. The current FIFO depth is eight.
Occupancy is sampled before rising-edge updates, outside reset.
The queued **kudu_fcov_bus_timing** helper and existing bus/fatal coverage
retain their transaction semantics. CHERI-only bus/tag/map/fatal points now
require CHERIoT mode; response-tag coverage also requires a request accepted
in CHERIoT mode. Response metadata is associated with accepted requests.
This is observed transaction timing, not simply coverage of requested
testbench delay settings.

**cp_operating_mode** in **FC_MA_TOP** identifies operating modes independently
of **kudu_cfg**, with goals filtered by static hardware: only **rv32_only** for
CHERIoTEn=0, and **rv32_compatible** plus **cheriot** for CHERIoTEn=1.
It is a run-classification check, not automatic partitioning of an accumulated
database. TOP/LSU **cp_pmode** and ID **cp_cheri_pmode** require both runtime
values on CHERIoT hardware, but do not sample and carry zero instance weight
on RV32-only hardware, where the mode pin is ignored.

The detailed commit, LSU, dcache and map-address goals added/refined through
2026-10-01 are specified in section 4.3 below. These are the final definitions,
not the superseded intermediate versions discussed during development.

Directed monitor fixtures exercise reservation bits/crosses, forwarding pairs,
branch-event sampling and scoreboard occupancy. Such fixture results establish
monitor behavior, not closure of those scenarios in the DUT. Use fresh coverage
databases for the renamed hierarchy and changed bins/crosses; preserve existing
reports and do not merge incompatible schemas.

### 4.2 Source census, not achieved coverage

The following snapshot is the coverage source census on 2026-10-10,
after the updates in this plan. Mode-qualified bins
and report denominators must be reviewed per hardware report domain.

| Organization | Covergroup types | Coverpoint declarations | Explicit crosses |
|---|---:|---:|---:|
| ISA instructions | 1 | 44 | 30 |
| ISA operands | 1 | 30 | 128 |
| ISA/CSR | 1 | 42 | 2 |
| IF | 1 | 62 | 3 |
| ID | 2 | 65 | 18 |
| Issue | 1 | 93 | 7 |
| EX, including branch groups | 4 | 92 | 14 |
| Context | 2 | 11 | 2 |
| LSU | 3 | 99 | 9 |
| Commit | 1 | 31 | 0 |
| Top level | 1 | 40 | 0 |
| **Total** | **18** | **609** | **213** |

The tool also reports **16 bind declarations**, **1,523 normal bin
declarations**, **75 illegal-bin declarations**, and **169 ignore-bin
declarations**. It reports the branch type separately as **cg_ma_branch**;
the table folds it into EX.

These are source declarations, not elaborated instance counts, expanded bin
counts, reachable goals or percentages achieved. Array/wildcard/transition
bins, crosses, generate conditions and repeated instances change the
elaborated model. Obtain actual closure denominators and scores from
configuration-specific VCS/URG reports.

Source checks cover declaration counts, bind resolution and configuration-matrix
elaboration with coverage enabled and disabled. Usage is documented in the
[functional coverage README](../fcov/README.md).

Full functional coverage is collected in the VCS flow. The standalone
covergroup-free timing-helper test can use Verilator; that does not establish
Verilator support for this functional coverage model.

### 4.3 Current detailed goals and directed targets (2026-10-01)

#### Commit register writes

**cp_rf_we** and **cp_rf_we2** have been removed. For each port **N=0,1,2**,
**cp_waddrN_cheri** has separate register bins **1–15**, qualified by the
port's write enable and effective CHERI mode. **cp_waddrN_rv32** has separate
register bins **1–31**, qualified by the write enable and inactive effective
CHERI mode. RV32-only hardware uses the latter regardless of the mode pin;
the CHERI points have zero weight there. Register zero is not an address goal.

**cp_waddr0_eq_waddr1**, **cp_waddr1_eq_waddr2**, and
**cp_waddr0_eq_waddr2** cover matching nonzero destinations. Ports 0/1
require their write enables. Port-2 comparisons use **load_early || load_late**
before arbitration, so an early load suppressed by a younger port-1 write
still credits its collision. Address points themselves require actual writes.
Directed tests must exercise all three pairs and show that stale/disabled
addresses and x0 do not credit collisions. **cp_we_vs_err** and its assertion
remain: an older instruction must commit when only the younger one faults.

#### LSU responses, capabilities and faults

All response metadata points below require **lsu_resp_valid**. CHERI-specific
points additionally require both current **cheri_active** and the responding
transaction's saved CHERI mode; they carry zero weight on RV32-only hardware.
Do not require a new request to be present when observing an older response.

| Point | Source and applicable goals |
|---|---|
| **cp_resp_clrperm** | Replaces request-side **cp_clrperm**. Read **load_store_unit_i.lsu_req_info_q.clrperm** for a capability response; separate hexadecimal bins **0, 1, 2, 3, 8, 9, A, B**, all with bit 2 clear |
| **cp_resp_is_load** | Saved **lsu_req_info_q.is_load**, covering both values in all operating modes |
| **cp_resp_is_cap** | **load_store_unit_i.lsu_resp_info.is_cap**, covering both values under the CHERI response guards |
| **cp_csr_cheri_asr_err** | Internal ASR error, separate clear/error bins on **csr_go_q** responses; include denied accesses, not just those passing **csr_access_o** |
| **cp_cheri_ls_err** | Internal load/store CHERI error, separate clear/error bins on non-CSR responses |
| **cp_ls_align_err_only** | On non-CSR responses with **cheri_ls_err=1**, distinguish alignment-only from other CHERI faults |

**lsu_resp_info** has type **pl_out_t**, which contains **is_cap** but not
**clrperm** or **is_load**. The latter fields therefore come from the saved
request associated with the response, not the live request bus.
Stimulus should change the live request while delaying its predecessor's
response, exercise each legal mask, and distinguish clear from faulting
responses. Error points must remain observable on failing responses.

**resp_mem_cap** casts **load_store_unit_i.data_rdata_i** to **mem_cap_t**
before permission/tag masking. Its seven coverage points observe successful
capability-load memory returns: require **lsu_resp_valid**, LSU data-valid,
no data or LSU response error, a saved load, capability classification, and
current/saved CHERI mode. This is not dcache-forwarding coverage.

| Raw capability point | Goals |
|---|---|
| **cp_resp_cap_valid** | Separate tagged and untagged bins; observe the raw tag even when **clrperm[3]** will clear the resulting register tag |
| **cp_resp_cap_rsvd**, **cp_resp_cap_cperms**, **cp_resp_cap_otype** | Per-value automatic bins for these small fields |
| **cp_resp_cap_cexp** | Separate bins for **0, 31, 24, 1**, and one scored bin combining **2–23 and 25–30** |
| **cp_resp_cap_top_vs_base** | **top8 == base9[7:0]**, **top8 > base9[7:0]**, and **top8 < base9[7:0]**; ignore **base9[8]** |
| **cp_resp_cap_addr** | Automatic range bins over the address field, not an exhaustive 32-bit value goal |

Only the raw-valid point samples untagged returns; all other raw capability
points require **resp_mem_cap.valid=1**. There are no standalone top8/base9
points. Directed cases should exercise the exponent boundaries, each
unsigned top/base relation with both values of base9[8], tagged/untagged
payloads, and suppression on invalid, erroneous or mode-inapplicable returns.

#### LSU sequencing, queues and crosses

**cp_transition** uses native **(state_a => state_b)** bins on **ls_fsm_cs**:
nine named transitions and five individual self-loops. It observes consecutive
samples of current state, not a same-cycle current/next-state concatenation.
Use delayed grants and split-access responses to exercise the paths and holds.
**cp_data_err_state** samples only with **data_err_i && data_rvalid_i** and
has three bins: **WAIT_RVALID_MIS**, **WAIT_RVALID_MIS_GNTS_DONE**, and **IDLE**.
Inject errors at each of these response phases rather than merely asserting
an error when no response is valid.

The two occupancy points stay inside **kudu_fcov_lsu.sv / cg_ma_lsu**:

| Point | Observed FIFO | Bins |
|---|---|---|
| **cp_waw_fifo_level** | **ls_pipeline.waw_fifo_i.fifo_level** | **0 / 1 / 2+** |
| **cp_wb_fifo_level** | **ls_pipeline.wb_fifo_i.fifo_level** | **0 / 1+** |

They sample signed eight-bit simulation counters before rising-edge updates,
outside reset. They measure stored occupancy, not bypass transfers.
Use producer/consumer pressure and fill/drain/flush sequences. No standalone
FIFO monitor or additional binds were added; these goals do not extend to the
dcache WAW FIFO or the RVFI FIFO.

The LSU group currently declares eight crosses:

| Cross | Constituent observations |
|---|---|
| **x_ls_type_1** | Request load/store, capability classification and cache eligibility |
| **x_ls_type_2** | Request capability classification, cache eligibility and CHERI request cause |
| **x_ls_cap_1** | Request load/store and capability-address alignment |
| **x_ls_rv32_1** | Request load/store, data size and address alignment |
| **x_access_err** | Writeback **cp_out_is_cap** and **cp_out_mcause**, from the same WB FIFO head |
| **x_resp_clrperm_1** | Raw response **cp_resp_cap_valid** and **cp_resp_clrperm** |
| **x_resp_clrperm_2** | Raw response **cp_resp_cap_cperms** and **cp_resp_clrperm** |
| **x_split_err_phase** | Saved load/store direction and split-access error phase |

The six CHERI-dependent request/response crosses have their own explicit sampling guards and
zero instance weight on RV32-only hardware; **x_ls_rv32_1** remains shared.
**x_ls_type_2** samples faulting requests, including both loads and stores.
The permission crosses require successful capability-load memory responses,
with a tagged raw capability additionally required by **x_resp_clrperm_2**.

**x_access_err** now samples both fields from the same valid, faulting
writeback, with current and saved WB CHERI-mode guards. **cp_out_is_cap**
has zero weight and serves only as its classification axis.
Directed cases must hold an older writeback while a newer response has the
opposite capability classification, and also exercise writeback without a
concurrent response. Test stored-head and empty-FIFO bypass mode provenance.
These are scenario goals, not correctness checks; assertions and architectural
comparison still establish correct fault handling.

The **store_fault** goal remains pending an RTL/architectural review:
**load_store_unit.sv** currently selects **LOAD_ACCESS_FAULT** for a bus error
without distinguishing stores. Do not waive this goal solely because the
current implementation cannot hit it. No RTL behavior is changed here.

#### Forwarding cache

**cp_rd_match** and **cp_wr_match** preserve the complete four-bit tag-match
mask rather than counting ones as the sampled value:

| Hamming weight | Read-match coverage | Write-match coverage |
|---|---|---|
| 0 | One miss bin | One miss bin |
| 1 | Separate bins for **0001, 0010, 0100, 1000** | Same four separate bins |
| 2 | Illegal | All six masks share **two_hits** |
| 3 or 4 | Illegal | Illegal |

The paired assertions enforce **$onehot0(rd_tag_match)** and
**$countones(wr_tag_match) <= 2**. Illegal masks are negative monitor-test
stimulus, not passing DUT coverage targets.
**cp_resp_inval_two_matches** and **cp_unaligned_two_matches** separately
require exactly two write-match bits and, respectively, **resp_invalidate=1**
or saved **unaligned_access_q=1**. Both may hit together.

**cp_rd_hit** and **cp_rd_match_ok** require **lsu_req_i=1**;
**cp_rd_hit_q** retains its existing sampling.
**cp_fwd_addr1** and **cp_fwd_data1** sample **fwd_info_o.addr1** and
**fwd_info_o.data1[31:0]** only with **valid[1]=1**, using automatic bins.
The 32-bit data slice excludes zero-filled capability-container bits and
provides 64 meaningful range bins in both hardware builds.
Exercise the active dcache forwarding path with varied destination registers
and data. The tied-off slot 0 is not a coverage target. Invalid slot-1 values
must not credit either point.

**cp_repl** requires an enabled cache and an actual line update after
invalidation priority. Exercise replacement into each way and an existing-line
update (**none**); idle selector rotation, disabled-cache activity and
invalidation-only cycles must not credit it.
**cp_update_valid** covers counts **0 / 1**; **2--4** are illegal.
**cp_update_invalid** covers counts **0 / 1 / 2 / 4**; **3** is illegal.
Each new illegal bin has an equivalent assertion. Verify legal masks and
separate intentional-negative cases; illegal hits are not closure targets.

#### Temporal-safety map address and response coverage

**FC_MA_TOP.cp_tsmap_addr_bits** adds 20 overlapping wildcard bins: a zero
and a one goal for every bit of **tsmap_addr_o[9:0]**, sampled with
**tsmap_cs_o && cheri_active**. Every selected address credits ten bins.
This is independent per-bit value coverage, not a requirement to reach all
1,024 addresses or to observe a transition. Exercise both values of every
bit during map reads. Existing **cp_tsmap_addr** range bins remain, and
CHERI map coverage has zero weight in the RV32-only hardware report.

**cp_tsmap_rdata** uses one-cycle-delayed request validity, matching the
synchronous map-memory response. Both request-time and current CHERI mode
are required, and reset clears pending validity. Exercise isolated reads,
back-to-back distinct population counts, idle data, reset with a pending read,
and mode changes between request and response. Address coverage retains
request-time chip-select qualification.

#### LSU request causes, capability loads and split faults

**cp_cheri_req_cause** now has named bins only for the encodings
**cheri_ls_check** can produce: **0** (alignment only), **1** (bounds),
**2** (tag), **3** (seal), **0x12** (load permission), **0x13** (store
permission) and **0x15** (store-capability permission). Every other value is
an illegal bin paired with **AssertCheriReqCauseReachable**. This shrinks
**x_ls_type_2** to 28 reachable goals. **cp_resp_early_cheri_cause** uses the
same bins for CHERI faults first detected at response time on requests that
were clean when issued, paired with **AssertRespEarlyCheriCauseReachable**.

Capability-load conversion adds three CHERI-only response points, sampled on
successful capability-load returns:

| Point | Goals |
|---|---|
| **cp_resp_cap_top_path** | All 8 combinations of **cexp == 0**, **base9[8]** and **top8 < base9[7:0]** for tagged raw capabilities |
| **cp_resp_cap_perm_effect** | Sealed/unsealed × **clrperm[0]** (GL/LG) × **clrperm[1]** (SD/LM) × whether the register permissions changed; 13 goals, including sealed SD/LM suppression and masks that change nothing because the permission was absent |
| **cp_resp_cap_tag_outcome** | Raw untagged, tag kept, and tag cleared by **clrperm[3]**; mismatching combinations are illegal and paired with **AssertRespCapTagMatchesClrperm** |

**cp_split_err_phase** and **cp_split_resp_is_load** sample the final response
of a split misaligned access: no error, first half only, second half only, or
both. **x_split_err_phase** crosses them with load/store direction (8 goals).
Inject bus/PMP errors on each half separately.

#### Temporal revocation semantics

**cp_clc_rd_i** now covers **x0** and separate bins **x1–x15**; CHERI
destinations above x15 are decoded as illegal. In the revocation stage,
**x_selected_bit** crosses **cp_selected_bitpos** (all 32 bit positions of
the map word) with **cp_selected_bit_value** (kept or revoked), sampled only
for in-range, tag-good capabilities (64 goals).
**cp_range_boundary** covers map word **0**, an interior word, the inclusive
**TSMapSize** limit, above the limit, and bases below **HeapBase**.
**cp_b2b_revocation_outcome** covers consecutive revocation checks whose
results differ (kept then cleared, cleared then kept).
Stimulus needs heap capabilities at both ends of the map and at every bit
position, with map bits both set and clear.

#### Capability bounds-setting outcomes

In **FC_MA_EX.mult**, CSetBounds, CSetBoundsExact, CSetBoundsImm and
CSetBoundsRoundDown are sampled at EX2 completion, only when both the saved
operation mode and current mode are CHERI. Every point and cross has zero
weight on RV32-only hardware.

| Point | Goals |
|---|---|
| **cp_setbounds_op** | The four bounds-setting instructions |
| **cp_setbounds_result_tag** | Result tag cleared or valid |
| **cp_setbounds_reason** | Success, exact request not representable, outside parent bounds, sealed or untagged input |
| **cp_setbounds_rounding** | Exactly representable, top rounded, base rounded, both rounded |
| **cp_setbounds_exp_path** | Normal exponent, second (overflow) exponent, and the two round-down exponent choices |
| **cp_setbounds_exp_class** | Result exponent **0**, **1–8**, **9–23**, **24–31** |
| **cp_setbounds_length_class** | Requested length **0**, **1–0xFF**, **0x100–0x7FFF_FFFF**, **2 GiB–4 GiB** |

Crosses **x_setbounds_op_reason**, **x_setbounds_op_rounding**,
**x_setbounds_op_exp_path**, **x_setbounds_op_length** and
**x_setbounds_result_reason** ignore structurally impossible cells:
non-exact operations with an inexact failure, round-down paths on other
operations (and vice versa), CSetBoundsImm with lengths above its 12-bit
immediate, and valid results with a failure reason.

#### Arithmetic corners

| Point / cross | Goals |
|---|---|
| **cp_shift_rotate_op**, **cp_shift_rotate_amount**, **cp_shift_operand_form**, **cp_sra_negative_operand** | SLL/SRL/SRA/ROL/ROR; amount 0, 1, 2–30, 31; register or immediate form; SRA of a negative value |
| **x_shift_op_amount**, **x_shift_op_form** | Every operation at every amount class and operand form, excluding immediate ROL (Zbb has none) |
| **cp_div_op_sem**, **cp_divisor_class**, **cp_dividend_class** | DIV/DIVU/REM/REMU; divisor 0, 1, −1, other; dividend 0, INT_MIN, positive, negative |
| **cp_signed_div_overflow**, **cp_signed_div_signs** | INT_MIN ÷ −1 and all four operand sign pairs for signed division |
| **cp_div_completion_path**, **cp_div_complete_op** | Early (divide-by-zero) vs full-iteration completion for each operation |
| **cp_mulh_op_sem**, **cp_mulh_operand_a_class**, **cp_mulh_operand_b_class** | MULH/MULHSU/MULHU with operands 0, 1, positive, negative, INT_MIN, −1 |
| **x_div_op_divisor**, **x_div_op_dividend**, **x_div_op_signs**, **x_div_op_completion**, **x_mulh_operands** | Operation × operand class crosses; sign pairs only for signed operations |
| **x_ind_timing_div** | Data-independent-timing setting × divide operation × divisor class |

#### Mult-pipeline occupancy

**cp_ex2_busy_op** samples the EX2 occupant (**ex2_reg** flags/CHERI op)
when **ex2_valid && !ex2_rdy**: a divide still iterating or WB back-pressure.
**cp_us_op** samples the instruction offered to EX1 when **us_valid_i**.
Both classify as MULT, DIV, SETBOUNDS (all four variants) or CJALR;
CRRL/CRAM are not goals. SETBOUNDS/CJALR bins exist only on CHERIoT
hardware. **x_ex2_busy_us_op** crosses them in the same cycle: an incoming
instruction held behind each kind of busy EX2 occupant (16 goals on CHERIoT
hardware, 4 on RV32-only). Short tests mostly hit DIV-busy; directed
stimulus needs WB back-pressure behind MULT, SETBOUNDS and CJALR.

#### CSR and SCR access coverage

**FC_ISA_CSR** samples each executed, legal CSR instruction once
(**csr_op_en_i && !illegal_csr_insn_o**). **cp_csr_addr** has one bin per
CSR address that **cs_registers** implements for the hardware configuration
(PMP, extra HPM counters, triggers and **MSHWM**/**MSHWMB**/**CDBG_CTRL** are
filtered by **PMPEnable**, **MHPMCounterNum**, **DbgTriggerEn** and
**CHERIoTEn**): 34 addresses on CHERIoT hardware, 31 on RV32-only.
**x_csr_addr_op** crosses it with **read** (CSRRS/CSRRC, rs1 = x0),
**write**, **set** and **clear**; writes to the four read-only machine
information CSRs trap and are ignored (124 goals on CHERIoT hardware, 112
on RV32-only). Runtime legality is not filtered: **MTVEC**/**MEPC** need
**PMODE=0**, **MSHWM*** need CHERI mode, and **DCSR**/**DPC**/**DSCRATCH*** need
debug mode. **x_scr_addr_op** covers all seven CHERI SCRs (MTCC, MTDC,
MSCRATCHC, MEPCC, DEPCC, DSCRATCHC0/1) with read and write (14 goals,
weight 0 on RV32-only hardware). The previous auto-binned **cp_addr**, which
also created goals for unimplemented PMP/HPM addresses, was removed.

Illegal accesses are covered per cause from the **cs_registers** internal
flags, sampled once per executed access: **cp_illegal_csr**
(**illegal_csr**, CSR accesses), **cp_illegal_scr** (**illegal_csr_cheri**,
SCR accesses, weight 0 on RV32-only hardware) and **cp_illegal_csr_priv**
(**illegal_csr_priv**, needs U-mode), each with **read** and **write**
(write/set/clear) bins, plus **cp_illegal_csr_write** for a write to a
read-only CSR. Causes may overlap in one access.

#### Complex-unit FSM transitions

**cg_ma_cmplx.cp_transition** samples **cmplx_fsm_cs** with native
**=>** transition bins: **start_req** (IDLE=>WAIT_RD), **read_abort**
(WAIT_RD=>IDLE), **read_ok** (WAIT_RD=>WRITE), **wr_issued**
(WRITE=>WAIT_WR), **wr_flush** (WRITE=>IDLE, flush only), **wr_done**
(WAIT_WR=>IDLE) and four separate per-state holds. **bad_transition** is an
illegal bin for every other transition, paired with
**AssertCmplxTransition**. The former next-state port **cmplx_fsm_ns** was
removed from the monitor and bind; use a fresh database. **wr_flush** needs a
commit flush landing in the WRITE cycle and may stay a hole in short tests.

#### Forwarding, branch resolution and recovery

The forwarding points in **FC_MA_ISSUE** sample every nonzero source operand
read by a valid issue slot:

| Point | Goals |
|---|---|
| **cp_consumer_slot**, **cp_operand** | IR0/IR1, rs1/rs2 |
| **cp_operand_outcome** | Ready from the register file, reserved but rescued by forwarding, RAW stall, or dependent on IR0 in the same bundle |
| **cp_producer** | For rescued operands: ALU0, ALU1, LSU, MULT, or several sources |
| **cp_consumer_class** | Consuming instruction class |
| **cp_issued** | Whether the consumer issued that cycle |

**x_operand_outcome_issue** (same-bundle outcomes only for IR1) and
**x_fwd_producer_consumer** relate outcome, issue, producer and consumer.

The prediction-resolution points in **FC_MA_ISSUE** sample each issued branch,
JAL or JALR:
slot × kind × predicted taken × actual taken × recovery path (none, ordinary
PC set, alternate-path apply, alternate-path cancel/flush). Jumps never
resolve not-taken. **cp_slot1_suppressed_by_mispredict0** covers IR1 being
held because IR0 mispredicted. The temporal-dependency points in
**FC_MA_ISSUE** cover CHERI instructions stalled or issued while load filtering
and runtime CHERI mode are enabled. Their point weights are zero without
CHERIoT hardware; the cross additionally has zero weight without load filtering.

All 93 issuer points and seven crosses belong to one **cg_ma_issue** instance.
Typed event-kind guards keep cycle sampling (once per rising edge outside
reset) separate from operand, resolution and temporal-dependency samples
(up to four, two and two per edge). No cycle point is resampled by those
event calls. **run_issue_sampling.py** checks simultaneous events, reset,
FSM history, saved-RA tracking and both hardware/load-filter/mode settings;
**--baseline** compares every native point/cross report against a preserved
pre-consolidation source. Other legal-bin counters and applicability are
preserved; only forwarding **pair_2** changes from a legal goal to an illegal
bin. The old four-group weighted average is not the new single-group score.
The negative forwarding sweep checks all 31 pair_2 bins and their paired
assertions in both hardware/runtime modes, including idle cycles, with
reset, between-edge and x0 rejection. Three legal goals per register remain.

In **FC_MA_IF**, **cp_pdt_cand0/1** cover which predictor source (branch,
JAL, JALR) each slot proposes, and **x_cp_pdt_priority_contention** crosses
both candidates with the arbitrated source when both slots predict, ignoring
slot-1 winners.

Some cells in the 5-way branch-recovery cross and the forwarding crosses may
prove unreachable in this pipeline; review zero-hit cells after the first
full campaign and add justified ignore bins rather than leaving them open.

All of these schema changes require recompilation and fresh databases.
Preserve prior reports; do not merge pre-change schemas into the new campaign.
Focused synthetic monitor tests establish binning/sampling behavior only,
not DUT reachability or campaign closure.

## 5. Integration priorities and release evidence

Before sign-off, retain TestRIG comparison results and reproducibility
manifests alongside Kudu coverage reports; align actual
simulation selectors with the configuration plan; and resolve coverage-model
diagnostics and sampling/exclusion reviews.

Maintain a feature-to-test/coverpoint/proof matrix and a reviewed gap list for
reference-model limitations, interrupt/debug/error alignment, temporal safety
and trace completeness. Track SCI's end-to-end formal work and Kudu-specific
integration separately from local assertion proofs. Record platform results
separately from simulation coverage.

The release evidence package should include pinned sources and tools, the
applicability matrix, passing regression and comparison manifests, per-instance
coverage reports and exclusions, formal proof/assumption reports, platform
test results, and disposition of every remaining verification issue.

## 6. Sources and maintenance

Local implementation links above describe the inspected checkout; the source
census is dated and must be regenerated after coverage edits. External links
below identify the source branches and relevant implementation sections
reviewed for this draft. Branch links can change: pin their commits in campaign
manifests.

| Reference | Use in this plan |
|---|---|
| [TestRIG read-from-file branch][testrig] | Overall branch workflow and setup |
| [CHERIoT-Ibex formal README][ibex-formal] | Sail/RTL trace-equivalence approach, tools and stated limitations |
| [CHERIoT-SAFE][safe], [configuration documentation][safe-config], [FPGA build selector][safe-build] | Selectable Ibex/Kudu platform example |
| [SAFE FPGA build notes][safe-fpga] and [simulation notes][safe-sim] | Board, tool, image and clock/UART considerations |

[testrig]: https://github.com/CHERIoT-Platform/TestRIG/tree/dii-read-from-file
[ibex-formal]: https://github.com/microsoft/cheriot-ibex/blob/main/dv/formal/README.md
[safe]: https://github.com/CHERIoT-Platform/cheriot-safe
[safe-config]: https://github.com/CHERIoT-Platform/cheriot-safe/blob/main/README.md#L29-L37
[safe-build]: https://github.com/CHERIoT-Platform/cheriot-safe/blob/main/build/build_arty_a7#L3-L21
[safe-fpga]: https://github.com/CHERIoT-Platform/cheriot-safe/blob/main/build/Readme.md
[safe-sim]: https://github.com/CHERIoT-Platform/cheriot-safe/blob/main/sim/Readme.md
