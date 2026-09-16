# CHERIoT-Kudu design-verification test plan

**Status:** Draft for review. **Baseline:** repository sources inspected on
2026-09-15. Coverage targets and future automation below are proposed sign-off
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

### 2.1 Reference and integration boundary

The requested TestRIG variant is the
[CHERIoT-Platform/TestRIG **dii-read-from-file** branch](https://github.com/CHERIoT-Platform/TestRIG/tree/dii-read-from-file).
Pin a commit of that branch, its submodules and the Sail model for each campaign.
Do not assume commands or protocol details from TestRIG's default branch are
identical.

The selected branch provides a file-based, two-phase preparation/reference
flow. It is not an integrated Kudu/Sail comparison runner:

```text
 QCVEngine --output-dir / retained instruction files
                         |
                 trace_NNN.hex.txt
                         |
          Phase 1: Sail file-fed DII execution
                         |
                  ELF + memory artifacts
                    /               \
      Kudu local ELF replay       Phase 2: Sail ELF execution
                    |               |
     RVFI/text trace + coverage   Sail log + RVFI records
                    \               /
       Explicit architectural comparison and coverage triage
                         |
             Targeted tests / generator refinement
```

The branch-specific sequence is:

| Phase | Source-verified behavior |
|---|---|
| Generate | QCVEngine **--output-dir** runs without sockets or comparison. It writes **trace_NNN.hex.txt**, with one hexadecimal instruction per line and comments. The current writer does not append an EBREAK terminator. |
| Construct an executable | **generate_elfs_from_traces.py** runs Sail with **-f input.hex.txt --elf-output output.elf**. File-fed DII writes/injects buffered instructions at the current PC. The alternative **--phase1_no_sail** path builds structured ELFs directly. |
| Re-execute in the reference model | **run_phase2_sail.py** executes the ELF normally, with verbose trace output, an instruction limit and optional binary RVFI. This phase is Sail-only. |
| Decode reference records | **run_two_phase.sh** decodes binary RVFI into labeled text under **results/**; phase-2 binary files are under **rvfi_bin_phase2/**. |
| Replay and compare Kudu | The local Kudu flow executes matching ELF/memory inputs. A separate comparison step must join its results to the phase-2 Sail reference. |

Representative Sail command shapes, taken from the branch's
[phase-1][testrig-phase1] and [phase-2][testrig-phase2] scripts, are:

```text
<sail> -f <input.hex.txt> --elf-output <output.elf>
<sail> <input.elf> -v --trace-output <sail.log> \
    -l <instruction-limit> --rvfi-output <phase2.rvfi.bin>
```

Use fresh output paths and the branch-compatible Sail build. The main runner
does not request phase-1 RVFI. **Use phase-2 ELF execution as the matching
reference for Kudu ELF replay**, rather than treating phase-1 instruction
injection as equivalent to ordinary fetch. Keep all required memory artifacts
and reject failed or unsuitable image generation before comparison.

The local flow called **DII_SIM** is likewise currently an **ELF-backed memory
replay** testbench, not a live TestRIG socket endpoint. Neither the public
two-phase runner nor the local sweep currently performs the complete
Kudu-versus-Sail comparison automatically. Closing that integration boundary
is part of this plan.

### 2.2 TestRIG-specific format and reproducibility requirements

The [current RVFI decoder][testrig-rvfi] defines **93-byte custom CHERIoT v1
packets**, with five nine-byte data fields carrying payload and capability
tag information. The branch README's 88-byte description differs from that
implementation. Version and validate the producer, binary decoder and Kudu
trace adapter together; do not assume a generic RVFI-v1 packet layout or
compare differently formatted files byte-for-byte.

The phase-2 script can accept a nonempty verbose log even when RVFI is absent
or contains only a halt packet. Batch processing can have partial failures,
and the runner uses lenient RVFI decoding. Therefore require useful
architectural records, checked completion and a successful explicit comparison;
successful generation/decoding is not a verification pass.

The [runner][testrig-runner] notes that QCVEngine ignores its forwarded seed
option. Archive the actual generated instruction files, ELFs and overlays;
the command-line seed alone is not a reproducer. The
[setup script][testrig-setup] can advance submodules with **git pull --ff-only**,
so record resolved commits rather than branch names alone. The corresponding
Sail-RISC-V branch is **cheriot-dii-read-from-file**.

The published Docker quick-test recipe uses **--clean**. Run it only in a
disposable, isolated output workspace, not against an existing test archive.

### 2.3 Local replay sequence

The implementation is
[run_dii_rvfi.py](../run_dii/run_dii_rvfi.py),
[tb_kudu_top.sv](../tb/tb_kudu_top.sv), and
[sparse_mem.cpp](../tb/sparse_mem.cpp).

| Step | Current behavior and planned acceptance check |
|---|---|
| Select inputs | The runner extracts **bin.tar.gz** and selects ELFs listed in **bin/elfs_no_conflict.list**. Record archive hash and selected members. |
| Compile | **--compile** invokes **vcscomp -dii -nowave -cov**. Otherwise the existing simulator is reused; record and verify its build identity. |
| Select mode | The runner uses the CHERIoT-capable **simv** for both modes. **--rv32** adds **+PMODE=0** rather than changing the elaboration. |
| Initialize | The testbench loads **BINDIR/TEST.elf** into sparse memory. Initialization of capability and CSR state is partly forced to match the reference environment; those assumptions must be recorded. |
| Execute | The DUT fetches through the memory model. The runner chooses memory-delay maxima once per invocation and passes **+RVFI_MAX**. |
| Record | Collect **rvfi_kudu_core.log**, **trace_kudu_core.log**, simulator diagnostics and raw coverage. The runner archives per-test **.rvfi/.trace** files in **results.tar.gz**. |
| Compare | Replay matching reference inputs and explicitly compare the intended trace interval. Simulation completion alone is not a differential-test verdict. |
| Accumulate | Merge coverage against the matching design database, retain provenance and review uncovered goals. Preserve failing-test evidence even if the sweep continues. |

[elf2dii.py](../scripts/elf2dii.py) converts ELF load segments into little-endian
16-bit memory records of the form **mem[X,address] -> value**, including
zero-fill by default. [check_dii_inputs.py](../scripts/check_dii_inputs.py)
checks duplicate input addresses. These files describe memory contents; they
are not interchangeable with a binary DII command stream.

Although the testbench constructs a **.dii** pathname, its current active
initialization calls **sparse_mem_init_elf**; the text-memory loader call is
commented out. A test plan or launcher must follow the active implementation,
not infer the input format from the build mode's name.

### 2.4 Kudu testbench organization

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

### 2.5 Comparison, reproducibility and data protection

Use [compare_trace.py](../scripts/compare_trace.py) for supported Kudu/Sail
trace comparisons and the existing clean/diff tools for compatible Ibex
golden traces. Review known equivalence rules rather than editing traces to
make a comparison pass.

The current comparator prints a verdict; it does not reliably communicate
that verdict through a failing process exit code. It also permits a Kudu
trace tail. A sign-off wrapper must check the reported verdict, comparison
extent, reference exhaustion, pending revocations and approved termination
tail. Exception-handler skipping is a scoped bring-up option, not evidence
that exception behavior was verified.

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

| Dimension | Planned coverage |
|---|---|
| Configuration | Supported KuduCfg1/1x/2/3 elaborations; issue width, FIFO/stage bypass, predictor, cache and multiplier variants applicable to the product |
| Architectural mode | CHERI-enabled operation, runtime RV32 operation, and a non-CHERI build; verify that mode-dependent aliases are classified from the instruction's saved state |
| Instruction set | RV32I/M/C and enabled A/B operations, CHERIoT operations and compressed forms, CSRs, legal operands and architecturally specified traps |
| Dependencies | RAW/WAW, forwarding, x0, source/destination aliasing, simultaneous writes, ready/stalled pipeline combinations and both issue slots |
| Control flow | All six branch conditions, signed/unsigned boundaries, taken/not-taken, prediction direction/target errors, JAL/CJALR, flush and recovery |
| Capability behavior | Tags, permissions, bounds and representability, sealing/sentry rules, capability loads/stores, temporal safety and revocation interactions |
| LSU/bus | Alignment and split accesses, byte enables, tags, LR/SC success/failure, AMO sequencing, grant/response timing, outstanding transactions, errors and cancellation |
| Asynchronous/system behavior | Interrupt classes and priority, CSR/trap state, debug entry/return/single-step, reset, fatal errors and recovery |
| Long sequences | Mixed pipelines, persistent pressure, wraparound, repeated faults, application/RTOS and long-running FPGA scenarios |

The matrix is a requirement list, not an assertion that all combinations are
supported. Record applicability and choose risk-based crosses rather than an
unbounded Cartesian product.

**Configuration integration item:** the current simulation testbench selects
KuduCfg2 for selector 2, KuduCfg3 for 3, and KuduCfg1 otherwise. Thus selector
0 does not currently establish a distinct KuduCfg1x simulation, even though
the source checker supports KuduCfg1x. Resolve and record that mapping before
claiming configuration closure.

### 3.2 Feature-to-evidence plan

| Goal | Stimulus and evidence |
|---|---|
| Every enabled instruction/format and meaningful operand class | TestRIG generation plus directed ISA/CHERIoT programs; Sail comparison and retire coverage |
| Correct behavior under microarchitectural pressure | Dependency chains, independently varied instruction/data delays, queue boundaries, pipeline mixtures and recovery; microarchitectural coverage plus architectural comparison |
| CJALR corner cases | rs1 equal/not equal to c1, prediction eligibility versus actual PCC update, immediate/target boundaries, tag/sealing/execute-permission faults, checking bypass modes |
| Accurate memory and atomic behavior | Read/write/SC/AMO/tag scenarios with delayed responses; compare architectural effects and check queued transaction attribution |
| Precise exceptions and control events | Faults in each relevant slot, competing events, older in-flight work, drain/execute/flush sequencing and absence of killed side effects |
| Temporal safety | Revocation/no-revocation, outstanding capability accesses, stalls and tag clearing; explicit reference/environment correspondence |
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
| Functional coverage | 100% of applicable planned legal bins and required crosses, reported per configuration and per instance after reviewed exclusions |
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
| **FC_ISA_INSTR** | Retirement observations; named instruction-encoding bins grouped by ISA/format, register/value classes, capability and memory attributes, control-flow/trap indicators |
| **FC_ISA_SYS** | Architectural CSR, privilege, interrupt, trap and debug state/events |
| **FC_MA_IF** | Fetch/prefetch handshakes, outstanding/discard state, fetch FIFO occupancy and alignment, split instructions, ALT buffering and prediction |
| **FC_MA_ID** | IR storage/handshakes, decode categories and errors, register read/write address crosses, revocation, breakpoints, CJALR source role and prediction/PCC update |
| **FC_MA_ISSUE** | Issue arbitration, hazards, stalls, routing, selected special events, drain/flush and control sequencing |
| **FC_MA_EX** | ALU0/1, mult/div/CHERI and AMO complex-unit behavior; forwarding/WAW/handshakes; branch-unit evaluations in separate IR0/IR1 groups |
| **FC_MA_LSU** | Load/store pipeline, data cache and revocation stage; queues, accesses, capability behavior, cancellation, split accesses and atomic interactions |
| **FC_MA_CMT** | Completion/commit combinations, scoreboard handling, errors, register-write and flush interactions |
| **FC_MA_BUS** | Instruction/data requests, data attributes, actual grant/response delays and metadata, temporal-safety map, interrupt/debug inputs and fatal-error lifecycle |
| **FC_MA_CONTEXT** | Resident instruction classes in IR/ALU/MULT/LSU crossed with current issue or selected special-event phases |

### 4.1 Important organization and sampling details

**Retirement:** ISA coverage follows the tracer's retirement FIFO walk and
separate AMO retirement event. It uses shared **tracer_pkg::instr_trace_t**,
not a private mirror type. Instruction encodings, including compressed forms,
are sampled from the trace; mode-specific classification uses saved decode
information rather than only a live mode pin. Commit-error handling and the
completeness of fault/side-effect reporting require explicit review.

**Execution:** ALU instances retain separate reports. Branch coverage is owned
once through the existing ALU0 monitor and reports **FC_MA_EX.branch.ir0/ir1**.
It samples valid, hazard-free evaluations, not only issued instructions, so
CJALR faults that prevent issue remain observable.

**Context:** six contexts represent IR0, IR1, ALU0, ALU1, MULT and LSU.
The model retains detailed instruction categories while using eight reduced
classes for tractable crosses. MULT observes saved instruction metadata;
ALU keeps minimal category tags because its stage records omit opcodes;
LSU uses the existing WAW FIFO's addresses/occupancy rather than independent
queue control, with AMO context from the complex unit.

Residents are sampled before edge-triggered updates. They cross with actual
issuer strobes, and with selected special events during drain, IR-only
special execution, or commit-flush entry. These are coexistence scenarios,
not proof of producer/consumer dependencies or instruction-specific causality.

**Bus:** both the coverage owner and queued timing helper are now in
**kudu_fcov_bus.sv**. Response metadata is associated with accepted requests.
This is observed transaction timing, not simply coverage of requested
testbench delay settings.

### 4.2 Source census, not achieved coverage

The following snapshot is the output of **count_cov.py** on 2026-09-15:

| Organization | Covergroup types | Coverpoint declarations | Explicit crosses |
|---|---:|---:|---:|
| ISA instructions | 1 | 47 | 0 |
| ISA/system | 1 | 35 | 0 |
| IF | 1 | 60 | 2 |
| ID | 1 | 57 | 16 |
| Issue | 1 | 43 | 0 |
| EX, including branch groups | 4 | 76 | 0 |
| Context | 1 | 8 | 2 |
| LSU | 3 | 76 | 0 |
| Commit | 1 | 27 | 0 |
| Bus | 2 | 39 | 0 |
| **Total** | **16** | **468** | **20** |

The tool also reports **15 bind declarations**, **1,067 normal bin
declarations**, **35 illegal-bin declarations**, and **7 ignore-bin
declarations**. It reports the branch type separately as **cg_ma_branch**;
the table folds it into EX.

These are source declarations, not elaborated instance counts, expanded bin
counts, reachable goals or percentages achieved. Array/wildcard/transition
bins, crosses, generate conditions and repeated instances change the
elaborated model. Obtain actual closure denominators and scores from
configuration-specific VCS/URG reports.

Useful read-only source checks, from **sim/**, are:

```sh
python3 fcov/count_cov.py
python3 fcov/check_binds.py
python3 fcov/check_syntax.py --matrix
python3 fcov/check_syntax.py --matrix --coverage-off
```

Full functional coverage is collected in the VCS flow. The standalone
covergroup-free timing-helper test can use Verilator; that does not establish
Verilator support for this functional coverage model.

## 5. Integration priorities and release evidence

Before sign-off, complete the TestRIG/file-replay/reference adapter contract,
automated comparison verdict checking and manifest capture; align actual
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
| [QCVEngine output mode][testrig-generator] | File-only generation, without DUT comparison |
| [Phase-1 ELF generation][testrig-phase1] and [Sail file-DII implementation][sail-file-dii] | Instruction-file input versus normal ELF execution |
| [Phase-2 Sail runner][testrig-phase2] and [two-phase driver][testrig-runner] | Reference execution, artifacts and acceptance limitations |
| [RVFI decoder][testrig-rvfi] | Actual custom binary record format |
| [Submodule setup][testrig-setup] | Revision/reproducibility requirements |
| [CHERIoT-Ibex formal README][ibex-formal] | Sail/RTL trace-equivalence approach, tools and stated limitations |
| [CHERIoT-SAFE][safe], [configuration documentation][safe-config], [FPGA build selector][safe-build] | Selectable Ibex/Kudu platform example |
| [SAFE FPGA build notes][safe-fpga] and [simulation notes][safe-sim] | Board, tool, image and clock/UART considerations |

[testrig]: https://github.com/CHERIoT-Platform/TestRIG/tree/dii-read-from-file
[testrig-generator]: https://github.com/CHERIoT-Platform/TestRIG/blob/dii-read-from-file/vengines/QuickCheckVEngine/src/QuickCheckVEngine/Main.hs#L502-L529
[testrig-phase1]: https://github.com/CHERIoT-Platform/TestRIG/blob/dii-read-from-file/utils/scripts/generate_elfs_from_traces.py#L63-L71
[sail-file-dii]: https://github.com/CHERIoT-Platform/sail-riscv/blob/cheriot-dii-read-from-file/c_emulator/riscv_sim.c#L1334-L1353
[testrig-phase2]: https://github.com/CHERIoT-Platform/TestRIG/blob/dii-read-from-file/utils/scripts/run_phase2_sail.py
[testrig-runner]: https://github.com/CHERIoT-Platform/TestRIG/blob/dii-read-from-file/run_two_phase.sh
[testrig-rvfi]: https://github.com/CHERIoT-Platform/TestRIG/blob/dii-read-from-file/utils/scripts/rvfi_to_text.py#L8-L40
[testrig-setup]: https://github.com/CHERIoT-Platform/TestRIG/blob/dii-read-from-file/scripts/setup_submodules.sh
[ibex-formal]: https://github.com/microsoft/cheriot-ibex/blob/main/dv/formal/README.md
[safe]: https://github.com/CHERIoT-Platform/cheriot-safe
[safe-config]: https://github.com/CHERIoT-Platform/cheriot-safe/blob/main/README.md#L29-L37
[safe-build]: https://github.com/CHERIoT-Platform/cheriot-safe/blob/main/build/build_arty_a7#L3-L21
[safe-fpga]: https://github.com/CHERIoT-Platform/cheriot-safe/blob/main/build/Readme.md
[safe-sim]: https://github.com/CHERIoT-Platform/cheriot-safe/blob/main/sim/Readme.md
