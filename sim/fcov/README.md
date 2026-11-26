# cheriot-kudu functional coverage model

Bind-based SystemVerilog coverage for Kudu. Historical comments refer to
`doc/functional_coverage_plan.md`, which is not present in this checkout.
This README describes the current implementation.

Architectural and microarchitectural coverage, plus instruction-context crosses:

| Group | Layer | Covergroup(s) | Bind target(s) |
|---|---|---|---|
| `FC_ISA_INSTR` | 1 | `cg_isa_instr` | `tracer` (retire trace) |
| `FC_ISA_OPERANDS` | 1 | `cg_isa_operands` | `tracer` (same retire records) |
| `FC_ISA_CSR`   | 1 | `cg_isa_csr` | `cs_registers` |
| `FC_MA_IF`     | 2 | `cg_ma_if` | `if_stage` (+ prefetch/predictor signals) |
| `FC_MA_ID`     | 2 | `cg_ma_id`, `cg_ir_decoder` x2 | `ir_stage` (+ both `ir_decoder` instances) |
| `FC_MA_ISSUE`  | 2 | `cg_ma_issue` | `issuer` |
| `FC_MA_EX`     | 2 | `cg_ma_alu` x2, `cg_ma_mult`, `cg_ma_cmplx`, **cg_ma_branch** x2 | ALU0/1, **branch_unit**, `mult_pipeline`, `cmplx_unit` |
| `FC_MA_LSU`    | 2 | `cg_ma_lsu`, `cg_ma_dcache`, `cg_ma_trvk` | `ls_pipeline`, `dcache`, `cheri_trvk_stage` |
| `FC_MA_CMT`    | 2 | `cg_ma_cmt` | `committer` |
| `FC_MA_TOP`    | 2 | `cg_ma_top`: scoreboard FIFO occupancy, bus and fatal-error lifecycle | `kudu_top` |
| `FC_MA_CONTEXT` | 2 | `cg_frontend`, `cg_execution` x6 | `kudu_top`: S0, IR0/1, ALU WB, MULT EX2/WB, LSU delay/request |

Run `python sim/fcov/count_cov.py` for the current source census. It counts
types, coverpoints, explicit crosses and bin declarations separately; it does
not claim to count elaborated instances or expand array/automatic bins.

A stage can have several covergroups where it spans multiple RTL modules or
has different sampling events:

* `FC_MA_EX` has one group per execution pipeline. `alu_pipeline0_i` and
  `alu_pipeline1_i` are identical, so they share a single parameterised
  covergroup type instantiated twice; `option.per_instance` reports them
  separately as `FC_MA_EX.alu0` and `FC_MA_EX.alu1`.
* `FC_MA_LSU` has one group for the LS pipeline itself and one each for the
  data cache and the temporal-safety revocation stage, which are separate
  blocks inside the stage.

Section banners group related coverpoints. Bind ports bring the relevant
signals into each coverage module; covergroups do not infer cross-stage
transaction identity from unrelated same-cycle signals.

All binds live in `kudu_fcov_bind.sv`. Instruction-context and submodule
coverage also use direct hierarchical RTL references, checked by full-design elaboration.
The syntax checker permits pyslang's upward-name warnings, but still fails on
unresolved paths, other coverage diagnostics, or any elaboration error.
The revocation monitor definition and its bind both require **CHERIoT**.
Without this matching guard, an RV32 compile with automatic top discovery can
elaborate the unbound monitor as a root and fail its upward RTL references.

## Building

### Operating modes and two hardware reports

The hardware/runtime operating mode is **orthogonal to kudu_cfg**:

| Report domain | Operating mode | CHERIoTEn | cheri_pmode_i |
|---|---|---:|---:|
| RV32 | RV32-only configuration | 0 | Ignored (normally 0) |
| CHERIoT | CHERIoT configuration, RV32-compatible mode | 1 | 0 |
| CHERIoT | CHERIoT configuration, CHERIoT mode | 1 | 1 |

CHERIoT-only coverpoints and crosses sample only in the third row.
Shared integer/control/trap coverage continues in all applicable rows.
Mixed points retain their common observations but qualify CHERIoT-only
values. Mode-identification points such as **cp_operating_mode** are
intentionally active in every mode. Instruction-specific coverage also uses
saved decode/transaction information so a delayed event cannot acquire a
CHERIoT interpretation merely from the current bus width or mode pin.

There are **two reports**, initially for **KuduCfg1** and eventually for every
supported pipeline configuration: RV32-only hardware (**CHERIoTEn=0**) and
CHERIoT-capable hardware (**CHERIoTEn=1**, the union of PMODE=0 and PMODE=1).
Use fixed-mode runs and merge matching **{kudu_cfg, CHERIoTEn, coverage schema}**
results, including both runtime modes within the CHERIoT report. Never merge
the two hardware elaborations. Run mode-switch testing separately. Combining
reports does not permit CHERI-only bins to sample RV32 runtime observations.
Runtime **iff** conditions stop sampling but do not remove elaborated bins
or automatically partition a database. CHERIoT-only goals are not applicable
in the RV32 hardware report; they remain required in the combined CHERIoT
report. Retain raw and applicability-adjusted scores.

**cp_operating_mode** retains the three named source bins but statically ignores
the other hardware's values: RV32 hardware has only **rv32_only** as a goal;
CHERIoT hardware has **rv32_compatible** and **cheriot**. The TOP/LSU **cp_pmode**
and ID **cp_cheri_pmode** points sample both runtime values on CHERIoT hardware.
On RV32-only hardware they do not sample and have zero instance weight because
the mode pin is ignored. Their automatic bins can still appear in raw listings.
Recompile and start fresh databases for this applicability/schema change.

The regression and DII runners partition both raw and accumulated coverage
by hardware build, not runtime mode:

| Runner | CHERIoT hardware database | RV32-only hardware database |
|---|---|---|
| **run_dii/run_dii_rvfi.py** | **cov_kudu_cheriot.vdb** | **cov_kudu_rv32.vdb** |
| **run/run_cov_regression.py** | **temp_cov_regression/cov_kudu_regr_cheriot.vdb** | **temp_cov_regression/cov_kudu_regr_rv32.vdb** |

DII **--build cheriot|rv32** defaults to **cheriot**. The existing **--rv32**
still means **+PMODE=0** on CHERIoT-capable **simv**; without it the default
is **simv +PMODE=1**. **--build rv32** selects **simv32 +PMODE=0**.
Both runtime modes on **simv** accumulate into the CHERIoT hardware database.

The regression **--build all|cheriot|rv32** defaults to **all**. RV32 CoreMark
and RISC-V tests run with PMODE=0 in both hardware builds when **all** is selected;
CHERIoT/debug tests run only on CHERIoT hardware, with PMODE=1. Test labels and
artifact paths distinguish hardware builds so the duplicated RV32 tests do not
overwrite each other. Both runners pass **+PMODE** explicitly. Their **vcscomp**
scripts compile both binaries. DII's **--compile** remains optional; the
regression **always recompiles once before actual runs**, even with **--no_cov**.
Its **--compile** flag is retained as a compatibility no-op, while **--conf**
always applies. **--list** never compiles or creates output directories.
Each build uses its own compile-time design base (**simv.vdb** or **simv32.vdb**).
The regression accepts **--design_vdb** only with a single selected build,
preventing one override from mixing the two elaborations. An override must match
the newly compiled hardware/schema and contain design data only, not old runtime
test records; relative override paths resolve from **sim/run**.

Run the regression from **sim/run** through **submit -i**:

```
submit -i ./run_cov_regression.py --cov_report
```

The regression's default output base is **sim/run/temp_cov_regression/**:

```
temp_cov_regression/
  build_<unique-id>/         # new each invocation; never reused or cleaned
    simv, simv32             # CHERIoT and RV32 executables (+ .daidir)
    simv.vdb, simv32.vdb     # fresh compile-time coverage definitions
    csrc/, csrc32/           # separate compiler scratch
    compile_cheriot.log, compile_rv32.log
  cov_kudu_regr_cheriot.vdb, cov_kudu_regr_rv32.vdb
  cov_temp/                 # raw per-invocation databases and merge staging
  urgReport_cheriot/, urgReport_rv32/
  bin                       # symlink to sim/run/bin
  sim.<build>.<test>.<variant>.log
```

**--work_dir** relocates this entire default output base (relative to **sim/run**
or absolute), not just simulation logs. The runner invokes **vcscomp** from its
own directory with **-cov -nowave -outdir=<fresh-build-directory>**. This option
resolves RTL, verification, DesignWare, file-list and coverage-hierarchy paths
before changing the compiler's working directory, so implicit VCS output does
not leak into **sim/run**. Direct **vcscomp** calls without **-outdir** retain their
existing behavior, including DII. Fresh build directories prevent old runtime
records or stale coverage definitions from contaminating the initial merge;
previous build directories and old **sim/run** databases are not reused.

**--cov_dir** is now a basename: **--cov_dir results/campaign.vdb** produces
**results/campaign_cheriot.vdb** and/or **results/campaign_rv32.vdb**.
An explicit relative **--cov_dir** remains relative to the runner's directory,
independent of **--work_dir**. Only builds selected for the invocation are
updated. **--cov_report** writes **urgReport_cheriot/** and/or
**urgReport_rv32/** under the regression's **--work_dir**, or in DII's runner
directory. **--keep_run_cov** retains build-specific raw databases; a raw
database name collision is an error rather than permission to delete it.
If a merge fails, its raw data is retained and other selected builds are
still merged.

Existing unsuffixed and **_pmode0/_pmode1** databases are left untouched:
they are not migrated or used as merge bases. **cp_operating_mode** does not
partition historical data. Continue to use different basenames for different
pipeline configurations/build schemas and apply hardware-specific exclusions.
**Regression coverage starts clean on every coverage-enabled invocation.** After
compilation and preflight succeed, and before the first simulation, the runner
deletes only the selected **--cov_dir** hardware outputs. Every merge uses the
current invocation's raw data and matching fresh design base (or **--design_vdb**
override), never the previous result. Unselected hardware outputs, old raw
databases, old build directories and DII databases remain untouched. **--list**
is read-only; **--no_cov** does not reset coverage. Compilation/preflight failure
preserves previous results. Once reset succeeds, failed simulations still merge
their partial coverage; merge failure retains raw data, not the deleted previous
result.

Regression reset targets, including custom **--cov_dir** paths, must stay inside
**sim/** and must not overlap design inputs, DII databases, or enclosing working
directories. Existing targets must be recognizable VCS database directories
(**snps/coverage/db/testdata/**), not design-only databases; symlink targets,
parents, or database contents are rejected.
Unsafe paths and deletion failures stop the run with an explicit error before
simulation. Outside-**sim/** coverage outputs are rejected rather than implicitly
authorizing deletion. No old raw/build directory sweep is performed.

DII retains its accumulation behavior: after RTL, coverage schema or configuration
changes, select a fresh **--cov_dir** instead of merging into an incompatible
campaign. Raw data is removed only after
a successful merge unless **--keep_run_cov** is supplied; fresh compile directories
remain available for diagnosis. Simulation logs and reports in a reused output
base retain their existing overwrite behavior.

The standard testbench currently maps pipeline selectors 2/3 to KuduCfg2/3
and other selectors to KuduCfg1. The default selector 1 matches the current
KuduCfg1 campaign. A future KuduCfg1x campaign needs an explicit simulation
selection; selector 0 does not select KuduCfg1x.

The standalone issuer and top fixtures accept **+mode_coverage**
and **+PMODE=0/1**, and expose a **CHERIoTEn** parameter. They deliberately
drive CHERI-looking observations in inactive modes: CHERI bins must remain
unhit while shared coverage continues. Match the **CHERIoT** compile define
to the hardware parameter so the shared package's capability widths match
the elaboration. The top fixture's **+request_mode** case accepts a request
in RV32 mode and returns it in CHERIoT mode; it must not count a CHERI
response tag. Default fixture scenarios remain available.

### Compilation

Add the file list after the RTL and testbench:

```
-f sim/fcov/kudu_fcov.f
```

`sim/run/vcscomp -cov` adds this list. `kudu_fcov_bind.sv` must be compiled last;
shared helpers precede their users.

`+define+KUDU_FCOV_OFF` disables the coverage modules and their binds, including
their assertions. Merely disabling coverage collection is different: the
compiled monitors and assertions remain active.

**Verilator is not supported** — it does not implement covergroups. The
Verilator file list is deliberately left unchanged.

`FC_ISA_INSTR` requires `+define+RVFI` because it binds to `tracer`, which is
`` `ifdef RVFI ``-gated. `kudu.vcs.f` already defines it.

### Configuration-dependent bins

Use a filtered array over the applicable value set rather than separate named
bins whose parameter-only filters can leave them empty. VCS warns about empty
named bins both during compilation and covergroup construction. Adding an
`item` comparison alone does not eliminate those empty-bin warnings.

ALU coverage targets **SingleStage=1**. The EX2-only **cp_ex2**,
**cp_ex2_waw_match**, **cp_fwd_rd_x0**, and EX2/WB **cp_full** points are
removed rather than retained with empty bins. **cp_fwd** samples only
**wb_fwd_valid_q**, with **source[]** bins 0 and 1; **cp_flush_busy** samples
**flush_i && wb_valid**. WB handshakes and WAW coverage remain, as does the
saved-category tracking used by instruction-context coverage. MULT's EX2
coverage is unchanged. These ALU points no longer cause empty-bin warnings.

ALU **cp_op_a_sel** has explicit **reg_a**, **currpc**, and **imm** bins for
**OP_A_REG_A**, **OP_A_CURRPC**, and **OP_A_IMM**. It has no **OP_A_FWD** bin.
ALU **cp_out_we** ignores **0**; only valid outputs with write enable **1**
contribute to its coverage.

For **AUIPCC**, each ALU instance has seven **cp_auipcc_pcc_*** points over
the inherited PCC: tag, reserved bit, compressed permissions, object type,
compressed exponent, base mantissa and top mantissa. They use the same
subfield bins as the architectural capability-source points, except that the
encodings that cannot reach the ALU are illegal: **59 goals per ALU**, with
no additional crosses.

**pcc_cap_i** is converted through
**pcc2fullcap_lite(pcc_cap_i, instr_i.pc)**, explicit **reg_cap_t** extraction,
then **reg2mcap()**. This mirrors the ALU's inherited source, supplies the
instruction PC as the cursor, and preserves its tag; it does not reinterpret
PCC bits as **mem_cap_t** or introduce the extra representability tag clearing
of **pcc2regcap()**.

Sampling requires **CHERIoTEn && cheri_pmode_i && us_valid_i &&
alupl_rdy_o && !flush_i && instr_i.cheri_op.auipcc**, and the tag,
reserved, permission, otype and exponent points also require
**!debug_mode_i**. Outside debug mode an untagged, sealed or non-executable
PCC is an issue-time trap (ir_decoder.sv:583-584), so only a tagged,
unsealed, executable-format PCC (cperms 0x08-0x0f, 0x28-0x2f) reaches the
ALU. A tagged capability also never has the reserved bit set or an exponent
above 24 (cexp 1-6). Debug mode skips the PCC check, so it is excluded. These are execution
acceptance observations, not retired operands or results. RV32 hardware
gives the points zero weight, and runtime PMODE=0 does not sample them.
AUIPCC still has no architectural CS1 operand in **cg_isa_operands**.
The native **run_ex_semantics.py** regression checks both ALU instances,
the conversion and acceptance/mode/reset/flush guards. It drives all 64 raw
encodings in debug mode (only base/top sample) and 64 legal encodings in
normal mode.

Branch **cp_branch_target_match** is removed from both IR slots because the
coverage campaign uses **ChkBranchJALAddr=0**. Its empty-bin filters and the
resulting VCS warnings are gone; other branch points remain unchanged.

IF **cp_unaligned0** samples only valid 32-bit slot-0 instructions: **split**
means PC offset 6 within a 64-bit fetch word, and **whole** covers the other
offsets. **x_cp_comp_align** excludes compressed slot-0 combinations, leaving
four goals: slot-1 compressed/uncompressed crossed with slot-0 split/whole.
Both slots must be valid to sample the cross; standalone split coverage still
samples when only slot 0 is valid.

This cleanup renames some ID, ALU/MULT and context bins without changing the
applicable value sets or context cross combinations. Use a fresh database;
do not merge against older bin names. No warning suppression flags were added.
The TRVK bind is guarded by the **CHERIoT** build define, matching the
testbench and syntax checker's **CHERIoTEn** selection. **kudu_top** also
derives **LoadFiltEn** from that parameter, so non-CHERI builds have no TRVK
instance and omit its bind. Runtime **PMODE=0** does not remove this bind
from a CHERI-capable build. Custom testbenches using this file list must keep
the build define consistent with the DUT's CHERI configuration.

### CSR coverage source

**kudu_fcov_csr.sv** owns **kudu_fcov_csr**, bound as **u_fcov_csr** to
**cs_registers**, with covergroup **cg_isa_csr** reported as **FC_ISA_CSR**.
It was split from **kudu_fcov_isa.sv** and renamed from the former **sys**
names without changing ports, coverpoints, bins or sampling. The ISA file now
contains only the instruction coverage module. The shared coverage file list
includes both sources before the binds.

The rename changes coverage hierarchy/report names; use a fresh database
rather than merging into a database with the old names.

**CSR/SCR access coverage.** **cp_csr_addr** × **cp_csr_op**
(**x_csr_addr_op**) and **cp_scr_addr** × **cp_scr_op** (**x_scr_addr_op**)
sample once per legal executed access (**csr_op_en_i** and not
**illegal_csr_insn_o**). The address bins come from
**fcov_csr_implemented()**, which mirrors the read mux in
**rtl/cs_registers.sv** and the bound parameters **CHERIoTEn**,
**DbgTriggerEn**, **PMPEnable** and **MHPMCounterNum**; update it when CSRs are
added. Read-only machine-information CSRs have read goals only. SCR goals are
read/write (CSpecialRW has no set/clear) and have weight 0 on RV32-only
hardware. These replace the former auto-binned **cp_addr**; use a fresh
database.

**Illegal CSR/SCR causes.** The internal **illegal_csr**,
**illegal_csr_cheri**, **illegal_csr_priv** and **illegal_csr_write** flags
are monitor ports connected by **.\***. **cp_illegal_csr**,
**cp_illegal_scr** and **cp_illegal_csr_priv** each have read/write bins
(write includes set/clear); **cp_illegal_csr_write** has one hit bin. They
sample on every executed access (**csr_op_en_i && csr_access_i**), with the
CSR causes qualified by **!csr_cheri_i** and the SCR cause by
**csr_cheri_i**, matching **illegal_csr_addr** in **cs_registers**.

## Retirement tap and saved decode metadata

The ISA groups mirror the tracer's output paths. Without temporal safety,
they consume `instr_trace_fifo[rd_ptr .. rd_ptr_nxt)`, finalized through
`fill_cmt_info()`. With temporal safety, they instead consume **final_fifo**,
waiting for each successful CLC's revocation response and applying its
final tag clear. A second mode sideband preserves instruction-associated mode
through this queue. AMOs retain the tracer's separate completion path.

Instruction bins match the original `t.rvfi.insn`, including compressed forms.
Mode-dependent aliases must also use the decode metadata saved with that
instruction; a CHERIoT-capable build (`MemW == 65`) alone does not establish
which interpretation was executed. Do not use a live mode pin to classify
an older queued instruction.

Instruction coverpoints are grouped by extension and encoding format:
`cp_rv32i_{r,i,s,sb,u,uj}_type`, `cp_rv32m_r_type`, `cp_rv32a_r_type`,
`cp_rv32b_{r,i}_type`, and `cp_cheriot_{r,i,s,u}_type`. Compressed instructions
use their CR/CI/CSS/CIW/CL/CS/CA/CB/CJ formats under `cp_rv32c_*_type` and
`cp_cheriot_*_type`. CSR instructions remain separate in `cp_rv32i_csr` and
`cp_cscrrw`; architectural CSR-state coverage is unchanged.
Each instruction has a named bin within its format coverpoint. Compressed
forms no longer fill a 32-bit instruction's bin. This changes the coverage
schema and weighting: use a new coverage database after recompiling rather
than merging these coverpoints into a database from the previous layout.

All **30 instruction-encoding coverpoints**, including CSR/SCR instructions,
are crossed with **cp_cheri_active** in **x_*_pmode**. The mode axis uses the
instruction's saved CHERI-active value at tracer enqueue (including the AMO
sideband), not the live retirement pin or RVFI privilege **cp_mode**.
CHERI-only points require CHERIoT hardware and saved mode/decode provenance;
a later change of the live mode pin does not discard their retirement.
The helper mode point has zero weight; the crosses contribute to coverage.
Shared instructions require separate hits in both runtime modes within the
combined CHERIoT hardware report. CHERI instructions require only mode 1;
AUIPC, C.ADDI4SPN and C.ADDI16SP require only mode 0 because their mode-1
encodings are CHERI aliases. These impossible combinations are statically
ignored, not merely sampling-gated. RV32-only hardware constructs only the
mode-0 axis and gives CHERI-only crosses zero weight. Interrupt-only records
do not fill instruction-encoding points or their crosses.

**FC_ISA_OPERANDS** replaces the four unqualified source-register/value
points with a separate instruction identity and operand axes. Its **165 named
instruction identities** retain compressed forms and CHERI mode aliases.
The encoding-set checker checks these identities against the original named
instruction bins. All operand crosses have **at most four axes**.
Only **x_instruction_pmode** includes the mode axis; the remaining goals
combine the reachable values across supported modes. There is still one
**cg_isa_operands**. Its family-qualified crosses replace the generic
operand crosses, partitioned into **arithmetic**, **muldiv**, **bitmanip**,
**control** (branches/jumps), **memory**, **atomic**, **system** (including
CSR), and **cheri** (including compressed CHERI forms and SCR operations).
Compressed RV32 instructions stay with their semantic family, not in a
separate compressed category. `operand_family()` classifies the existing
instruction identities; operand-role helpers further remove unused sources
and fields within each family.

| Axes / purpose | Model |
|---|---|
| Instruction, saved mode | One two-way cross; impossible mode aliases are excluded. |
| Instruction, integer source address, source data | Separate RS1 and RS2 crosses; each architectural register has a bin. Data classes are zero, one, minus one, signed minimum/maximum, other positive and other negative. Capability cursors never sample these classes. CHERI scalar RS2 inputs also cross the actual CS1 tag. |
| Instruction, both source addresses or both source data classes | Only instructions with two actual source operands contribute goals. |
| Instruction, integer operand bit length | Separate RS1/RS2 points for unsigned lengths 0--32, including CRRL/CRAM length inputs. |
| Instruction, immediate class; optionally one source data axis | Signed/unsigned and compressed-format-specific extrema, zero, one, minus one, other positive and other negative values. |
| Instruction, capability source address, CS1 tag | Separate actual CS1/CS2 register addresses; CS1=c0 cannot have tag 1. |
| Instruction, CS1 field, CS1 tag | Reserved bit, permission category, object type, encoded exponent, and base/top mantissa boundary classes. The CS1 address/tag cross already covers its tag marginal. |
| Instruction, matching CS1/CS2 fields, CS1 tag | Tag, reserved, permission category, object type, exponent, base and top are paired with the same field of the other source. Includes CSC and its compressed forms, CSEAL, CUNSEAL, CSETEQX, CSUB and CTESTSUBSET. |
| Instruction, CS1 field, integer RS2 class or size, CS1 tag | Every CS1 subfield is crossed with the seven scalar data classes and, separately, unsigned bit lengths 0--32. Includes CHERI scalar-operand instructions and CHERI-mode integer stores/atomics. |
| Instruction, source tag, CD tag, CS1 tag | CD coverage retains only **cp_cd_tag** and tag-propagation goals. CS1 tag is not duplicated when already an axis. |
| Instruction, CD tag without CS1 | Only source-free link/PCC results and read-only CSPECIALRW. |

The generator adds illegal bins for tagged encodings that cannot exist:
reserved bit set, and CEXP 1--6 (exponent above the root's 24). It also marks
an untagged link capability from a capability-mode jump as illegal. Each is
paired with a simulation-only assertion in **kudu_fcov_isa.sv**, and
**isa_operand_reference.py** removes those bins from the expected goals.

CHERI-family crosses include **cp_cs1_tag** wherever CS1 is actually used.
CRRL/CRAM retain untagged scalar RS1 crosses, and AUIPCC has a separate
source-free immediate cross; neither invents a CS1 operand. Read-only
CSPECIALRW retains destination goals but no source goals. Bounds lengths,
address/permission operands and CINCADDR offsets remain genuine scalar RS2
values, crossed with each source-capability subfield. For ordinary RV32 memory,
atomic and indirect-control mnemonics, saved CHERI mode changes the address
source from integer to capability: scalar crosses sample only their integer
interpretation, while capability-field crosses sample the CHERI interpretation.
Runtime guards and static goal filters both enforce these distinctions.

The native operand regression checks every elaborated cross denominator
against an independent architectural oracle and prints per-family totals
for both hardware builds. These are expanded goals, not source declarations.

| Family | Crosses | RV32-only goals | CHERIoT-capable goals |
|---|---:|---:|---:|
| Arithmetic | 8 | 22,465 | 22,465 |
| Multiply/divide | 6 | 12,600 | 12,600 |
| Bit manipulation | 8 | 33,348 | 33,348 |
| Branch/control | 19 | 10,980 | 11,533 |
| Memory | 31 | 7,505 | 34,909 |
| Atomic | 28 | 16,001 | 68,502 |
| System/CSR | 3 | 765 | 765 |
| CHERI | 45 | 0 | 69,442 |
| Instruction/saved mode | 1 | 128 | 290 |
| **Total** | **149** | **103,792** | **253,854** |

**Permission crosses.** All eleven operand crosses formerly using raw
**cperms** now use six categories from **cheri_pkg::expand_perms**' encoding:
**memory-capability** (low five bits 24--31), **load-capability** (20--23),
**store-capability** (16), **data-only** (17--19), **execute** (8--15), and
**sealing** (0--7). Bit 5 is **Global**, not another category. CS1/CS2
permission-category pairs have 36 combinations, not 4,096. Every non-target
category remains a separate goal; none is silently ignored or labelled an
architectural error. In particular, execute capabilities also grant Load and
Load/Store-Capability, so they can be valid load authorities.

Ten focused crosses retain operation-relevant detail without multiplying it
by scalar data/size axes:

| Focus | Goals per instruction, including source tags |
|---|---:|
| Integer/capability loads and stores, LR/SC/AMO: all 16 memory-category encodings, one execute bin and one sealing bin; Global folded | 36 |
| Indirect control: all eight execute variants, one bin for each other category | 26 |
| CSEAL/CUNSEAL authority in CS2: all eight sealing variants, one bin for each other category, both source tags | 52 |
| CGETPERM: each of the 12 expanded permission bits absent/present | 48 |
| CANDPERM: each expanded permission bit crossed with its corresponding scalar-mask bit | 96 |
| CTESTSUBSET/CSETEQUAL: equal, CS2 proper subset, CS1 proper subset, or incomparable expanded permission sets, including Global | 16 |
| CSC and compressed forms: reachable Store/Load-Store-Capability/Store-Local combinations against stored-capability Global, both source tags | 40 |
| CUNSEAL: both source Global bits and both source tags | 16 |

Bit goals intentionally overlap: CGETPERM and CANDPERM contribute one hit
per permission bit, not one hit per raw encoding. Other focused crosses
contribute one hit per observation. Invalid, interrupt-only and issue-trap
records do not contribute; execute faults retain captured source coverage.
These changes require fresh databases, not merges into the old raw-value schema.

Source-use and register restrictions remove impossible goals **statically**,
not just through sampling guards: unary operations and LR have no RS2 goals;
CSR-immediate forms have no RS1 register goals; compressed prime/fixed/nonzero
register restrictions, CGP at register 3, CHERI's 16-register bank, and the
zero register's zero cursor are respected. C.MV reads only RS2. CSPECIALRW
has an optional register operand, not an RS2 operand for its SCR selector;
its read-only register-zero form creates CD hits but no source-data hits. CRRL/CRAM and scalar length/offset/mask/high-word operands are integer data,
not capability metadata.
In CHERI mode, ordinary memory/address-control operations also cover their
capability address source.

CD tag coverage requires a capability-producing instruction in CHERI
mode, a nonzero destination register and no trap. It does **not** interpret
integer results from CGETTAG, other CGET operations, CRRL/CRAM, CSUB,
CTESTSUBSET or CSETEQUAL as capabilities. Ordinary integer ALU results and
stores likewise have no CD capability goals. CHERI-mode link instructions
do produce capability destinations.

Tag-propagation exclusions retain CMOVE's tag preservation, prohibit tag
creation from untagged inputs for capability transformations, and restrict
CCLEARTAG/CSETHIGH to untagged results. Other CD subfield points and their
crosses are removed. CS1/CS2 are independent inputs, so their matching-field
crosses do not impose source-to-destination copying restrictions; unequal
permissions, types and bounds are intentional goals, including faulting
execute-stage observations.

RVFI capability values are **mem_cap_t**, produced by **reg2mcap()**. The model
does not reinterpret them as the differently packed internal register
capability. Bounds points describe raw encoded mantissas/exponents, not
decoded absolute bounds or representability. Immediates are reconstructed
from **t.ir_dec.insn**, the saved expanded instruction; CSETBOUNDSIMM is
unsigned, CSR zimm and shift amounts are five-bit unsigned, and AUIPCC/AUICGP
use Kudu's signed C20 displacement with an 11-bit shift.

The approach was compared with
[cheriot-ibex's coverage interface](https://github.com/microsoft/cheriot-ibex/blob/531ca2ec439fe3fa89bd6f60ae8f256bc0b9b241/dv/cheriot/fcov/core_ibex_fcov_if.sv).
That reference samples execution, not retirement, and includes crosses wider
than four axes; neither behavior is copied. Kudu samples valid retirement
records, including execute-stage faults whose source operands were captured,
but excludes interrupt-only packets and issue-side traps from source/immediate
goals. The exception is an issue-side CJALR fault (tag, seal or execute
violation): its CS1 is the operand the fault was computed from, so it fills
the control-family CS1 crosses (address/tag, permission, otype and bounds
fields, target permissions), but not CD or immediate goals.
**AssertIsaJumpFaultCause** (simulation) checks that the traced CS1 explains
the fault. Recognized issue-side traps still fill the instruction/mode cross.
The tap calls the tracer's **fill_cmt_info()**, retains older/faulting records
in a commit-error cycle, and handles both normal AMO completion and first-phase
AMO errors. The final FIFO path prevents pre-revocation CLC tags from filling
CD coverage. Helper operand points have zero weight; their qualified crosses
carry the goals. Use fresh coverage databases after recompiling.

**Operand regression and maintenance.** `generate_isa_operand_crosses.py`
checks the generated family-cross and permission-point block; `--write` regenerates it
after a schema change. Eligibility and metadata transformations remain in
the SystemVerilog helpers. `check_isa_encoding_sets.py --classifiers` checks
the generated schema and encoding identities as well as the shared classifiers.
`run_isa_operands.py` is the native VCS/URG regression:

```
cd sim
source /etc/profile.d/modules.sh
source run_dii/load_module_vcs
PYTHONDONTWRITEBYTECODE=1 python3 fcov/run_isa_operands.py
python3 fcov/run_isa_operands.py --check temp/isa_operands_families_<run>
```

It creates an exclusive run directory and invokes every licensed tool through
`submit -i`. Both hardware builds run exhaustive compressed classification,
32-bit identity/immediate checks, directed scalar/capability-role cases with
both saved modes and both CS1 tags, unused-source and scalar-result exclusions,
tag-transform checks, commit-error/AMO retirement, and final CLC revocation.
An independent architectural Python oracle checks every native family-cross
denominator and directed bin counts. The source-pair vectors cover all eligible
instructions, matching CS1/CS2 fields, scalar RS2 classes/bit lengths, both
saved modes and source tags, execute/issue traps, interrupts and invalid packets.
They verify that removed CD metadata points are absent and that source-pair
counts come from the correct operands. These are monitor regressions, not proof
that the DUT has closed all coverage goals. Keep their databases separate from
campaign databases.

The **permissions** scenario additionally sweeps all 64 input encodings and
all 64-by-64 capability-source pairs, both saved modes and source tags.
Zero/all-one scalar masks exercise every per-bit CANDPERM combination.
The checker verifies every focused denominator and exact bin count, including
non-target categories, Global-sensitive cases and sampling exclusions.

Review changes to that loop together with the coverage tap. Width/PC/queue
checks can catch structural or accounting mistakes, but do not constitute an
independent architectural retire-order oracle.

`instr_trace_t` is shared from `tracer_pkg`; the coverage tap casts the packed
bind input using that shared type and checks its width. There is no private
mirror struct to maintain. Width agreement does not validate when the tracer
has finished filling every architectural result field.

## Vector widths and discard state

**cp_discard** samples the complete **{branch_discard_q, discard_req_q}**
concatenation, not an OR-reduced bitmap. Its width is **PrefetchDepth + 1**.
Each legal bitmap/request-flag combination has its own bin:

| Prefetch depth | Branch-discard bitmaps | Normal bins including the request flag |
|---|---|---:|
| 2 | 00, 01, 11 | 6 |
| 3 | 000, 001, 011, 111 | 8 |

Bit 0 of the bitmap represents the oldest request. The prefetch update logic
sets prefixes and shifts them towards bit 0 on responses, so sparse/non-prefix
masks are structural errors. An illegal bin and **AssertDiscardPrefix**
check that assumption. This is pending-state coverage, not a count of discarded
responses.

The FIFO occupancy bind carries the full unsigned 32-bit **$countones**
result; it is not narrowed to four bits. Complex-unit state coverage uses the
RTL's two-bit encoding and a four-bit current/next-state concatenation.

Not every reduction is an error: **any forwarding active**, **both slots valid**
and occupancy counts are deliberate summaries. Preserve full masks when bit
identity matters, use counts only for multiplicity, and document intentional
summaries. **test_checkers.py** elaborates the real DUT in both prefetch-depth
configurations and checks the discard operands, occupancy width and complex FSM
widths to catch regressions.

**cp_err0 / cp_err1** in **kudu_fcov_id.sv** sample three-bit error
categories, not the raw five-bit **ir_errs_t** flags. Each has seven explicit
normal bins: no error, permission, bounds, illegal instruction, illegal
compressed instruction, fetch error, and multiple errors (encodings 0 through
6, respectively). Encoding 7 has an illegal bin and a matching assertion.
The RTL can raise simultaneous error flags; these legitimately map to
**ERR_MULTIPLE**, rather than an illegal coverage value. The sampled enum is
packed into bits without changing its width so VCS accepts the reserved bin.
Regressions check the bin encodings and all 32 raw-mask classifier inputs.

## IR CJALR prediction

**cp_cjalr_predict_ok** observes both physical decoder-slot prediction flags,
masked by **s0_rd_valid**, with normal **none / slot0 / slot1** bins and an
illegal **both** bin. **AssertCjalrPredictOneHot** checks the same masked
vector with identical mode/validity guards, outside reset. It
samples only when at least one input slot is valid. The flags describe
prediction eligibility before the stage-1 valid/ready acceptance mask.

**cp_cjalr_pcc_set** observes the actual PCC-update output with **no_update**
and **hit** bins; no update can also mean idle or stalled, not just a failed
prediction. Both points sample only with **PredictRA && CHERIoTEn && cheri_pmode_i &&
!StageBypass[1]**. Disabled hardware/pipeline configurations have zero weight;
RV32-compatible mode suppresses sampling.
The hierarchical prediction tap is generated only when applicable, so
configurations without **gen_stage1** do not reference a nonexistent signal.

## IR register addresses and write/source matches

**cp_rf_ren0 / cp_rf_ren1** treat the RS2-only read-enable mask **2'b10**
as illegal. **none**, **rs1**, and **both** remain normal bins.
**AssertRfRen0Legal / AssertRfRen1Legal** check the same decoder signals
with the corresponding **ir_valid_o** qualifier, outside reset.

**cp_cjalr_rs1_0 / cp_cjalr_rs1_1** distinguish **ra** (**rs1 == 1**)
from **other** (**rs1 != 1**, including x0) for each IR output slot.
They require **CHERIoTEn**, runtime **cheri_pmode_i**, slot-valid,
**is_jalr**, and the slot's **rf_ren[0]**. These are decode-stage
observations, not retirement events, and are independent of **PredictRA**.
Non-CHERI builds give them zero weight and do not sample them.

**kudu_fcov_id.sv** observes both logical decode outputs, **ira_dec_o**
(slot 0) and **irb_dec_o** (slot 1):

| Points | Sampling condition | Bins per point |
|---|---|---|
| **cp_rs1_0 / cp_rs1_1** | Slot valid and that slot's **rf_ren[0]** | One per register, x0 through x31 |
| **cp_rs2_0 / cp_rs2_1** | Slot valid and that slot's **rf_ren[1]** | One per register, x0 through x31 |
| **cp_rf_waddr0 / cp_rf_waddr1 / cp_rf_waddr2** | Corresponding **rf_weN_i** | One per address, 0 through 31 |
| **cp_rf_waddrN_rsS_L** | Write enabled, slot L valid, source S read enabled | **same** and **different** |

The last family covers every combination of three write ports, two sources
and two slots: 12 individual equality points, not a large address cross.
For example, **cp_rf_waddr2_rs1_1** compares **rf_waddr2_i** with
**irb_dec_o.rs1**, gated by **rf_we2_i**, **ir_valid_o[1]** and
**irb_dec_o.rf_ren[0]**. All use the group's reset-gated clock sampling.

The three five-bit write-address inputs connect through the existing
**bind ir_stage ... (.*)**; no additional bind or hierarchy layer is needed.
Write-address coverage does not require an IR instruction to be valid.
Matches describe same-cycle address equality, not successful forwarding,
operand correctness, or an architectural RAW dependency. In particular,
x0 equality is included. Existing x0 summary points are retained.

## Submodule coverage

Submodule coverpoints stay in their existing owning coverage modules and use
hierarchical RTL references. They do not introduce new coverage modules,
binds, or independently maintained FIFO models.

### Fetch buffering and alignment (`kudu_fcov_if`)

`cg_ma_if` observes `if_stage.prefetch_buffer_i.fifo_i` (`fetch_fifo64`)
before branch prediction or instruction-buffer substitution:

* The existing `cp_fifo_occupancy` remains the single unconditional registered
  word-count coverpoint. `cp_fifo_clear_level` measures that count on redirects;
  `cp_fifo_alt_restore_level` measures the zero-to-three saved words restored
  from an ALT entry, not the number of allocated ALT entries. ALT save/pop
  coverage distinguishes retaining slot 1's word after a slot 0 prediction
  from ordinary word consumption.
* Word arrival/pop combinations and empty-FIFO bypass distinguish storage
  activity from instruction consumption. One FIFO word can supply multiple
  instructions, so instruction reads do not necessarily pop a word.
* Each output slot has eight length/alignment bins: 16/32-bit instructions
  at PC byte offsets 0, 2, 4 and 6 within a 64-bit word. A separate aligner
  offset covers the actual data-mux selection, which can differ from PC
  alignment when unaligned fetch is enabled.
* Two-instruction length combinations and 2/4/6/8-byte advancement paired
  with word retention/pop exercise the aligner's consumption cases.
* Tail readiness and buffered-versus-arriving second-word selection cover
  boundary waits and completed split instructions. First/second-word errors
  are observed separately from the existing output fetch-error coverpoints.
* The prefetch parent contributes capacity-limiting and held-request/redirect
  arbitration coverpoints.

Instruction alignment and pair lengths sample actual FIFO transfers without
reported fetch errors. Transfer/word-flow samples exclude clear cycles, because
the raw FIFO output is suppressed by its parent on a redirect. Occupancy and
tail-wait observations are intentionally cycle/event samples, not retire counts.

### Decode, execution and load/store children

**Decoder CHERI checks:** **kudu_fcov_id.sv** also reports
**FC_MA_ID.ir0_decoder** and **FC_MA_ID.ir1_decoder**. Each has explicit
zero/one bins for **hdrm_ge4**, **hdrm_ge2**, **hdrm_ok**, **base_ok**,
**allow_all**, **cheri_perm_vio**, and **cheri_bound_vio**, tapped directly from
the corresponding **ir0_decoder_i** or **ir1_decoder_i**, plus **cp_debug_mode**.
These are eight coverpoint declarations instantiated twice (16 points).
**x_perm_vio_debug** and **x_bound_vio_debug** each have three legal goals:
normal mode with/without the error, and debug mode without the error.
The error-active/debug-mode combination is excluded from coverage goals;
**AssertDebugSuppressesCheriErrors** detects violations for each decoder.

Sampling requires reset released, a valid decoder input, active CHERI mode,
and no flush of that input stage. Error/debug points include debug-mode
samples; the five bounds-calculation helpers retain their non-debug qualifier.
It does not require
instruction acceptance or a fault-free decode. For **StageBypass[1] == 0**,
decoder validity is **s0_rd_valid[0/1]**. For **StageBypass[1] == 1**, the
decoders consume physical mema/memb, so **ira_is0_o** maps the age-ordered
valid bits to their physical decoders. S0-only flush suppresses buffered
sampling, but not the direct-stage FIFO. Both groups have weight zero on
RV32-only hardware. Existing bind and file lists are unchanged.

| Owner | Hierarchical observations added |
|---|---|
| `kudu_fcov_id` | Stage-0 FIFO stored occupancy and accepted read source; full final-stage FIFO exchange |
| `kudu_fcov_alu` | `rv32_alu` comparison decisions and shift-amount boundaries on accepted, nonflushed integer operations |
| `kudu_fcov_lsu` | `lsu_if` hold capture/backlog, writeback FIFO storage flow, retained WAW-head cancellation, LSU start blockers and split-load capture |
| `kudu_fcov_dcache` | Existing WAW FIFO's stored versus write-through reservation read |
| `kudu_fcov_trvk` | Saved capability's range/sealing eligibility while valid |

ID hierarchy follows `StageBypass`; inapplicable occupancy/read-source bins
are filtered for the configured FIFO implementation. WAW reservation validity
is not treated as occupancy. Data-dependent observations use the saved request
or a qualified transfer, not a later instruction's live decode.

This expansion adds 28 coverpoint declarations within the existing 15
covergroup types. The bind and file lists are unchanged. It is not an exhaustive
coverage model of every child: `multdiv32` internals remain deferred because
their unnamed generate scope would require nonportable `genblk` references;
no RTL rename, new bind or checker relaxation was introduced to work around it.

## Complex-unit FSM transitions

**cg_ma_cmplx.cp_transition** in **kudu_fcov_cmplx** uses standard
SystemVerilog transition bins on **cmplx_fsm_cs** (sampled each enabled
clock): six legal state changes (**start_req**, **read_abort**,
**read_ok**, **wr_issued**, **wr_flush**, **wr_done**), four per-state hold
bins, and an **illegal_bins bad_transition** list of the remaining
transitions, paired with **AssertCmplxTransition**. **cmplx_fsm_ns** is no
longer a monitor port. Bin names changed, so start a fresh database.

## Branch-unit coverage

**kudu_fcov_branch_unit** (in **kudu_fcov_ex.sv**) is bound to the single
**branch_unit** instance and declares **cg_ma_branch** with 12 points per
logical slot, reported separately as **FC_MA_EX.branch.ir0** and
**FC_MA_EX.branch.ir1**. Branch-unit inputs/outputs are monitor ports
connected with **.\***; only the issuer qualifiers (**DECODE** state, slot
valid/hazard, commit error, issued) are read hierarchically from
**kudu_top.issuer_i**. The groups were previously embedded in the ALU0
monitor; their names, points and bins are unchanged, but the instance
path is now **branch_unit_i.u_fcov_branch_unit.gen_slot[N]**, so use a
fresh database.

The points cover branch/JAL/JALR kinds, physical A/B ordering, issued versus
held evaluation, all six conditional-branch operations with taken/not-taken
outcomes, operand signs/equality, branch direction, prediction direction,
the full four-bit misprediction cause, JALR prediction,
raw target low bits and immediate ranges, and CJALR error masks.

Sampling requires reset released, issuer **DECODE** state, a valid logical
slot, resolved operands (**!ir_hazard[slot]**), no commit error, no existing
decode error, and a branch/JAL/JALR instruction. The decode and resolved
operands are reordered using **branch_unit_i.ira_is0_i**, matching the
already-ordered branch-unit outputs.

These are **evaluations, not retirement events**. A stalled or subsequently
discarded candidate can count once its operands are ready. Requiring issue
would miss CJALR faults, which prevent issue; **cp_issued** records whether
the evaluated candidate was issued that cycle.

The three CJALR error bits are independent: **{execute permission, sealing
rules, tag}**. All eight combinations are normal coverage values, not illegal
encodings. CHERI check/error points sample only in CHERIoT mode; neither
RV32 runtime case contributes zero-error/check-disabled hits, including
PMODE=0 runs contributing shared coverage to the combined CHERIoT report.
The JAL target-miss cause is filtered when **ChkBranchJALAddr** is disabled.
JALR target coverage observes the masked target (**{r[31:1],1'b0}**), so odd
low-bit values are illegal (**AssertSvaBrJalrTargetEven**).

## One issuer group, four sampling kinds

**cg_ma_issue** has exactly one instance, **FC_MA_ISSUE**, containing all
**113 coverpoints and 17 crosses** (20 points and 10 crosses were added for
the bug cross-check; see "Bug-driven coverage" below). Forwarding, prediction-resolution and
CHERI temporal dependency points no longer appear as separate groups.
Typed sample arguments carry the event kind and payload by value; every
point and cross has an event-kind **iff** guard. Outside reset, each rising
edge samples the cycle points once, then separately samples each used nonzero
source operand (up to four), issued control-flow instruction (up to two), and
applicable CHERI dependency (up to two). Event calls do not resample cycle
points, including FSM transitions or the saved-RA comparison.

Per-point sampling qualifiers and cross weights are retained. All four
**cp_fwd_wrsv_r1..r31** values, including **pair_2**, are normal coverage goals.
The three former CHERI subgroup points now carry **CHERIoTEn ? 1 : 0**
weights individually; their cross still uses **CHERIoTEn && LoadFiltEn**.
This preserves hardware applicability, not the former four-group weighted
average: grouping changes the aggregate score. Compare per-point/bin results,
and start fresh databases rather than merging the old hierarchy.

**run_issue_sampling.py** runs deterministic native VCS stimulus across both
hardware parameters, both load-filter settings and both runtime modes.
It checks reset rejection, nine same-edge samples, x0/unused/invalid operands,
FSM transitions and RA tracking. An optional **--baseline PATH** takes the
pre-consolidation source snapshot and instantiates it beside the production
monitor on the same signals, comparing the snapshot's 100 native point/cross
bin reports with the same-named production points (the production group now
reports 130; later additions are absent from the snapshot) and point options (allowing only the documented CHERI weight relocation;
all bin counts must match). Separate
**+forwarding_pairs** runs check all four normal bins for every register
in both hardware builds and runtime modes, including reset, between-edge and
x0 rejection and all 124 pair goals, without error-continuation flags. All generated
sources, logs, reports and databases are retained under a fresh **sim/temp/**
directory; **--check DIRECTORY** rechecks them without licensed tools.

## Issuer exception causes

**cp_mcause** samples the full six-bit **csr_exc_info_o.mcause** only when
**csr_save_cause_o && !debug_csr_save_o**, on rising clock edges outside
reset. Debug entry also asserts save-cause but leaves mcause at its default;
neither that value nor idle cycles count as an exception.

Bins follow **issuer.sv**: instruction-access fault, illegal instruction,
CHERI fault, breakpoint, U/M-mode ECALL, software/timer/external machine
interrupts, and individual fast interrupt IDs 0-14 (**0x30-0x3e**).
The issuer also forwards **cmt_err_info_i** during commit flush, so load/store
misalignment and load-access fault from the current LSU are included.
The **other** default bin records unlisted encodings diagnostically, without
making them normal coverage goals. Unlike CSR-side cause coverage, this point
does not count software writes to MCAUSE.

The existing wildcard issuer bind connects the typed exception-info struct
and both save strobes. The standalone issuer fixture's **+mcause** mode
sweeps all 64 encodings under reset, save-disabled, debug-save and normal
trap-save conditions. Each of the 27 normal bins should receive one hit;
only the final sweep contributes.

## Issuer branch misprediction events

**cp_ira_is0** covers the issuer's physical-to-logical slot selector
**ira_is0_i** on each rising clock edge outside reset. Its bins are
**irb_is_ir0** (0) and **ira_is_ir0** (1), including cycles without valid
instructions. The input connects through the existing wildcard issuer bind.

**cp_branch_mispredict_event** in **kudu_fcov_issue.sv** samples the full
two-bit **branch_mispredict_event** signal through the existing wildcard bind.
Separate wildcard hit bins **ir0** and **ir1** count each asserted slot bit;
zero contributes no hit. The RTL already qualifies this signal with branch
decode and issue, unlike the unqualified **mispredict** vector. Sampling is
on rising clock edges outside reset. The standalone issuer fixture's
**+branch_mispredict** mode expects one IR0 hit and two IR1 hits, excluding
events presented during reset.

## Issuer per-register reservation state

**kudu_fcov_issue.sv** observes the registered reservation bitmaps directly,
instead of the six derived per-slot RAW/WAW/CHERI state points:

| Coverpoints | Bins |
|---|---|
| **cp_reg_wrsv_q** | **r1** through **r31**, each matching its bit set |
| **cp_reg_cheri_trsv_q** | **r1** through **r15**, each matching its bit set |

The inputs retain the RTL's **[31:1]** and **[15:1]** ranges and connect
through the existing wildcard issuer bind. Sampling expressions pad bit zero
and zero-extend as needed so the 32-bit wildcard positions match register
numbers without shifting their meaning. The bins overlap: one sample counts
every reserved register, not only one-hot bitmap values. No register-zero
bin is created.

Each point has an **x_cp_<signal>** cross with **cp_hazard**, which samples
**hazard_q = ir_hazard & ir_valid_i**. Thus each reserved register is crossed
with **none**, **ir0**, **ir1**, and **both**, giving 124 bins for
**x_cp_reg_wrsv_q** and 60 for **x_cp_reg_cheri_trsv_q**.
These are reservation-state observations on
each rising clock edge outside reset, not claims that every reserved register
caused the current instruction's hazard. No additional slot-valid gate is
applied to the bitmaps. The CHERI point and its cross require runtime CHERIoT
mode and have zero weight when CHERIoT or load filtering is compiled out.
The ordinary write-reservation bitmap remains active in all three modes.

**cp_fwd_wrsv_r1** through **cp_fwd_wrsv_r31** each sample
**{ir0_pl_fwd_act[n], reg_wrsv_q[n]}**. The four normal bins retain their
native names **pair_0** = **00** (neither), **pair_1** = **01** (reserved only),
and **pair_3** = **11** (both). **pair_2** = **10** (forwarding without a write
reservation) is also a coverage goal: 124 normal bins in total.
The former **AssertFwdRequiresReservation** assertions are removed.
These points sample every rising clock edge outside reset, including idle
cycles, all hardware/runtime modes and either load-filter setting. There is
no instruction-valid qualifier; x0 is excluded. Additional event-kind samples
do not count.

The standalone **tb_fcov_issuer_ra.sv** fixture also accepts **+hazard_bits**.
It exercises every reservation bit with all four hazard values, then all
reserved bits together and an empty bitmap. Each of the 46 set-bit bins should
have five hits; all 184 cross bins should be covered, with two hits for
**both** and one for each other hazard value. Its
**+forwarding_pairs** sweep includes all four normal values.
The current **tb_fcov_frontend_temporal.sv** fixture's
**+forwarding_pairs** case, driven by **run_issue_sampling.py**, checks the
four values, including exactly one **pair_2** hit per register, without
**-covg_cont_on_error** or assertion failures.
This coverage schema change requires a fresh database.

## RA update followed by a stalled CJALR

**kudu_fcov_issue.sv** adds **cp_ra_update_jalr** to **FC_MA_ISSUE**.
It captures the predicted RA when an issuing logical IR0 writes register 1
while logical IR1 is a predicted CJALR reading register 1, has a RAW hazard,
and cannot issue. Sampling requires runtime CHERI mode.

The monitor saves the younger instruction's PC, instruction and predicted
register-format capability. It follows that instruction into logical IR0 and
compares against the physical A/B forwarded source capability only after its
hazards clear. Comparing on the initial stall would instead observe stale RA.
Each captured pair contributes at most one sample, including a resolving
CJALR that redirects or faults rather than issuing.

| Bin | Meaning |
|---|---|
| **actual_equals_predicted** | Equal address, tag, object type, reserved bit, expanded bounds and permissions |
| **predicted_more_permissive** | Predicted bounds contain actual bounds and predicted permissions contain all actual permissions, with at least one strict difference |
| **predicted_less_permissive** | Actual bounds contain predicted bounds and actual permissions contain all predicted permissions, with at least one strict difference |
| **other** | Incomparable authority, changed address/tag/object type/reserved bit, or a non-equal comparison with untagged or inverted bounds |

The more/less bins require matching address and metadata and tagged
capabilities. Bounds use the full **33-bit upper limit**; permissions use
set inclusion, not numeric ordering. Equality is semantic rather than a
comparison of redundant compressed/cached encoding fields. A flush, commit
error, mode exit or replacement consumer cancels an unresolved observation.
The resolving CJALR's own redirect does not suppress its sample. These are
issuer evaluations, not proof that either instruction retired, and the
coverage monitor neither forces a stall nor checks architectural correctness.

**tb_fcov_issuer_ra.sv** is a standalone directed fixture for the actual
coverage module. Compile **cheri_pkg.sv**, **csr_pkg.sv**, **super_pkg.sv**,
**kudu_fcov_pkg.sv**, **kudu_fcov_issue.sv**, and the fixture, in that order,
using VCS **-sverilog +define+CHERIoT -top issuer**. The fixture deliberately
supplies the **issuer** hierarchy: do not include the real RTL issuer or the
production bind/file list. Use a fresh build directory, a separate run database,
and **submit -i** for compilation, simulation and URG.

## Instruction-context coverage

**kudu_fcov_context.sv** samples simultaneous stage contents on each rising
edge outside reset, before register updates. It no longer samples issue strobes,
walks the WAW FIFO, or combines EX2 and WB into one context.

| Report instance under **FC_MA_CONTEXT** | Resident source |
|---|---|
| **frontend** | **ir_stage_i.s0_rdata0/1**, classified through their existing decompressor/decoder outputs; present only when **CFG.IrStageBypass[1] == 0** |
| **alu0_wb**, **alu1_wb** | The respective valid WB register, using the category tags maintained by **kudu_fcov_alu** |
| **lsif_req_dly** | **ls_pipeline_i.lsu_if_i.req_dly_q**, with **req_dly_valid** in **DLY1** or **DLY1_WGNT** |
| **lsu_req** | **load_store_unit_i.lsu_req_info_q**, while **outstanding_resp_q** is set |
| **mult_ex2**, **mult_wb** | The respective valid saved instruction, CHERI operation and CJALR flag |

The frontend cross **x_s0_s1** is **s0_rdata0 x s0_rdata1 x ir0 x ir1**,
capturing the S0/S1 relationship independently of special events.
The frontend event coverpoints remain standalone.
Each of the six execution instances has its own
**ir0 x ir1 x special_event x ex_resident** cross.

The S0 axis (**cp_s0_rdata0/1**) uses its own coarse execution-class
category: **S_ALU** (every RV32 ALU form, including LUI, AUIPC/AUIPCC,
shifts, bitmanip, and CHERI inspect/modify/seal operations), **S_MULDIV**,
**S_BRANCH**, **S_JAL**, **S_JALR**, **S_LS** (integer and capability loads
and stores), **S_AMO** (including LR/SC), **S_CSR** (including CSPECIALRW),
**S_SYS**, **S_ILLEGAL** and **S_EMPTY**. With all features enabled,
**x_s0_s1** has 10 x 11 + 1 = 111 S0 pairs and 57 IR pairs (6,327 goals).

The EX axis (**cp_ex_resident**) uses a finer context category, mapped from
the detailed instruction category:
**C_ALU** (every RV32 ALU form, including LUI, shifts and bitmanip),
**C_AUIPCC** (the AUIPC opcode: AUIPCC when PMODE=1, AUIPC when PMODE=0),
**C_MUL**, **C_DIV**, **C_BRANCH**, **C_JAL**, **C_JALR**, **C_LOAD_INT**,
**C_STORE_INT**, **C_LOAD_CAP**, **C_STORE_CAP**, **C_AMO**, **C_CSR**,
**C_SCR**, **C_CHERI_INSPECT**, **C_CHERI_MODIFY** (including CSeal/CUnseal
and AUICGP), **C_SYS** and **C_ILLEGAL**. The LSU splits loads from stores
by the saved **is_load**; the ALU WB stage carries an AUIPC flag beside its
detailed category. The two IR axes use only pipeline designations with a
separate DIV category. Use per-configuration URG denominators, not source
declaration counts.

**cp_ir0/1** use the issuer's logical age-ordered decodes, not physical IRA/IRB.
Each has eight bins: **IR_LOCAL**, **IR_ALU**, **IR_LS**, **IR_MULT**,
**IR_DIV**, **IR_JAL**, **IR_JALR**, and **IR_EMPTY**. A valid slot samples
**ir*_dec.pl_type**, except that **DIV/DIVU/REM/REMU** under **PL_MULT**
use **IR_DIV**. The split checks the complete RV32M opcode/funct7 and the
divide/remainder funct3 bit; CHERI operations using MULT remain **IR_MULT**.
Multiplication variants also remain **IR_MULT**. An invalid slot uses
**IR_EMPTY**, never stale decode data.
This applies to both frontend and all six execution instances, including
stalled instructions. Other instruction categories, branch outcomes, faults,
breakpoints and sysctl flags no longer subdivide or override the IR bins.
Interrupt/debug/error handling remains in standalone event coverpoints and
the execution crosses' event axis.

These are decoder designations, not resolved execution-pipeline selections.
In particular, **PL_JALR** stays **IR_JALR**: it routes through ALU when
**CHERIoTEn=0** or **PMODE=0**, and through MULT when both are one.
The EX axis still describes the actual resident pipeline.

**cp_special_event** has six bins over
**{cmt_err_i, handle_debug, ir1_err, ir0_err, handle_irq}**:
**none** (`00000`), **irq** (`????1`), **ir0_err** (`???1?`),
**ir1_err** (`??1??`), **debug** (`?1???`), and
**commit_error** (`1????`). Each slot's error is
**ir_valid[slot] && issuer_i.ir_any_err[slot]**, retaining decoder errors and
issuer-detected CJALR errors. **ir0_err** is equivalent to **handle_err**;
**ir1_err** observes a pending younger error without waiting for it to become
IR0 or for exception handling to begin. Invalid slots cannot report stale errors.
The per-bit bins overlap: multiple asserted
conditions hit multiple bins and corresponding execution cross goals on the
same edge.
They are not exact-onehot or priority-selected events.
The uncrossed **cp_special_event_value** retains all 32 exact masks, including
zero, in both frontend and execution groups with the same sampling event.

Feature and execution-routing filters remove unsupported S0/EX categories.
ALUs exclude loads, CSRs, MUL/DIV and local
instructions; MULT accepts MUL/DIV, bounds/representability CHERI operations
and CHERI CJALR; LSU accepts memory, atomic and CSR/SCR requests.
Bitmanip is part of the ALU category, so it needs no feature gate. Resident
categories are not re-gated by a later
live PMODE value. Cross exclusions enforce ordered S0/IR validity.
In the execution crosses, **error_without_ir0/1** exclude the respective
**ir0_err/ir1_err** bin when that slot is **IR_EMPTY**, since each error requires
a valid slot. Other former
fault/category exclusions are removed: pipeline designation alone cannot
identify a fault.

In **x_ir_special_ex** only, a valid IR slot with **is_cmplx** suppresses
cross sampling, excluding AMO without excluding other **PL_LOCAL**
instructions. Invalid slots with stale **is_cmplx** do not suppress sampling.
Execution-resident AMO read/write phases also suppress that stage's cross
using the saved request's
**amo_flag[3:2]**. The shared **C_AMO** category and its cross goals remain,
because they also cover LR/SC (**amo_flag[1:0]**), which are not excluded.
LR/SC in IR continues to contribute to **IR_LS** cross goals. AMO observations
still sample in individual coverpoints and the frontend cross. The cross
qualifiers remove AMO samples, not shared pipeline bins or their non-AMO goals.
Assertions expose unexpected resident categories, pipeline encodings and
validity ordering instead of silently discarding them.

The LSU delay buffer is normally used by stores and non-early reads, but an
early-load or CSR request arriving in **DLY1** can also queue there. Copies
left by the direct early path in **IDLE/DLY0_WGNT** are excluded. The hold
buffer is deliberately not covered here. Complex AMO requests omit the
opcode, so both AMO halves and LR/SC are classified using **amo_flag**.

Counts measure cycles containing a particular simultaneous snapshot, not
retired instructions or data dependencies. Matching IR and resident pipeline
types are not excluded: these can be different instructions, including
instructions stalled behind a busy pipeline. Remaining goals are not a proof
of reachability under every software environment. This replaces the old
**cg_context** schema; start a fresh database and preserve previous results.

The execution event axis uses six overlapping bins rather than crossing all
32 exact masks; the separate raw-mask point has 32 standalone goals per instance.
Recompile into a fresh database.
Run **python3 -B fcov/run_context_events.py** from **sim/** with the VCS
modules loaded for the focused native regression. It extracts both production
covergroup definitions, checks all masks and ordered/unordered resident
combinations, and verifies exact URG marginal and cross counts, including
AMO exclusions, retained LR/SC goals and standalone bins. It extracts the
production IR enum and logical-slot taps, exercises every pipeline designation
under both physical slot orderings and hardware modes, and checks all eight
RV32M operations plus CHERI/non-M negative controls for the DIV split.
Special decode flags do not override the designation. Independent and
simultaneous slot errors, including issuer-only errors and invalid-slot
suppression, are checked alongside stale AMO and unknown pipeline data.
Its full IR domain and reduced S0/EX domains test coverage semantics, not DUT reachability. Use
**python3 -B fcov/check_syntax.py --matrix** for full-design elaboration across
all four pipeline configurations and both hardware modes.

## Coverage schema and output safety

The corrected bins, category meanings, sampling guards and new crosses change
the coverage schema. Compile and run in fresh output directories and start a
new coverage database; do not merge these results into an older schema or
overwrite an existing database. Run every VCS compile, simulation and URG
command through `submit -i`.

See `COVERAGE_CHANGES.md` for the implementation report, validation evidence
and explicitly deferred work.

## LSU FIFO occupancy coverage

Within **cg_ma_lsu** in **kudu_fcov_lsu.sv**, **cp_waw_fifo_level** samples
**ls_pipeline.waw_fifo_i.fifo_level** into **empty / one / two_or_more** bins.
**cp_wb_fifo_level** samples **ls_pipeline.wb_fifo_i.fifo_level** into
**empty / one_or_more** bins. No additional coverage modules or binds are used.
The existing LSU covergroup samples the signed eight-bit simulation counters
on rising clocks with reset released, before that edge updates occupancy.
Negative levels do not fill the nonnegative bins; these points cover stored
occupancy, not same-cycle bypass traffic. Dcache and RVFI FIFOs are not included.

## LSU response and FSM coverage

The forwarding-cache **cp_rd_match** and **cp_wr_match** sample their raw
four-bit match masks: **0000** is a miss, and each one-hot value has a separate
hit bin. Read matches with weight **2 or greater** are illegal, backed by
**$onehot0(rd_tag_match)**. For write matches, all six weight-2 masks share
one **two_hits** bin; weight **3 or 4** is illegal, backed by
**$countones(wr_tag_match) <= 2**.
**cp_resp_inval_two_matches** covers **resp_invalidate=1** while exactly two
bits of **wr_tag_match** are set (a capability access matching both words).
**cp_unaligned_two_matches** covers a misaligned integer access that
straddles words **addr** and **addr+4** (a word at offset 1-3 or a halfword
at offset 3, the accesses load_store_unit splits) while both words are held
in valid lines. It samples at request acceptance (**lsu_req_i &&
lsu_req_done_i**), before **unaligned_access_q** invalidates every line,
and excludes CSR, capability, AMO/LR/SC and CHERI-faulting requests. Its
eight bins are load/store by word offset 1/2/3 or halfword offset 3. The
**addr+4** match compares **tags** directly, since **wr_tag_match** only
covers the first word of an integer access.
**cp_rd_hit** and **cp_rd_match_ok** sample only while **lsu_req_i** is
asserted; their request input is connected by the existing wildcard bind.
**cp_fwd_addr1** and **cp_fwd_data1** sample the corresponding **fwd_info_o**
fields only when **fwd_info_o.valid[1]** is asserted, using automatic bins.
The data point covers **data1[31:0]**, not the capability-width container:
dcache zero-extends its 32-bit integer result, so covering the full 69-bit
field would put every result in the lowest automatic range. The 64 data
range bins now span the meaningful 32-bit value domain in both hardware builds.
They observe the active dcache forwarding slot; the tied-off slot 0 is not
a coverage target.

**cp_repl** samples only when the cache is enabled and at least one line
actually updates (**update_valid & ~update_invalid**). Its four way bins
cover replacement updates; **none** covers updating an existing matching line.
Idle selector rotation, disabled-cache activity and invalidation-only cycles
do not credit replacements.
**cp_update_valid** has normal count bins **0 / 1**; counts **2--4** are illegal.
**cp_update_invalid** has normal count bins **0 / 1 / 2 / 4**; count **3** is
illegal. These reflect a single updated word, at most two matching invalidated
words, or all-line unaligned invalidation. The equivalent
**AssertUpdateValidOneHot** and **AssertUpdateInvalidNotThree** assertions
remain active whenever the coverage monitors are compiled in.

CSR access coverage belongs to **FC_ISA_CSR**. The LSU monitor no longer
duplicates **cp_access**, **cp_op_en**, **cp_op**, **cp_read_only**,
**cp_cheri**, **cp_addr**, or **cp_illegal**. LSU request classification
(including **cp_is_csr**), response/error handling, and **cp_tsafe_en**
remain in the LSU monitor.

The LSU-specific response checks **cp_csr_cheri_asr_err**, **cp_cheri_ls_err**,
and **cp_ls_align_err_only** observe internal **load_store_unit_i** signals:
**csr_cheri_asr_err**, **lschk_err_final.any_fault** and bit 5 (align-only) of
**ls_err_cause**. They require **lsu_resp_valid** and both current
and saved CHERI mode, with zero weight on RV32-only hardware. The ASR point
samples CSR responses (**csr_go_q**), including denied accesses that never
reach the CSR block. The load/store error point excludes CSR transactions.
Both have separate clear/error bins. Alignment-only coverage samples actual
load/store CHERI errors, distinguishing alignment-only from other CHERI faults.

Request-side error coverage (**cp_cheri_req_err**, **cp_cheri_req_cause**,
**cp_align_err_only**) reads **lsu_req_info.lschk_err** (the **check_ls_err**
result attached by **lsu_if**) and decodes the cause with
**cheri_pkg::vio_cause_enc**, so it uses the RTL's own cause priority.
**check_ls_err** also flags misaligned LR/SC/AMO in every mode.
**cp_atomic_align_fault_rv32** (PMODE=0 or RV32-only hardware) and
**cp_atomic_align_fault_cheri** (CHERI mode only) cover LR, SC and the AMO read
phase taking that fault at the response. The AMO write phase is not a goal,
because a faulting read phase never issues it.

The LSU **cp_resp_clrperm**, **cp_resp_is_load**, and **cp_resp_is_cap** sample
only with **lsu_resp_valid**. Permission masks and load/store identity come
from **load_store_unit_i.lsu_req_info_q**, the saved metadata for the responding
transaction; **lsu_resp_info** is a **pl_out_t** with **is_cap** but no
**clrperm** or **is_load** fields. The capability point reads that response's
**is_cap** directly. New live requests cannot change these observations.
**cp_resp_clrperm** replaces the request-side **cp_clrperm** and keeps eight
separate mask bins: **0, 1, 2, 3, 8, 9, A, B** (hex).
Permission masks additionally require a capability response. Both CHERI
points retain current-mode and saved-response-mode guards and zero weight
on RV32-only hardware; load/store identity remains shared across modes.

**resp_mem_cap** casts **load_store_unit_i.data_rdata_i** to
**cheri_pkg::mem_cap_t**, before permission/tag masking. The seven
**cp_resp_cap_*** points cover **valid**, **rsvd**, **cperms**, **otype**,
**cexp**, **top8 versus base9[7:0]**, and **addr**. They require a valid, error-free
LSU data response for a capability load, with both current and saved CHERI
mode active. This covers memory returns, not dcache forwarding. **valid** has separate
tagged/untagged bins. The other fields sample only tagged capabilities.
**cexp** has separate bins for **0, 31, 24, 1**, plus one scored **other**
bin combining **2--23 and 25--30**. **cp_resp_cap_top_vs_base** has separate
**equal**, **greater**, and **less** bins comparing **top8** with only
**base9[7:0]**; **base9[8]** is ignored. There are no standalone top/base
coverpoints. The remaining raw fields use automatic bins
(one per value for fields up to six bits, up to 64 range bins for wider
fields). All seven points have zero weight on RV32-only hardware.

The six CHERI-dependent LSU crosses have explicit sampling guards and zero
instance weight on RV32-only hardware; weighting their constituent points
alone does not disable a cross. **x_ls_rv32_1** remains shared.
**x_ls_type_2** observes faulting requests, including both loads and stores.
The permission crosses require a successful capability-load memory response;
**x_resp_clrperm_2** additionally requires a tagged raw capability.
It crosses the six-category **cp_resp_cap_perm_category** helper with the eight
saved response masks: **48 goals**, rather than 512 raw-value combinations.
The standalone **cp_resp_cap_cperms** still covers all 64 raw return values.
**cp_resp_cap_perm_bits** independently covers absent, preserved and cleared
states for each maskable expanded permission: Global, Load-Global,
Load-Mutable, Store, Load/Store-Capability and Store-Local. Its 18 overlapping
goals observe actual pre-/post-mask permissions, including sealed capabilities,
category conversion and tag-clearing responses that suppress permission masking.
The native LSU **permissions** scenario checks exact counts over all 64
encodings, eight masks and sealed/unsealed cases, plus sampling exclusions.

**x_access_err** crosses **cp_out_is_cap** with **cp_out_mcause** on the same
valid, faulting WB FIFO head. Both current CHERI mode and that head's saved
mode are required. **cp_out_is_cap** is a zero-weight helper, not another
independently scored goal. An unrelated concurrent response cannot change
the access classification, and no response is required while an older
writeback is pending. **cp_resp_is_cap** retains its response-side meaning.
The existing **store_fault** cause goal is deliberately retained: the current
LSU bus-error branch emits **LOAD_ACCESS_FAULT** without a load/store
distinction. Resolve this RTL/architectural discrepancy before excluding
the store-fault goal; these coverage changes do not alter RTL.

**cp_transition** samples **ls_fsm_cs** using native SystemVerilog transition
bins, for example **(IDLE => WAIT_GNT)**. It records transitions between
consecutive samples of the current state, rather than matching a same-cycle
current/next-state concatenation. There are seven named transitions and
four distinct **hold[]** self-loop bins; **WAIT_RVALID_MIS_GNTS_DONE** is no
longer reachable, since the LSU issues the second half of a split access only
after the first rvalid. Sampling uses the
existing reset-qualified LSU covergroup clock event.
The unused next-state coverage port and bind connection are removed.
Recompile and use a fresh coverage database for the changed bin schema.

**cp_data_err_state** samples **ls_fsm_cs** only when both **data_err_i**
and **data_rvalid_i** are asserted. Its two bins are **WAIT_RVALID_MIS** and
**IDLE**, shared across operating modes.

## Commit register-write coverage

Each write port has **cp_waddrN_cheri** and **cp_waddrN_rv32** points, sampled
only when that port writes. The CHERI point requires **CHERIoTEn && PMODE**
and has one bin per register **1--15**; the RV32 point requires the inverse
effective mode and has one bin per register **1--31**. Thus RV32-only hardware
always uses the RV32 points, regardless of the ignored mode pin. CHERI address
points have zero weight on RV32-only hardware. Register zero is not a goal.

**cp_waddr0_eq_waddr1**, **cp_waddr1_eq_waddr2**, and
**cp_waddr0_eq_waddr2** each record a nonzero, same-destination pair.
Ports 0/1 must have their write enables asserted. Port-2 comparisons use
**load_early || load_late**, before arbitration: an older load conflicting
with a younger port-1 write is still covered when **rf_we2_o** is suppressed.
Idle/stale address equality does not count.

The generic **cp_rf_we** and **cp_rf_we2** points are removed.
The targeted **cp_we_vs_err** check and its assertion remain, as do write-port
count, reservation-clear and load-conflict coverage. These changes require
recompilation and fresh coverage databases.

With the VCS/LSF modules loaded, run **python3 fcov/run_cmt_writes.py** from
**sim/** for the focused regression using the real committer RTL.
It checks both hardware builds and both mode-pin values, all address goals,
exact pairwise match counts, suppressed early loads, and negative cases.
Licensed tools use **submit -i** and outputs are preserved in a fresh
**sim/temp/cmt_writes_*/** tree. Use **--check EXISTING_RUN_DIRECTORY** to
recheck its URG reports without running licensed tools.

## ISA coverage checks

**python3 fcov/check_isa_encoding_sets.py** checks all 65,536 compressed
encodings in both alias modes, the 165 operand identities, the 30 original
instruction/mode crosses, the single operand instruction/mode cross, and
the matching-field structure of all CS/CD crosses.

The older native instruction-mode runner depends on
**tb_fcov_isa_modes.sv**, which is not present in this checkout. Its historical
reports can still be checked read-only with
**python3 fcov/run_isa_modes.py --check temp/isa_modes_RUN_DIRECTORY**.
It is not an operand-rewrite regression. Native operand/classifier fixtures
and DUT runs for this rewrite are isolated under
**/home/scratch/fortress/kunyanliu/kudu_temp/isa_operands_TfPHiE/**; they preserve their reports and databases.
Destination-field and post-revocation sampling fixtures are under
**/home/scratch/fortress/kunyanliu/kudu_temp/isa_cd_B5l5l6/**, including exact cross-denominator and hit-count checks.

## Checking the model without a simulator

The Python checkers can run without a licensed simulator. The elaboration
and classifier checks require pyslang (`pip install pyslang`):

```
python sim/fcov/check_syntax.py    # full elaboration of kudu_top with the binds
python sim/fcov/check_syntax.py --matrix
python sim/fcov/check_syntax.py --matrix --coverage-off
python sim/fcov/check_syntax.py --matrix --fv-helpers   # also the FV-only kudu_fvh_* lemmas
python sim/fcov/check_binds.py     # resolves every bind port connection
python sim/fcov/count_cov.py       # source declarations, not expanded bins
python sim/fcov/check_isa_encoding_sets.py --classifiers
python sim/fcov/check_flow_bus_timing.py
```

The top-level coverage owner **kudu_fcov_top** and its queued timing helper
**kudu_fcov_bus_timing** are both defined in **kudu_fcov_top.sv**.
**cp_sbd_fifo_level** directly samples **kudu_top.sbd_fifo_i.fifo_level**
on each rising clock edge with reset released, retaining its signed eight-bit
width. It has individual bins for **0, 1, 2, 3, 4, 5** and one **6 and above**
bin. The current scoreboard FIFO has depth eight; occupancy is observed before
the edge's updates. This tap uses the RTL's simulation-only level counter.

The owner is bound as **u_fcov_top**, with one **cg_ma_top** group reported as
**FC_MA_TOP**. It includes **cp_fatal_err** and its five state/transition bins.
The bus request points have no **ready_no_req** bin, there is no
**cp_ibus_same_cycle_resp**, and **cp_fatal_err** has no
**reset_after_fatal** bin; these were removed as non-goals.
Explicit sampling keeps the other points on rising edges outside reset and
samples only the fatal point on falling edges, including during reset after
NBA updates. The fatal point is mode-gated and has zero weight on RV32 hardware.
Merging the former fatal group changes the schema: recompile and use a fresh
coverage database; existing databases are not migrated. CHERI-specific
tag, map and fatal coverage is additionally mode-gated; bus timing remains
active in all three modes. Queued request metadata retains the request's
CHERI-mode bit so response-tag coverage requires both CHERI request provenance
and CHERI mode at sampling time.

**FC_MA_TOP.cp_tsmap_addr_bits** has 20 overlapping wildcard bins: a zero
and a one goal for each bit of **tsmap_addr_o[9:0]**. Sampling requires
**tsmap_cs_o && cheri_active**, with zero weight on RV32-only hardware.
Each sample credits one value for each of the ten bits; this is per-bit
value coverage, not a 1,024-address cross or a transition/toggle count.
The existing **cp_tsmap_addr** range coverage remains unchanged.

**cp_tsmap_rdata** samples the one-cycle synchronous map response, using a
registered request qualifier rather than the current **tsmap_cs_o**.
The qualifier remembers that the request occurred in CHERI mode; sampling
also requires current CHERI mode. Reset discards pending validity.
Isolated and back-to-back reads therefore cover their returned words rather
than idle data or an unrelated current request. Address points continue to
sample on chip-select.

## Formal verification of the fcov assertions

JasperGold proves the SVAs of this model (the illegal-bin companions and the
kudu_sva_* invariants) with **fv/fv_kudu_fcov.tcl**. The FV-only helper
lemmas at the end of the fcov files (**kudu_fvh_*** modules, compiled only
with **+define+KUDU_FV_HELPERS**, and only with CHERIoT defined and
KUDU_FCOV_OFF undefined, like their binds at the end of kudu_fcov_bind.sv)
belong to that flow and never affect simulation. The wt_fifo lemmas
(AssertHelpWt*) stay inside **kudu_sva_wt_fifo**, guarded only by
KUDU_FV_HELPERS, because they read that checker's own reference model. The
flow, its environment, the helpers and the result history are described in
[sim/fv/README.md](../fv/README.md).

## Native coverage-accuracy regression

With the VCS/LSF modules loaded, run **python3 fcov/run_fcov_accuracy.py**
from **sim/**. This focused regression uses the production LSU/dcache/top
monitors to check forwarding ranges, cache update/replacement sampling,
map-response timing, and LSU cross attribution and applicability.
Synthetic fixture results establish monitor behavior, not DUT coverage closure.
Every licensed tool runs through **submit -i** and outputs go to a fresh
**sim/temp/fcov_accuracy_*/** directory. **--check EXISTING_RUN_DIRECTORY**
rechecks the saved native reports without changing them.
Recompile and start fresh campaign databases for these bin/cross changes;
do not merge them into earlier schemas.

## Semantic and temporal coverage regressions

Three further native regressions check monitors added on 2026-10-01. Run
them from **sim/** with the VCS/LSF modules loaded; each uses **submit -i**,
writes only to a fresh **sim/temp/<name>_*/** directory, and accepts
**--check EXISTING_RUN_DIRECTORY** to recheck saved reports.

| Runner / fixture | Coverage checked |
|---|---|
| **run_ex_semantics.py** / **tb_fcov_ex_semantics.sv** | **FC_MA_EX**: shift/rotate amounts and forms, DIV/REM and MULH operand corners, CSetBounds* outcome, rounding, exponent path and length classes; CHERI zero weight on HW0 |
| **run_lsu_semantics.py** / **tb_fcov_lsu_semantics.sv** | **FC_MA_LSU**: reachable request/response CHERI causes, capability-load top/permission/tag conversion, split-access error phase; revocation bit selection, range boundaries and back-to-back outcomes |
| **run_frontend_temporal.py** / **tb_fcov_frontend_temporal.sv** | **FC_MA_ISSUE** forwarding outcome/producer/consumer, branch prediction→resolution→recovery, slot-1 suppression, CHERI temporal stalls; **FC_MA_IF** predictor priority contention |
| **run_issue_sampling.py** / **tb_fcov_frontend_temporal.sv +issue_sampling** | Single **FC_MA_ISSUE** sample isolation, simultaneous events, reset, FSM transitions and RA tracking; optional all-point/cross comparison against the pre-consolidation source |

New illegal bins (CHERI cause encodings and capability tag outcome) each
have an assertion in **kudu_fcov_lsu.sv**. Cross cells that are
structurally impossible (for example an inexact failure on a non-exact
bounds operation, or an immediate ROL) are ignore bins, documented beside
the cross. Detailed goals are in section 4.3 of the
[test plan](../testplan/README.md).

## Additional standalone fixtures

The standalone timing checker defines
**KUDU_FCOV_BUS_TIMING_ONLY** to compile only the covergroup-free helper
with Verilator. Normal coverage builds compile both modules from this single
file. The timing helper's module name and behavior are unchanged.

**tb_fcov_top.sv** exercises the seven occupancy bins by filling a real
depth-eight **dual_fifo** one entry per cycle. Compile **cheri_pkg.sv**,
**csr_pkg.sv**, **super_pkg.sv**, **dual_fifo.sv**, **kudu_fcov_pkg.sv**,
**kudu_fcov_top.sv**, and the fixture in that order, with VCS
**-sverilog +define+CHERIoT -top kudu_top**. Do not include the real
**kudu_top** module or production bind list in this standalone build.
The expected occupancy counts are one each for **0–5** and three for **6+**
(levels 6, 7 and 8). Run in fresh build/report directories through
**submit -i**, with an explicit fresh **-cm_dir** for the simulation.

### Why the binds use `.*`

The coverage modules name their ports after the RTL signals they sample, so
`.*` connects most of them. That is not just brevity, it is the main safety
mechanism:

* With an explicit `.x(x)` where `x` does not exist in the target, **the
  identifier silently becomes an implicit 1-bit net.** The covergroup then
  samples a constant forever and still reports coverage. `` `default_nettype
  none `` does not help, because the implicit net is created in the *target*
  module's scope, not the bind file's.
* With `.*`, a port that has no matching signal is a **hard elaboration
  error**, and a size mismatch raises `-Wimplicit-port-type-mismatch`.

Switching to `.*` immediately found four coverpoints that had been sampling
implicit nets: `cycle2` in `alu_pipeline` and `is_mult` / `is_div` in
`mult_pipeline` are fields of `alupl_reg_t` / `flags_t`, not module-scope
signals, and `nmip` in `cs_registers` is a field of `dcsr_t`.

Connections that rename, index, reduce or reach into a sub-instance still have
to be written out. The checker reports their current count.

`check_binds.py` checks explicit expression roots against source declarations.
Field selection, widths, indices and generate/configuration scopes still
require elaboration with `check_syntax.py --matrix`.

Between them the two tools also catch the other recurring mistake: naming a
signal that exists in the RTL but lives inside a generate block, and so is not
reachable from a bind (`ls_pipeline.dcache_i`, `branch_predict.bht_entry_sel`,
`ir_stage.s0_fifo`). Where that happened, the coverage module binds the
sub-module directly instead of reaching through a configuration-dependent
hierarchical path.

## Bug-driven coverage

The RTL bugs found so far (**sim/testplan/bug_logs*.md**, KUDU-001..074) were
cross-checked against this model in **sim/testplan/fcov_bug_crosscheck.md**.
The resulting additions are listed below by group, with the bugs each one
targets. Existing points were left in place except for the fixes noted.

**Fixes to existing code.** Issuer bind renames **debug_single_step_i** and
**single_step_trap_q** (explicit, commented connections); the missing
parentheses in the **cp_pdt_pc_set** guard; **cp_dbg_entry_src** now separates
haltreq, trigger, ebreak and step entry and their pairwise races (030/040/071),
with the ebreak bin sampling the ebreak entry term rather than the trigger
match;
**cp_step_with_ie** is weight 0 (dcsr.stepie is hardwired, KUDU-029).

| Group | New points / crosses | Bugs |
|---|---|---|
| **FC_MA_ISSUE** | Trap context **cp_tc**, **cp_trap_dm/priv/mie/step**, **x_trap_dm**, **x_trap_mie**, **x_step_trap**; **cp_mtval**, **x_cause_mtval**, **cp_mtval_unexpected**, **cp_trap_pc_odd**; **cp_sysctl***, **x_sysctl_mode**, **x_wfi_tw**, **cp_mret_asr**; **cp_irq_priv/mie**, **x_irq_priv_mie**, **cp_irq_block**, **cp_irq_withdrawn**; **cp_dbg_src_q**, **x_dbg_src_cause**, **x_dbg_ir_valid**; **cp_cheri_dep_class**, **x_cheri_dep_consumer** | 004, 005, 010, 012, 015, 021-023, 026, 028-030, 034-036, 038-041, 051, 071 (072/073 waived: diagnostic only) |
| **FC_MA_IF** | **cp_pdt_en**, **cp_fetch_jal**, **x_jal_pdt_off**; **cp_ra_pdt_fresh** (weight **PredictRA**) | 011, 049 |
| **FC_MA_ID** | **cg_ir_decoder**: **cp_hdrm_win**, **cp_ferr_word**, **cp_ferr_is_comp**, **x_hdrm_fetch_err**; **cg_ma_id**: **cp_b_near_miss0** | 070, 006 |
| **FC_MA_LSU** | **cp_split_bus_err_phase/mtval**, **x_split_err_mtval**; **cp_csr_noasr_cls/out**, **x_csr_asr**; **cp_mshwm_upd_src**; **cp_resp_clrperm_any**, **x_clrperm_dm**; **cp_amo_bus_err_phase/cause**, **x_amo_bus_err_cause**, **cp_amo_cheri_cause** | 008, 017, 018, 024, 032, 037, 052, 061 |
| **FC_MA_LSU** dcache | **cp_inflight_cls/rel/hit**, **x_inflight_fwd**, **x_inflight_cap** (load forwarding while an earlier request is in flight) | 014, 033, 050 |
| **FC_ISA_CSR** | **cp_dbg_csr_wr**, **cp_dbg_wr_pmode**, **x_dbg_csr_pmode**; **cp_save_kind**, **cp_dm_trap_m_write**; **cp_mshwm_wr_to_store**; **cp_minstret_inc**, **cp_mstatush** | 025, 022/027, 016, 019, 042 |

In total 46 coverpoints, 19 crosses and 9 assertions were added. New
connections use **.*** (new ports on **kudu_fcov_csr**, **kudu_fcov_dcache**
and **kudu_fcov_if**, which also gains a **PredictRA** parameter) or direct
hierarchical taps; the stub testbenches carry the matching signals.

**Weight-0 points.** These are diagnostics or tripwires and do not count
toward the score: **cp_step_with_ie**, **cp_minstret_inc** (KUDU-019, open),
**cp_mstatush** (KUDU-042, open), **cp_dbg_src_q**, **x_dbg_src_cause**,
**cp_mtval_unexpected**, **cp_irq_withdrawn** (KUDU-072/073 waived),
**cp_csr_noasr_out**, **cp_resp_clrperm_any**, **cp_amo_bus_err_cause** and
the three **cp_inflight_*** points (their crosses carry the goal). A tripwire
should stay empty until its bug is fixed; then give it weight 1.

**New illegal bins and their assertions.**

| Illegal bin(s) | Assertion | Invariant |
|---|---|---|
| **cp_trap_pc_odd.odd** | **AssertTrapPcEven** | Trap PC is halfword aligned |
| **cp_irq_block.in_debug/stepping** | **AssertNoIrqInDebug**, **AssertNoIrqWhileStepping** | No interrupt taken in debug mode or while stepping |
| **cp_split_bus_err_mtval.other**, **x_split_err_mtval** | **AssertSplitErrMtval** | Split-access bus error reports the faulting half's address |
| **cp_csr_noasr_out.other**, **x_csr_asr** | **AssertCsrNoAsrOutcome** | CSR access outcome matches its ASR class |
| **x_amo_bus_err_cause** | **AssertAmoBusErrCause** | LR reports a load fault, SC/AMO a store fault |
| **x_inflight_fwd.risky_fwd**, **x_inflight_cap.cap_fwd** | **AssertNoFwdBehindRiskyReq** | No load forwarding behind a misaligned, capability or SC request |
| **cp_dm_trap_m_write.written** | **AssertNoMTrapCsrWriteInDebug** | Debug entry or a trap in debug mode leaves mcause/mepc |
| *(none; goal is the illegal decode)* | **AssertBNearMissIllegal** | B-extension near-miss encodings decode as illegal |

**Unreachable-bin closure.** Bins that coverage closure never hit and that
RTL analysis showed to be unreachable became illegal bins. Each has an SVA
twin that JasperGold proves on KuduCfg1 with CHERIoT in PMODE 0 and 1. The
exception is kudu_fcov_isa, which is not in the FV file list, so its
immediate assertions are checked in simulation only.

| Group | Illegal bin(s) | Assertion | Invariant |
|---|---|---|---|
| csr | mpp/priv/dcsr_prv reserved, **cp_entering**, **cp_stepie**, **cp_dcsr_nmip**, **cp_step_with_ie**, **x_dbg_csr_pmode** | **AssertDbgEnteringTiedOff**, **AssertNoDbgCsrWrInPmode** | Tied-off debug inputs and legalised privilege fields |
| csr | **cp_mshwm_wr_to_store.same_cycle** | **AssertNoMshwmCsrWrWithLsuWr** | No MSHWM CSR write in the same cycle as an LSU update |
| alu | **cp_ds.rdy_no_out**, **cp_wb.idle** | **AssertAluDsRdyValid**, **AssertAluWbIdleRdy** | Pipeline ready/valid handshake |
| alu | **cp_auipcc_pcc_tag.untagged**, **cp_auipcc_pcc_cperms.not_executable**, **cp_auipcc_pcc_otype.sealed** | **AssertAuipccPccExecutable** | Outside debug mode AUIPCC's PCC is tagged, unsealed and executable |
| alu | **cp_auipcc_pcc_reserved.set**, **cp_auipcc_pcc_cexp.above_max** | **AssertAuipccPccEncoding** (simulation) | Tagged capabilities never carry the reserved bit or an exponent above 24; this is a memory invariant, so formal with unconstrained memory cannot prove it |
| branch | **cp_jalr_target_low** odd | **AssertSvaBrJalrTargetEven** | JALR target bit 0 is cleared |
| mult | **cp_ds.rdy_no_out**, **cp_ex2.idle**, **cp_wb.idle**, **cp_out_we.no_write** | **AssertMultDsRdyValid**, **AssertMultEx2IdleRdy**, **AssertMultWbIdleRdy**, **AssertMultOutWe** | Pipeline handshake; every mult result writes |
| mult | **x_setbounds_op_rounding.rndn_base_rounded** | **AssertMultRndnBaseExact** | CSetBoundsRoundDown never rounds the base |
| cmplx | **cp_transition** wr_flush, write_hold; **cp_is_amo.not_amo** | **AssertCmplxWriteOneCycle**, **AssertSvaCmplxStart** | AMO write lasts one cycle; the complex unit only runs AMOs |
| lsu | **cp_ds.rdy_no_out**, **cp_flush_busy.hit** | **AssertLsDsRdyValid**, **AssertLsNotBusyAtFlush** | Handshake; no flush while busy |
| lsu | **x_ls_type_2** sc_scalar, align_cached_scalar | **AssertReqScFaultIsCap**, **AssertReqScalarAlignUncached** | Request classification |
| lsu | **cp_resp_early_cheri_cause** store causes, **cp_resp_clrperm.no_mc_keeps_lg_lm**, **x_access_err.cap_illegal**, **cp_tsafe_en.off** | **AssertRespEarlyCheriCauseReachable**, **AssertRespClrpermMcImpliesLgLm**, **AssertIllegalInsnRespNotCap**, **AssertTsafeTiedOn** | LSU response encodings |
| dcache | **x_inflight_fwd.word_st_same_miss** | **AssertWordStSameWordHit** | A word store to the same word hits |
| isa | **cp_rd.x0**, shifted **cp_mem_rmask/wmask**, **cp_target_align.odd**, **cp_mode** 1-3 | **AssertIsaRdX0NoData**, **AssertIsaMemMaskUnshifted**, **AssertIsaTargetEven**, **AssertIsaModeTied** (simulation) | RVFI encodings |
| isa | **tagged_reserved**, **tagged_above_max** in every generated cross with a CS1 reserved or exponent axis | **AssertIsaTaggedCapEncoding** (simulation) | Tagged CS1, CS2 and CD never carry the reserved bit or CEXP 1--6 (exponent 25--30); only CSetHigh sets the reserved bit and its result is untagged |
| isa | **untagged_link** in **x_control_cs1_cd_tag** and **x_control_cd_no_cs1_tag** | **AssertIsaJumpLinkTagged** (simulation) | JAL/JALR and compressed forms in capability mode always write a tagged link capability |
| lsu | **cp_resp_cap_rsvd.set**, **cp_resp_cap_cexp.above_max** | **AssertRespTaggedCapEncoding** (simulation) | A tagged capability returned from memory never carries the reserved bit or CEXP 1--6 |
| id | **cp_flush.one_sided** (cp_hold removed) | **AssertIrFlushBothOrNone**, **AssertIrHoldTiedOff** | Both IR flushes come from pc_set; ir_hold is tied off |
| if | **cp_busy.split**, **cp_redirect_align.misaligned**, **x_cp_pdt_priority_contention.src_ne_cand0** | **AssertIfBusyEqPrefetchBusy**, **AssertRedirectTargetEven**, **AssertPdtSrcMatchesCand0** | Wiring, even redirect targets, slot-0 PDT priority |
| issue | **cp_producer.multi**, **cp_fwd_to_slot.ir1** | **AssertFwdActOneProducer**, **AssertIr1FwdSubsetIr0** | One forwarding producer per register |
| issue | **x_operand_outcome_issue** raw_stall/same_bundle issued, **x_cheri_temporal_issue.stall_issued**, **cp_waw_hazard.ir0_waw** | **AssertIssuedOperandsReady**, **AssertCheriHazardNotIssued**, **AssertNoIr0WawHazard** | No issue over a hazard (AllowWaW=1) |
| issue | **cp_recovery.pc_set_with_alt**, four **x_prediction_resolution_recovery** groups | **AssertAltFlushOnPcSet**, **AssertBpResolutionRecovery** | Mispredict recovery path (AltEnable=1) |
| issue | **cp_fsm_trans.t_bad**, **cp_dbg_src_q.none**, five **x_dbg_src_cause** groups | **AssertFsmTransLegal**, **AssertDbgCauseFromSrc** | Controller FSM edges and debug-cause priority |

kudu_fcov_issue takes the **AllowWaW** and **AltEnable** parameters from
issuer through the bind. The configuration-dependent illegal bins use
**with (...)** guards. They become normal bins when the parameter is off,
for example **ordinary_pc_set** on KuduCfg2.

## Illegal bins

Structural assertions accompany the illegal bins. Keep new illegal bins and
their assertions aligned; do not turn a forbidden value into a normal coverage
goal. Both mechanisms are disabled by `KUDU_FCOV_OFF`. Historical finding IDs
refer to the unavailable plan, not an independently checked current invariant.

An illegal bin must encode an invariant of the *design*, not of the modeller's
reading of it. Four classes of mistake produced false failures here and are
worth checking against before adding a new one:

* **`pl_sel` is not one-hot.** Bit 0 selects the branch unit and bits 4:1 are a
  one-hot execution-pipeline select (`issuer.sv:221-222`). `select_pl`
  (`issuer.sv:133-158`) pairs the two for jumps, so `5'h03` (JAL/JALR + alu0),
  `5'h05` (JAL/JALR + alu1) and `5'h11` (CHERIoT CJALR + mult, which needs the
  mult pipe for the bounds check) are normal encodings. The scoreboard stores
  the raw `pl_sel`, so the same encodings reach `FC_MA_CMT`. Only `pl_valid_st`
  and `pl_err_st` in the committer have bit 0 tied low.
* **Raw per-slot decodes are not arbitrated outputs.** `pdt_pc_set` (`FC_MA_IF`)
  and `ir_any_err` / `ir_hazard` (`FC_MA_ISSUE`) are combinational decodes of
  both slots; the consumer applies the priority. Both bits set at once is the
  dual-candidate case, not an error. Assert the arbitration guarantee that
  makes it safe instead — for `pdt_pc_set` that is
  `AssertSlot0RedirectWins`, not "at most one slot requests a redirect".
* **A stored control value is not an index.** `ir0_raw_cause` / `ir1_raw_cause`
  look like register numbers but `reg_wrsv_cause[]` holds the *`pl_sel` of the
  producing instruction* (`issuer.sv:1108-1121`), and the cause is the bitwise
  OR of the rs1 and rs2 entries (`issuer.sv:1126-1127`), so a consumer waiting
  on two pipelines yields a multi-hot mask such as `5'h06`. There is no legal
  value set to police here at all; the one-hot-zero invariant belongs on
  `cp_pl_sel_ir0/ir1`, where the value is produced. Read the signal's driver
  before trusting its name.
* **The guard must be the cycle the value is valid, not the cycle it is
  requested.** `cp_dbg_cause_sel` sampled `debug_cause_o` on `handle_debug`, but
  `handle_debug` is the request that makes the control FSM enter the debug
  special case, and `debug_cause_o` is only driven once it is *in* that state
  (`issuer.sv:940-952`). Every sample read the default `DBG_CAUSE_NONE`. The
  guard is `ctrl_fsm_cs[CSM_ISSUE_SPECIAL] & (special_case_q == DEBUG)`. A
  cause that is latched from a request can also go stale, so `NONE` is a real
  bin there rather than an illegal one.
* **A `valid` strobe may have terms outside the sampled concatenation.**
  `cp_sysctl0` sampled six of the seven decode terms that make up
  `sysctl.valid` (`ir_decoder.sv:127-137`); the missing one, `csrw`, made every
  `csrw mstatus/mie` sample as all-zero and hit `illegal_bins multiple`. When a
  coverpoint is guarded by a `valid` that is an OR, sample *every* term of that
  OR — and check the matching assertion for the same omission.

## Bin ranges and `$countones`

`$countones` returns `int`, so an open-ended `bins more = {[4:$]}` covers the
whole signed 32-bit range. VCS discards it with `Warning-[PSBU] Invalid values
in bin` and the bin disappears from the report — the same silent coverage loss
that the `.*` binds exist to prevent. Bound such coverpoints with the width
parameter (`{[0:PrefetchDepth]}`), which also avoids leaving permanently
unreachable bins in configurations where the vector is narrower.
