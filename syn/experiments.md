# Synthesis experiments

These are exploratory timing/area experiments, not signoff results. RTL variants
are kept in isolated scratch directories. Only Experiment 3 (**FlatFetchAddrMux**)
has been promoted into **rtl/**.

## Default for future Kudu synthesis work

Use Fusion Compiler synthesis followed by post-placement optimization through
**final_opto**. Compare baseline and variant using the same tool, libraries,
physical setup, optimization stage, and constraints.

A wireload-only rebaseline was considered, but the loaded MTK028LP libraries
contain only **ZeroWireload**, whose fanout lengths are all zero. The requested
flow was subsequently switched back to post-placement optimization. The results
below are physical-flow estimates, not wireload-only benchmarks. In particular,
the -0.3075 ns reference is from **final_opto**, not the earlier **logic_opto**
checkpoint.

The flow is deterministic for identical input, but logically equivalent RTL
with trivially different structure moves the result by about 0.04 ns (one
standard deviation) in worst slack and about 500 um^2 in area (see the noise
study in Experiment 3). A single baseline/variant pair cannot resolve changes
smaller than about 0.1 ns. Compare at least four equivalent variants per side,
for example by renaming the **kudu_top** instances with different seeds.

## Fusion setup

| Item | Setting |
|---|---|
| Core | KuduCfg1 (Experiment 4 also KuduCfg2), CHERIoTEn=1, UseDWMult=1; CJALR errors remain enabled |
| Tool | Fusion Compiler X-2025.06-SP2, invoked through **submit -i** |
| Libraries | Existing syn028lp MTK028LP setup, SS 1.035 V, 125 C |
| Synthesis | **compile_fusion -to logic_opto** |
| Post-placement optimization | **compile_fusion -from initial_place -to final_opto** |
| Effort | Default optimization effort; two tool cores per case |
| Clock | 2 ns / 500 MHz (Experiment 4 also 3 ns / 333 MHz) |
| Memory-data input arrival | 1.5 ns on all 65 data and 64 instruction bits |
| Other timed inputs and outputs | 0.6 ns |
| Initial floorplan | Square, 60% utilization, unit7 rows, 5 um core offsets |
| Physical setup | Pins on METAL3/METAL4; estimated routing on METAL2..METAL6 |
| Interconnect | Existing MTK028LP rcbest/rcworst TLU+ estimates |

Area is mapped standard-cell area in um^2, not core area or gate equivalents.
There are no added input driving cells/slews, output loads, or clock uncertainty.
Reset and the original static boot address, hart ID, and CHERIoT mode false paths
are retained. No experiment-specific timing exceptions or relaxed I/O delays
were added.

Fusion's native CCD/planned sink clock latencies are retained. They are not an
implemented clock tree. These results have no real CTS, detailed routing,
SI/OCV, or hold/reset signoff and must not be interpreted as zero-skew timing.

## Experiment 1: Registered one-hot forwarding destination

### Hypothesis and implementation

The baseline worst path starts at the D-cache's five-bit forwarding destination
tag and ends at the instruction-address output. The hypothesis was that
registering the destination predecode could shorten this control cone without
adding pipeline latency.

Two variants were compared with an unchanged, freshly synthesized baseline:

- **hazard_oh:** capture 31 nonzero destination decode bits whenever
  **fwd_info_o.addr1** is captured, then gate them with the existing forwarding
  validity. Destination capture, hold, invalidation, and WAW cancellation timing
  are unchanged.
- **operand_oh:** additionally use the registered one-hot mask, indexed by the
  source register, for LSU operand-hit matching in **issuer**. Other forwarding,
  capability checks, branch resolution, and redirect logic are unchanged.

Both placed variants retain 31 actual one-hot destination registers.

### Measured results

Worst slack includes all reported path groups. Negative slack fails setup at
the requested 500 MHz target.

| Variant | Cell area (um^2) | Area change | Worst slack (ns) | REG2REG (ns) | DMEM2REG (ns) |
|---|---:|---:|---:|---:|---:|
| Baseline | 77,080.33 | - | -0.3075 | -0.2324 | -0.0474 |
| Hazard-only registered decode | 76,820.53 | -0.337% | -0.3144 | -0.2005 | -0.0533 |
| Also reuse decode for operand matching | 79,034.16 | +2.535% | -0.3074 | -0.2169 | -0.0882 |

The fresh baseline reproduced the earlier Cfg1 area and worst slack exactly.
All final clock and I/O delay constraints were checked identical.

The hazard-only variant leaves the binary operand-match path in place:
its worst binary-tag-to-fetch slack is **-0.3079 ns**, through 35 combinational
cells. Its new one-hot-to-fetch path is shorter, at **-0.2035 ns**, but the
remaining binary path prevents an overall improvement.

Reusing the decode for operand matching removes the direct binary-tag-to-fetch
paths. However, the replacement path from **fwd_rd_oh_q_reg[18]** to
**instr_addr_o[6]** still contains 38 mapped combinational cells and has
**-0.3031 ns** slack. The baseline tag-to-fetch path contains 35 cells with
**-0.3075 ns** slack. Both targeted paths have the same 0.0600 ns estimated
launch-clock latency. Source selection, forwarded-data selection, and downstream
branch/redirect logic remain.

The hazard-only variant's overall worst path moves to the multiplier writeback
destination tag; the operand-reuse variant's worst path moves to ALU1 capability
result address bit 12, ending at **instr_addr_o[28]**.

### Electrical and functional checks

The baseline and operand-reuse variant have no max-transition or
max-capacitance violations. The hazard-only variant has no transition violations
and one capacitance violation: **ls_pipeline_i/ctmn_50937**, driven by
**ls_pipeline_i/ctmi_60685/O**, reports 0.0224 pF required and 0.0225 pF actual.
Its negative slack rounds to -0.0000 pF in the source report; no unrelated repair
was attempted.

RV32 and CHERIoT focused simulations each passed 262,144 operand-lookup
combinations and 10,258 D-cache state checks, including all 32 destinations,
x0, hold cycles, WAW cancellation, reset, and randomized state transitions.

All 36 CPU simulations passed: 12 tests per case, covering ISA tests with
default/delayed memory, CHERIoT CoreMark, RV32 runtime mode, RV32 hardware without
CHERIoT, and self-checking load/store/AMO riscv-tests. Both variants' raw and
cleaned traces and cycle counts exactly match the baseline. This is
simulation-based validation, not a formal-equivalence proof.

The scratch simulation setup uses per-run program-directory links and an
explicit **KUDU_DW_MULT=1** in copied file lists. Initial setup-only runs were
cancelled and retained separately; they are not counted as passes.

### Conclusion and artifacts

**No meaningful worst-case timing improvement.** Hazard-only predecode is
6.9 ps worse. Operand reuse is effectively unchanged at 0.1 ps better at the
reported precision, while increasing cell area by 2.535%. Neither variant is
recommended for promotion on these results.

Artifacts:
**/home/scratch/fortress/kunyanliu/cfg1_onehot_20261117T0444Z.KhKB78/**

The **final_results/** subdirectory contains **summary.txt**, **summary.csv**,
**summary.json**, **interpretation.txt**, the two RTL source patches, functional
comparison results, and input/constraint provenance. Full timing reports,
physical checkpoints, and simulator logs remain under **cases/**.

## Experiment 2: Parallel JALR target addition

### Hypothesis and implementation

Move the JALR immediate addition ahead of forwarding selection: add the
sign-extended immediate to each candidate address in parallel, then select the
target using the existing destination-tag matches. This exchanges arithmetic
area for a potentially shorter tag-to-target control path.

Only scratch copies of **branch_unit.sv** and **kudu_top.sv** change. The branch
unit receives raw RF rs1 addresses and the four pipeline forwarding records.
For Cfg1, the four slot-0 forwarding valids are constant zero. Consequently,
there are five active address candidates per instruction slot: RF, ALU0 WB,
ALU1 WB, LSU WB, and multiplier WB. Across both instruction slots this gives
ten active candidate-addition expressions instead of the original two target
additions, before synthesis factoring and optimization.

x0 handling, 32-bit wraparound, and clearing target bit 0 are preserved. Full
capability prediction comparisons, CJALR error generation, branch decisions,
issue logic, and pipeline latency are unchanged. A named unpacked forwarding
array is used because Fusion PRESTO rejects the initial inline port assignment
pattern; both versions have identical **branch_unit.sv** arithmetic.

### Measured results

These are completed **final_opto** results under the setup above. The unchanged
baseline reuses Experiment 1's physical result; its RTL hashes were checked
against this experiment's baseline. Final clock, input/output delays, and false
paths were checked identical, including every memory-data input bit.

| Variant | Cell area (um^2) | Area change | Worst slack (ns) | REG2REG (ns) | DMEM2REG (ns) |
|---|---:|---:|---:|---:|---:|
| Baseline | 77,080.33 | - | -0.3075 | -0.2324 | -0.0474 |
| Parallel JALR target addition | 78,770.73 | +2.193% | -0.3163 | -0.2216 | -0.0522 |

The variant costs **1,690.40 um^2** and has **8.8 ps worse worst-case slack**.
REG2REG improves by 10.8 ps, but neither design meets the overall 500 MHz target.
Both have zero reported max-capacitance and max-transition violations.

### New critical path

Both worst paths are **REG2OUT** paths ending at the instruction-address output:

- Baseline: **ls_pipeline_i/genblk1.dcache_i/fwd_info_o_reg[addr1][3]**
  to **instr_addr_o[9]**, with -0.3075 ns slack.
- Parallel JALR: **alu_pipeline0_i/wb_reg_reg[rd][0]**
  to **instr_addr_o[6]**, with -0.3163 ns slack.

The new startpoint is an ALU0 **destination-tag bit**, not payload data: its Q
output drives **alupl0_fwd_info[addr1][0]**. Thus forwarding selection/control
still limits the fetch-address path after parallelizing target arithmetic.
The experiment does not remove tag matching, full-capability comparisons, or
downstream redirect decisions.

The baseline reports 1.7075 ns arrival with 0.0600 ns estimated launch-clock
latency; the variant reports 1.7163 ns with 0.0400 ns launch-clock latency.
Both require arrival by 1.4000 ns because of the 0.6 ns output delay. Native
planned-clock estimates differ, so this is not a controlled zero-skew comparison
of combinational logic alone. Excluding those launch-clock estimates gives
1.6475 ns and 1.6763 ns respectively, including clock-to-Q and the estimated
cell/net path. This single physical comparison demonstrates no timing benefit;
it is not signoff or a statistical placement study.

### Functional validation and limitation

The original forwarding lookup ORs matching payloads. Selecting an OR of
independently added targets is generally equivalent only with at most one
nonzero-register forwarding hit. For example, matching payloads 1 and 2 with
immediate 1 produce aligned targets 4 in the original expression and 2 in the
parallel expression. No exclusivity assumption was added to synthesis or timing
constraints.

Source-derived RV32 and CHERIoT focused miters each passed **1,179,648 vectors**,
covering register/immediate selection, forwarding alternatives, x0, alignment,
overflow, and unchanged branch/error outputs. Full-core live assertions checked
hit exclusivity and target equivalence at valid decoded slots, including stalls;
none failed. This is simulation evidence, not a formal invariant or equivalence
proof.

Five baseline/variant CPU pairs passed with identical raw and cleaned trace
hashes, cycle counts, live-check counts, and forwarding-source counts:

| Test | Mode | Cycles in both designs |
|---|---|---:|
| isa_test1, default memory | CHERIoT | 7,028 |
| isa_test1, delayed memory | CHERIoT | 13,865 |
| isa_test1a, default memory | CHERIoT | 1,698 |
| jalr_parallel, default memory | RV32 runtime mode | 25,197 |
| jalr_parallel, delayed memory | RV32 runtime mode | 47,232 |

All five pairs use the CHERIoT-capable core with **UseDWMult=1**; the directed
RV32 cases select **PMODE=0**. Each directed run checks 3,072 issued JALRs and
requires an explicit **JALR PARALLEL PASS** plus UART termination. Together they
exercise RF and all four active WB sources, including LSU forwarding, in both
designs. Delayed runs set all four memory wait maxima to 3.

The initial broad sweeps exhausted their 90-minute limits waiting for VCS
licenses, after four baseline and three variant passes. Those completed runs
were recovered rather than repeated, then supplemented by the two directed
tests per design. The extra baseline-only **isa_test1a.memdly** also passed, but
is not counted as a matched pair. The planned broad regression did not complete.

### Conclusion and artifacts

**No demonstrated worst-case timing improvement for +2.193% cell area.** Keep
this as a scratch experiment rather than promoting it into repository RTL.

Artifacts:
**/home/scratch/fortress/kunyanliu/cfg1_jalr_parallel_20261117T0900Z.S33W97/**

The **final_results/** directory contains the matched **summary.csv**,
**summary.json**, **summary.txt**, **tradeoff.json**, RTL **parallel.diff**,
constraint/source provenance, actual-trace comparisons, forwarding-source
coverage, the multi-hit counterexample, and license-limited job records.
**common/finalize_placed_experiment.py** performs the final audit.
Full timing paths are in each case's **placed/reports/timing_REG2OUT.rpt**;
**cases/baseline/placed/** refers to the verified earlier baseline.
The frozen synthesis recipes are **common/synthesize.tcl** and
**common/physical.tcl**. All failed, partial, and completed run artifacts are
preserved. Repository RTL remains unchanged.

## Experiment 3: Flattened fetch-address mux (FlatFetchAddrMux)

### Hypothesis and implementation

After the CSR write-enable fix, the worst path was still **REG2OUT** into
**instr_addr_o**. In **prefetch_buffer64.sv** the address is a priority mux,
**valid_req_q ? stored_addr_q : branch_i ? comb_target : fetch_addr_q**, and
**comb_target** is itself a chain of muxes selected by the late redirect
controls (ALT redirect, the execute PC set, then the predecode PC set). The
hypothesis was that flattening the whole selection into one AND-OR, with the
late selects acting only at the last level, would shorten that path.

The flat mux ORs seven sources, each gated by a one-hot select:
**stored_addr_q**, the two ALT next addresses read directly from the
**fetch_fifo64** ALT table, the predecode target, the seven per-source execute
targets, and **fetch_addr_q**. To support it, **issuer** exports its target
select and data (**pc_tgt_sel_o** / **pc_tgt_data_o**), and **fetch_fifo64**
exports the ALT-table next addresses. **pc_target_o** is still used for
**fetch_addr_d**, the fetch FIFO input address and simulation checks.

The change is selected by **localparam bit FlatFetchAddrMux = 1'b1** in
**kudu_top.sv**, passed down through **issuer**, **if_stage**,
**prefetch_buffer64** and **fetch_fifo64**. Setting it to 0 restores the
original mux. With 0, the new **issuer** and **fetch_fifo64** outputs are tied
to zero and **prefetch_buffer64** XOR-reduces the unused inputs.

### Equivalence and functional checks

Conformal LEC 26.10-s300 (RTL to RTL, **kudu_lec_top** wrapper, CHERIoTEn=1,
UseDWMult=0, synthesis CFG, SYNTHESIS and CHERIoT defined) passed in all three
comparisons, with 11,134 equivalent points (159 POs, 10,974 DFFs, 1 DLAT) and
none non-equivalent, aborted or not compared:

- Original RTL vs unparameterized flat RTL.
- Original RTL vs FlatFetchAddrMux=1 and vs FlatFetchAddrMux=0.
- FlatFetchAddrMux=0 vs FlatFetchAddrMux=1 (final repository RTL).

The single DLAT is **lsu_if.sv** **lsif_fsm_q[2]**: a 3-bit enum whose states
0-3 never set bit 2, so Conformal models the constant bit as a disabled-clock
latch. The RTL has no latches.

Simulation: the unparameterized flat RTL passed the full regression
(**310 PASS, 0 FAIL, 7 XFAIL**, the XFAILs being known bugs KUDU-042 and
KUDU-019). It included a simulation-only checker comparing the flat mux with
the original expression on every cycle; it never fired. The parameterized RTL
compiled without warnings at both settings and passed ten sanity tests, with
byte-identical traces at FlatFetchAddrMux=0 and 1. The checker was removed
after LEC passed.

### Measured results and noise study

The first unparameterized pair suggested a large gain:

| Run | REG2OUT (ns) | REG2REG (ns) | INPUT2OUT (ns) | Area (um^2) |
|---|---:|---:|---:|---:|
| CSR fix, original mux | -0.29 | -0.21 | -0.08 | 76,264.7 |
| CSR fix, flat mux | -0.17 | -0.16 | -0.13 | 75,633.5 |

Identical reruns of both reproduced every number exactly. However, the
parameterized repository RTL, which is LEC-equivalent to the flat run, gave
-0.29 ns and 77,197 um^2, and FlatFetchAddrMux=0 gave -0.21 ns.

To measure the noise, both settings were synthesized four more times with the
twelve **kudu_top** instance names renamed by a seeded hash (same seed for both
settings). With the original and repository runs this gives six equivalent
samples per side:

| Run | Mux | REG2OUT | REG2REG | INPUT2OUT | Total TNS | Area (um^2) |
|---|---|---:|---:|---:|---:|---:|
| original | old | -0.29 | -0.21 | -0.08 | -17.10 | 76,264.7 |
| repo | old | -0.21 | -0.18 | -0.09 | -15.46 | 76,611.3 |
| seed 1 | old | -0.31 | -0.19 | -0.14 | -20.82 | 77,239.6 |
| seed 2 | old | -0.27 | -0.18 | -0.15 | -20.71 | 77,159.1 |
| seed 3 | old | -0.22 | -0.18 | -0.11 | -19.80 | 76,196.5 |
| seed 4 | old | -0.28 | -0.20 | -0.07 | -16.48 | 77,048.3 |
| original | flat | -0.17 | -0.16 | -0.13 | -12.39 | 75,633.5 |
| repo | flat | -0.29 | -0.20 | -0.14 | -21.43 | 77,197.2 |
| seed 1 | flat | -0.23 | -0.18 | -0.11 | -20.55 | 77,371.4 |
| seed 2 | flat | -0.26 | -0.19 | -0.11 | -18.25 | 77,069.3 |
| seed 3 | flat | -0.28 | -0.19 | -0.15 | -23.14 | 76,638.1 |
| seed 4 | flat | -0.25 | -0.21 | -0.13 | -19.14 | 76,980.8 |

REG2OUT is the overall worst slack in every run. Mean ± standard deviation:

| Metric (n=6) | Old mux | Flat mux |
|---|---:|---:|
| REG2OUT / worst slack (ns) | -0.263 ± 0.040 | -0.247 ± 0.043 |
| REG2REG (ns) | -0.190 ± 0.013 | -0.188 ± 0.017 |
| Total TNS (ns) | -18.4 ± 2.3 | -19.2 ± 3.7 |
| Area (um^2) | 76,753 ± 460 | 76,815 ± 629 |

Paired by seed, the flat-minus-old REG2OUT difference ranges from -0.08 to
+0.12 ns, with mean +0.017 ns and a 95% interval of about -0.07 to +0.10 ns.

### Interrupt input-delay check

Assuming the interrupt inputs are flopped outside the core, the 18 **irq_*_i**
ports were given a 0.4 ns input delay instead of 0.6 ns (the flow's
**relax_input_ports** option), on the FlatFetchAddrMux=1 repository RTL. The
irq paths left the 30 worst INPUT2OUT paths, and the worst INPUT2OUT path
became **data_rvalid_i** to **instr_addr_o** (-0.14 to -0.11 ns). The other
groups moved by amounts within the noise above (REG2REG -0.20 to -0.22 ns,
area +1,112 um^2). The repository constraints are unchanged.

### Conclusion and artifacts

**The flat fetch-address mux gives no measurable timing or area benefit.** The
first -0.17 ns result was a favourable noise sample. The change is kept in
**rtl/** with FlatFetchAddrMux=1 as an equivalent alternative structure. Any
real effect is below this flow's resolution of about 0.1 ns.

The same caveat applies to the other single-pair results in this file,
including the CSR write-enable fix (REG2REG -0.23 to -0.21 ns on one pair).

Artifacts under **/home/scratch/fortress/kunyanliu/**:

- **cfg1_fetch_flat_20261119T043036/**: unparameterized flat RTL, its
  synthesis and rerun, the CSR-fix rerun, and sanity simulations.
- **lec_fetch_flat_20261119T141429/**: LEC of the unparameterized change.
- **flat_regression_20261119T135710/**: full regression of the flat RTL.
- **cfg1_fetch_param_20261119T145551/**: parameterized RTL, **fetch_param.diff**,
  LEC (**lec_p1**, **lec_p0**, **lec_p0_vs_p1**) and sanity simulations.
- **cfg1_irq_relax_20261119T164242/**: repository RTL at FlatFetchAddrMux=1
  (**repo_rtl**) and 0 (**repo_p0**), and the interrupt input-delay run.
- **cfg1_noise_20261119T195242/**: the eight seeded variants, **perturb.py**,
  **summarize.py** and **summary.txt**.

## Experiment 4: KuduCfg1 vs KuduCfg2

### Configurations

Both use repository RTL at commit **9670aff** (FlatFetchAddrMux=1), the Fusion
setup above, CHERIoTEn=1 and UseDWMult=1. They differ only in the **CFG**
parameter from **rtl/kudu_cfg_pkg.sv**:

| Field | KuduCfg1 (5-stage) | KuduCfg2 (4-stage) |
|---|---|---|
| IfRdataBypass | 0 | 1 |
| IrStageBypass | 2'b01 | 2'b10 |
| IfCompDecEn / IrCompDecEn | 0 / 1 | 1 / 0 |
| PredictUseBtb | 0 | 1 |
| PredictBhtSize | 32 | 16 |
| PredictRA | 1 | 0 |
| PrefetchDepth | 3 | 2 |
| IrS0Depth | 4 | 2 |
| AltEnable | 1 | 0 |

The packed values passed to Fusion are:

- Cfg1: **315'h60000000000001002100000021000002200000005b940000001000000041400202000000000000f**
- Cfg2: **315'h60000000000001002100000021000002200000005be80000000a000000204002020000000000009**

Both were computed from the struct definition; the computation reproduces the
Cfg1 value used in all earlier experiments.

Following the noise study in Experiment 3, each configuration was synthesized
four times: the unmodified RTL plus **kudu_top** instance-rename seeds 1-3. The
Cfg2 seeds use the same names as the Cfg1 seeds. Cfg2 was run at 2.0 ns and
again at 3.0 ns (333 MHz). At 3.0 ns, both **clk** and **io_vclk** use the new
period and the I/O delays keep the same absolute values: 1.5 ns on instruction
and data read data, 0.6 ns on other inputs and all outputs.

### Results

Placed (**final_opto**) results, mean ± standard deviation of four runs:

| Metric | Cfg1, 2.0 ns | Cfg2, 2.0 ns | Cfg2, 3.0 ns |
|---|---:|---:|---:|
| Worst slack (ns) | -0.265 ± 0.026 | -0.965 ± 0.006 | **-0.022 ± 0.010** |
| Total TNS (ns) | -20.8 ± 2.0 | -507 ± 95 | **-0.30 ± 0.24** |
| REG2OUT WNS (ns) | -0.265 | -0.850 | -0.005 |
| REG2REG WNS (ns) | -0.190 | -0.712 | -0.013 |
| INPUT2OUT WNS (ns) | -0.13 | -0.97 | -0.02 |
| IMEM2REG WNS (ns) | +0.34 | -0.60 | 0.00 |
| Cell area (um^2) | 77,069 ± 313 | 82,845 ± 796 | **56,679 ± 300** |
| Sequential cells (unmodified run) | 9,606 | 8,407 | 8,183 |

Per-run worst slack (ns) / area (um^2):

| Run | Cfg1, 2.0 ns | Cfg2, 2.0 ns | Cfg2, 3.0 ns |
|---|---:|---:|---:|
| unmodified | -0.29 / 77,197 | -0.97 / 81,981 | -0.02 / 56,527 |
| seed 1 | -0.23 / 77,371 | -0.96 / 83,625 | -0.03 / 57,037 |
| seed 2 | -0.26 / 77,069 | -0.97 / 82,365 | -0.01 / 56,797 |
| seed 3 | -0.28 / 76,638 | -0.96 / 83,409 | -0.03 / 56,354 |

### Critical paths

Cfg2's worst paths have the same structure at both periods:

- **INPUT2OUT:** **instr_rdata_i** to **instr_addr_o**. Instruction read data
  feeds the next fetch address in the same cycle. At 2.0 ns the I/O delays
  alone (1.5 + 0.6 ns) exceed the period, so this path cannot close.
- **IMEM2REG:** **instr_rdata_i** to the **ir_stage** stage-0 FIFO
  (**gen_stage0_direct.s0_fifo**), which has only 0.5 ns at 2.0 ns.
- **REG2OUT / REG2REG:** the stage-0 FIFO to **instr_addr_o** and to the
  **cheri_alu** operand registers (**imd_fcap_q**, **ptrmi9_q**).

Cfg1's worst paths are listed in Experiments 1-3; they end at **instr_addr_o**
and **cheri_alu imd_fcap_q** but start from execute/writeback registers.

### Conclusion and artifacts

At 2.0 ns, Cfg2 misses timing by almost 1 ns and is 7.5% larger than Cfg1,
because the tool upsizes and buffers to chase unreachable paths. At 3.0 ns
(333 MHz), Cfg2 essentially closes: the remaining -0.01 to -0.03 ns is
within the flow's noise, and a 3.05 ns period would probably close
cleanly. Its area is then **26% smaller** than Cfg1 at 2.0 ns.

Cfg2 therefore trades about 33% of clock frequency for about 26% less cell
area. Which is faster overall depends on Cfg2's cycles per instruction, for
example on CoreMark, which was not measured here. These results use the same
memory-timing assumption (read data at 1.5 ns) for both configurations; a
memory that returns instruction data earlier would favour Cfg2.

Artifacts under **/home/scratch/fortress/kunyanliu/**:

- **cfg2_synth_20261123T181128/**: Cfg2 at 2.0 ns, with **summary.txt**
  (including the four Cfg1 runs).
- **cfg2_3ns_20261124T133523/**: Cfg2 at 3.0 ns, with **summary.txt**, and
  **common/synthesize.tcl** showing the period change.
- Cfg1 runs: **cfg1_irq_relax_20261119T164242/cases/repo_rtl** and
  **cfg1_noise_20261119T195242/cases/p1_v1..v3**.
