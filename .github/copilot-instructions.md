# cheriot-kudu

32-bit RISC-V microcontroller RTL (SystemVerilog) plus its simulation, formal and
synthesis environments. In-order, dual-issue, 5-stage pipeline, RV32IMC(+B, +A),
with the CHERIoT extension. Setting `cheri_pmode_i = 0` at run time disables all
CHERIoT behaviour and gives a backward-compatible RV32 core.

Verification is simulation-based: run the DUT, dump an instruction trace, and diff it against a
golden trace (cheriot-ibex or the cheriot-sail model).

## Tool access and file-change permission

Do not ask for conversational approval before running any tool or command:
reading and searching files, fetching public URLs, building test programs,
compiling, simulating, running regressions or scripts, and creating scratch
files under `/home/scratch/fortress/kunyanliu/` or a script's own fresh
output directory. This
preference applies across sessions in this repository.

The exception is changing the repository or the RTL: never modify tracked
files, anything under `rtl/`, or git state (commit, amend, reset, checkout,
stash, branch) without the user's explicit approval for that change.

Tool access is not blanket permission to modify files. Limit edits to changes
the user explicitly requested; ask before modifying unrelated files or replacing
existing results, logs, or databases. Run builds and simulations in fresh,
isolated output directories so they do not overwrite existing artifacts. The
data-protection rules below still apply.

These instructions govern assistant behavior, not CLI permission enforcement.
Do not bypass CLI-generated approval prompts or change permission settings
without an explicit request.

## Never destroy the user's data

**Never delete, overwrite, move or truncate anything outside sim/ area and its subdirectories, without explicitly ask for permission.  ** This is absolute; 
**Never delete or overwrite the run_dii/cov_kudu.vdb database without explicitly ask for permission.

Never open a verification or debug script with `rm -rf`.

## Keep temporary files on the scratch disk

The home directory (which holds this repository, including `sim/temp/`) has a
disk quota. Never create scratch, temporary or verification files (scripts,
logs, test fixtures, build directories, simulation runs, traces, reports,
databases) anywhere under the home directory, including `sim/` and
`sim/temp/`. Put them in a fresh subdirectory of the scratch disk
`/home/scratch/fortress/kunyanliu/` (e.g.
`/home/scratch/fortress/kunyanliu/<task>_<time>/`). This applies to every
compile (`./vcscomp -outdir=<scratch dir>`), simulation, regression work
directory (`--work_dir`), `urg` report, subagent work area and one-off helper
script. Scripts that must run from their own directory still run there; only
their output goes to scratch. `sim/temp` is a symlink to
`/home/scratch/fortress/kunyanliu/kudu_temp/`, which holds the earlier review,
regression and reproducer directories cited in `sim/testplan/*.md`. Scripts
that default to `sim/temp/` therefore already write to scratch; never replace
that symlink with a real directory.

## Layout

| Path | Contents |
|---|---|
| `rtl/` | The DUT. Flat directory, one module per file. |
| `prim/` | OpenTitan `prim_*` primitives and assertion macros. |
| `sim/run/` | Main VCS area: compile scripts, file lists, regressions, `bin/` test images. |
| `sim/run_dii/` | Remote/LSF DII (direct instruction injection) runs against archived ELFs, with accumulated coverage. |
| `sim/run_ibex/`, `sim/icache/` | cheriot-ibex builds used to produce golden traces. |
| `sim/run_misc/` | Standalone block-level testbenches (FIFOs, mult, `lsu_if`, `cap_ex`). |
| `sim/tb/` | Testbench: `tb_kudu_top.sv`, memory models, stats/logging modules. |
| `sim/fcov/` | Functional coverage model (bind-based). Has its own README — read it before touching coverage. |
| `sim/tests/` | Test program sources plus linker scripts; built into `sim/run/bin/`. |
| `sim/scripts/` | Build and trace-comparison tooling. |
| `sim/verilator/` | Verilator flow (no coverage support). |
| `fv/` | JasperGold formal (`run_jg`, `fv_*.tcl`). |
| `model/`, `syn/`, `misc/`, `bak/` | Python performance models, Design Compiler scripts, scratch. |

## Environment

VCS, Verdi and `urg` come from modules. `sim/run_dii/load_module_vcs` is the
reference list:

```
module load tools/synopsys/vcs/Y-2026.03-SP1
module load tools/python/python3/3.9.2
module load tools/gnu/gcc/13.2.0
module load lsf
```

Compiler paths for building test programs live in `sim/scripts/common_setup.sh`
(CHERIoT LLVM/clang for CHERIoT tests, riscv-gnu GCC for plain RV32).

File lists reference `$rtlRoot`, `$verifRoot` and `$dwRoot`. Every compile script
exports these itself; the paths are relative to the directory the script runs
from, so **always invoke the scripts from their own directory**.

### Run every VCS job through `submit -i`

Synopsys licences are not reachable from an interactive login shell — `vcs` and
`simv` fail there with `Cannot connect to the license server`. **Prefix every VCS
compile and every simulation run with `submit -i`** so it executes on the LSF
farm, which has licence access:

```
cd sim/run
submit -i ./vcscomp -cov
submit -i ./simv +TEST=isa_test1
```

`submit -i` runs the job interactively and streams its output back, so it is a
drop-in prefix. It applies to `vcs`, `simv`/`simv32`, `urg`, `verdi`, the
regression scripts and `run_dii_rvfi.py` alike. Useful options: `-m <GB>` for
memory, `-t <minutes>` for a kill timeout, `-o <file>` to capture output.
Commands that do not touch a licence (`clean_trace.pl`, `diff_files.py`,
`compare_trace.py`, the pyslang checkers in `sim/fcov`, the test-program build
scripts) run fine locally.

### Batch simulations into about 10 LSF jobs

Each `submit -i` costs roughly a minute of LSF dispatch overhead, which dwarfs
most simulations (riscv-tests and most directed or stress tests take well under
10 s of CPU time). For regressions, stress tests and any other multi-test sweep,
**do not submit one LSF job per simulation**. Pack the simulations into about
10 LSF jobs in total and run them all concurrently. Each job runs a shell script
that executes its simulations back to back. Balance the batches by expected run
time (longest-processing-time-first greedy packing), so that all batches finish
at about the same time. Estimate run times from the `CPU Time` lines of
earlier `sim.log` files. CoreMark and the `*_test_csr` tests take 60–130 s each;
nearly everything else takes seconds. `run_full_regression.py --lsf_jobs N`
implements this; reuse its approach in ad-hoc stress scripts. Keep a per-test
log and exit code, so that a test failure does not hide the rest of the
batch.

## Build

From `sim/run`, `./vcscomp` always builds both `./simv32` (no `CHERIoT`
define) and `./simv` (`+define+CHERIoT`). Flags combine:

| Flag | Effect |
|---|---|
| *(none)* | `KUDU_PPL_CFG=1`; `CHERIoT` defined for `./simv` only |
| `-conf0` .. `-conf3` | Selects `KUDU_PPL_CFG` (pipeline configuration) |
| `-cov` | Adds `-f ../fcov/kudu_fcov.f` and `-cm line+cond+tgl+fsm+branch+assert -cm_hier ./cm_hier.cfg` |
| `-dii` | `+define+DII_SIM`: load ELF into sparse memory, stop after `+RVFI_MAX` packets |
| `-dw` | DesignWare multiplier; switches to `kudu_dw.vcs.f` |
| `-nowave` | `+define+NO_FSDB` |
| `-trace_dpi` | `+define+TraceDPI` (C-based tracer) |
| `-outdir=<dir>` | Builds into `<dir>` (absolute input paths, `csrc`/`csrc32`, `compile_{rv32,cheriot}.log`) instead of the cwd |

The riscv-tests tohost protocol is not a `vcscomp` flag: `./run_riscv_tests`
and `run_cov_regression.py` select it at run time with the `+RISCV_TEST_SUITE`
plusarg (see "Regressions").

`cm_hier.cfg` restricts code coverage to `tb_kudu_top.dut`, so the testbench and
memory models do not dilute the numbers. Functional coverage binds into the DUT
and is unaffected.

`sim/verilator/vgen` + `sim/verilator/vcomp` mirror the same flag set for
Verilator. Coverage is deliberately absent there — Verilator has no covergroups.

## Run a single test

```
cd sim/run
./simv +TEST=isa_test1
./simv32 +TEST=coremark.rv32o3
./simv +TEST=dbg_test1 +DBGROM=debug_rom
```

`+TEST=<name>` loads `bin/<name>.vhx` (or `bin/<name>.elf` under `-dii`).
Other plusargs read by `tb_kudu_top.sv`:

`+TIMEOUT` (cycles, default 1e6), `+RVFI_MAX`, `+BINDIR`, `+DBGROM`,
`+INSTR_GNT_WMAX` / `+INSTR_RESP_WMAX` / `+DATA_GNT_WMAX` / `+DATA_RESP_WMAX`
(memory delay injection), `+INSTR_ERR_RATE` / `+DATA_ERR_RATE` (random bus-error
injection), `+INSTR_ERR_ADDR=<hex>` / `+DATA_ERR_ADDR=<hex>` (bus error on every
access to one address), `+PMODE`, `+INTR_RATE`, `+DBG_REQ_RATE`, `+STAT_MCYCLE`,
`+ntb_random_seed_automatic`.

**Random interrupts and debug requests.** `+INTR_RATE` / `+DBG_REQ_RATE` (0..7)
set the stimulus rate; 0, the default, generates none. A test sees interrupts only
for lines it unmasks in `intr_mask` at `0x8380_0108` (one bit per line, 1 = masked,
reset all masked; bit 0 external, 1 software, 2 timer, 17:3 fast). Pending lines
stay raised until acknowledged by writing them to `0x8380_0104`. To stop
interrupts, write `0x3ffff` to `intr_mask` and then ack. Bit 2 of `0x8380_0100`
no longer gates interrupts. Random debug requests need `+DBGROM`.

**Random bus errors never hit the 4 KB at `0x8000_0000`–`0x8000_0FFF`.**
`data_mem_model.sv` exempts that DRAM page from `+INSTR_ERR_RATE` and
`+DATA_ERR_RATE` (on both the fetch and data side), so put trap handlers/ISR code,
and any data they touch, there when a test enables random errors; elsewhere a
random error can hit the handler itself and recurse. The exemption covers only the
random errors: `+INSTR_ERR_ADDR` / `+DATA_ERR_ADDR` still fault inside the page, and
random TSRAM (tag RAM) errors are not exempted.

Each run overwrites `trace_kudu_core.log` and `rvfi_kudu_core.log` in the cwd, so
rename them before the next run (the regression scripts do this).

Simulation ends on a UART write with bit 7 set (UART at `0x8380_0200`, aliased to
`0x1000_0000`; other writes print a character), on `+TIMEOUT`, or under `-dii`
once `+RVFI_MAX` RVFI packets have retired.

## Regressions

All from `sim/run`; these are **zsh** scripts that recompile into their own scratch
directory, so they do not disturb `./simv`:

```
./run_mini_regression       # rv32 + cheriot tests, default and memdly variants -> temp_regression/
./run_riscv_tests           # riscv-tests rv32ui/zba/zbb/zbc/zbs/ua suite      -> temp_riscv_test/
./run_mini_diff             # wish/tk GUI + stdout diff of the above vs run_ibex goldens
```

### Coverage regression (`./run_cov_regression.py`)

Runs the union of the two suites above (97 tests) and accumulates the coverage of
all of them into one persistent database, `cov_kudu_regr.vdb`:

```
submit -i ./run_cov_regression.py --compile --cov_report
./run_cov_regression.py --list                 # what would run, without running it
./run_cov_regression.py --suite riscv --only 'zbb'   # subset
```

It drives `./vcscomp -cov -nowave` once, producing the CHERIoT-capable `./simv`
used by every test. `coremark.rv32o3` and all riscv-tests add `+PMODE=0`.
The riscv-tests additionally pass `+RISCV_TEST_SUITE`, selecting the tohost
monitor in `data_mem_model.sv` at runtime; other tests retain UART termination.
The existing compile-time `RISCV_TEST_SUITE` define still selects tohost by
default for other scripts.

All tests record into one raw database under `cov_temp/`, then `urg` merges it
into `--cov_dir`, using `simv.vdb` as the initial design base. Older databases
from different elaborations may still have shape mismatches. Recompile once
after this change so `./simv` includes the runtime tohost selection.

The riscv-tests are self-checking through the tohost protocol, so the script
fails a test whose log lacks `RISCV Test passed`; for the mini-regression tests
only the exit code is checked, since their verdict comes from a trace diff. A
failing test never aborts the run and never discards the coverage already
collected. Other options: `--no_cov`, `--cov_tag`, `--keep_run_cov`,
`--keep_traces`, `--conf <0-3>`, `--continue_on_illegal_bin`, `--work_dir`.

## Comparing traces

```
sim/scripts/clean_trace.pl trace_kudu_core.log      # .log -> .clog (comparable form)
sim/scripts/diff_files.py --ignore-extra-lines 5 a.clog b.clog
sim/scripts/compare_trace.py kudu_trace sail_trace  # against cheriot-sail
sim/scripts/rvfi_gdiff.py                           # RVFI-level diff
```

`diff_files.py` and `compare_trace.py` encode known-benign trace differences
(trapped load/store annotations, `c.addi x0` rs1 reporting, etc.). When a diff is
a legitimate architectural equivalence rather than a bug, add the masking rule
there instead of hand-editing logs.

## DII flow (`sim/run_dii`)

Replays archived ELFs (from `bin.tar.gz`, selected by `bin/elfs_no_conflict.list`),
archives per-test `.rvfi`/`.trace` into `results.tar.gz`, and merges coverage into
a persistent `cov_kudu.vdb` with `urg`.

```
source ./load_module_vcs
python3 run_dii_rvfi.py --rvfi_max 5000 --compile --cov_report
```

`--compile` runs `./vcscomp -dii -nowave -cov` first; without it the existing
`./simv` is reused. `--rv32` uses the same CHERIoT-capable `./simv`, adding
`+PMODE=0` at simulation time. It does not add `-rv32` to compilation.
Both modes use `simv.vdb` as the first-time merge base and accumulate into
the same `cov_kudu.vdb`. Using one elaboration avoids the cross-build shape
mismatches caused by the former `simv32` flow; older databases from different
builds can still mismatch. Memory wait-state plusargs are randomised per invocation.

An `illegal_bins` hit is a fatal runtime error in VCS (`simv` exits 1), and every
illegal bin in `sim/fcov` marks a structural invariant of the design, so the
default is to let the run abort. `--continue_on_illegal_bin` adds
`-covg_cont_on_error` to demote hits to warnings, which is useful for surveying
how many distinct bins fire in one pass. Other options: `--no_cov`, `--cov_dir`,
`--cov_tag`, `--design_vdb`, `--keep_run_cov`.

A failing test does not abort the sweep: the remaining ELFs still run, whatever
logs exist are archived, the coverage collected so far is still merged, and the
script exits 1 with a list of the failed tests. This matters because `simv`
records coverage per test into the shared per-invocation database and only the
post-loop `urg` merge moves it into `--cov_dir` — stopping early would discard
every test that had already run. Note that RVFI/trace miscompares are *not*
detected here; comparison is a separate step after simulation.

The merge base is `cov_kudu.vdb` when it exists and the compile-time `simv.vdb`
the first time, since a raw simulation database holds test data only. `urg`
unions the two databases, so each invocation adds to the accumulated scores; it
also collapses all input tests into a single merged test record, so use
`--keep_run_cov` if per-test attribution is needed. The accumulated database
carries the design data of the build it was created from, and the script warns
when `simv.vdb` is newer than it — after an RTL change, start a fresh
`--cov_dir` rather than merging into stale design data.

`sim/scripts/elf2dii.py` converts an ELF to the `mem[X,addr] -> word` DII format;
`sim/scripts/check_dii_inputs.py` flags duplicate addresses in one.

## Building test programs

Run from `sim/tests` (the scripts `cd` into `work/` and copy `.vhx` + `.elf` into
`sim/run/bin/`):

```
cd sim/tests
../scripts/build_test.sh cheri_test1        # CHERIoT, clang -mcpu=cheriot
../scripts/build_test_rv32.sh <test>        # plain RV32, riscv-gnu gcc
../scripts/build_coremark.sh                # CoreMark (cheriot)
../scripts/build_coremark_rv32.sh
../scripts/build_dbg_test.sh
```

## Conventions

**Configuration is a struct, not parameters.** `rtl/kudu_cfg_pkg.sv` defines
`kudu_cfg_t` and the `KuduCfg1` / `KuduCfg1x` / `KuduCfg2` / `KuduCfg3` constants.
`tb_kudu_top.sv` picks one from `` `KUDU_PPL_CFG `` and passes it down as the single
`CFG` parameter. New configurability belongs in `kudu_cfg_t`, not in a new
module-level parameter. `kudu_top`'s only other parameters are `CHERIoTEn`
(from `` `define CHERIoT ``), `UseDWMult` and `RvfiDumpEn`.

**Every RTL and testbench file starts with the three-line header:**

```
// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
```

**File-list order matters.** Packages first (`cheri_pkg`, `csr_pkg`, `super_pkg`,
`kudu_cfg_pkg`), then RTL, then `tracer_pkg`/`tracer_dpi.cpp`/`tracer.sv`, then
testbench. `kudu_fcov_bind.sv` must be compiled last. Add new RTL to
`sim/run/kudu.vcs.f`, `sim/run/kudu_dw.vcs.f` and `sim/verilator/kudu.verilator.f`
together — they are maintained by hand and drift silently.

**Coverage binds use `.*` on purpose.** An explicit `.x(x)` against a signal that
does not exist in the target silently creates an implicit 1-bit net and the
covergroup then reports coverage on a constant. `.*` turns that into an
elaboration error. Only rename/index/reduce connections are written out, each with
a comment. Every `illegal_bins` is paired with an equivalent SVA assertion in the
same file. `check_syntax.py` / `check_binds.py` / `count_cov.py` (pyslang) validate
the model without a simulator.

**The `FC_ISA_INSTR` coverage tap mirrors the tracer's retire loop** — the
`rd_ptr .. rd_ptr_nxt` walk over `instr_trace_fifo` in `rtl/tracer.sv` — and
re-casts `instr_trace_t` against a local mirror struct because that type cannot
be named from a bound module. Changing either will silently desynchronise
coverage with no assertion to catch it; see `sim/fcov/README.md`.

**Working directories are dirty by design.** `sim/run*`, `sim/tests/work`, `csrc`,
`simv*`, `*.log`, `*.clog`, `*.fsdb` and `*.vdb` are build output. Do not commit
them, and do not clean up untracked files there.

Commit messages are a single lowercase imperative/past-tense line describing the
RTL or flow change, e.g. `fixed bug in LSU (incomplete csr_access logic ...)`.
