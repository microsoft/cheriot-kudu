#!/usr/bin/env python3
"""Run the mini-regression and riscv-tests suites and accumulate their coverage.

This is the coverage-collecting counterpart of ./run_mini_regression and
./run_riscv_tests: it runs the union of the tests those two scripts run and
merges coverage separately into cov_kudu_regr_rv32.vdb (CHERIoTEn=0) and
cov_kudu_regr_cheriot.vdb (CHERIoTEn=1, both runtime modes together).

Run it from sim/run, on the farm, so that the simulations can reach a licence:

    source ../run_dii/load_module_vcs
    submit -i ./run_cov_regression.py --compile --cov_report

By default RV32 tests run on both ./simv32 and ./simv with +PMODE=0; CHERIoT
and debug tests run on ./simv with +PMODE=1. --build selects all, cheriot or
rv32. ./vcscomp -cov -nowave builds both simulators in one invocation.
Each hardware build has its own raw and design database. RISC-V tests also
add +RISCV_TEST_SUITE to select the tohost monitor instead of UART termination.

The accumulated database is never deleted: every invocation merges into it, so
scores only ever grow. --cov_dir specifies a basename to which _rv32.vdb
and _cheriot.vdb are appended (after removing an optional .vdb suffix).
Existing unsuffixed and PMODE-partitioned databases are not used or modified.
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
from coverage_builds import BUILDS, build_cov_dir


TRACE_LOG = "trace_kudu_core.log"
TRACE_CLOG = "trace_kudu_core.clog"

# Must match the metrics used at compile time by ./vcscomp -cov.
COV_METRICS = "line+cond+tgl+fsm+branch+assert"
# Basename for the two persistent hardware-build coverage databases.
DEFAULT_COV_DIR = "cov_kudu_regr.vdb"
DEFAULT_WORK_DIR = "temp_cov_regression"

# Memory wait states used by the 'memdly' variant of the mini regression.
MEM_DELAY_ARGS = [
    "+INSTR_GNT_WMAX=2",
    "+INSTR_RESP_WMAX=2",
    "+DATA_GNT_WMAX=2",
    "+DATA_RESP_WMAX=2",
]
MINI_VARIANTS = (("default", []), ("memdly", MEM_DELAY_ARGS))

COMPILE_FLAGS = ["-cov", "-nowave"]

# Tests taken from ./run_riscv_tests. They are self-checking through the tohost
# protocol: the memory model prints 'RISCV Test passed :)' or 'failed :('.
RISCV_TESTS = [
    "rv32ui-p-add", "rv32ui-p-addi", "rv32ui-p-and", "rv32ui-p-andi",
    "rv32ui-p-auipc", "rv32ui-p-beq", "rv32ui-p-bge", "rv32ui-p-bgeu",
    "rv32ui-p-blt", "rv32ui-p-bltu", "rv32ui-p-bne", "rv32ui-p-fence_i",
    "rv32ui-p-jal", "rv32ui-p-jalr", "rv32ui-p-lb", "rv32ui-p-lbu",
    "rv32ui-p-ld_st", "rv32ui-p-lh", "rv32ui-p-lhu", "rv32ui-p-lui",
    "rv32ui-p-lw", "rv32ui-p-ma_data", "rv32ui-p-or", "rv32ui-p-ori",
    "rv32ui-p-sb", "rv32ui-p-sh", "rv32ui-p-simple", "rv32ui-p-sll",
    "rv32ui-p-slli", "rv32ui-p-slt", "rv32ui-p-slti", "rv32ui-p-sltiu",
    "rv32ui-p-sltu", "rv32ui-p-sra", "rv32ui-p-srai", "rv32ui-p-srl",
    "rv32ui-p-srli", "rv32ui-p-st_ld", "rv32ui-p-sub", "rv32ui-p-sw",
    "rv32ui-p-xor", "rv32ui-p-xori",
    "rv32uzba-p-sh1add", "rv32uzba-p-sh2add", "rv32uzba-p-sh3add",
    "rv32uzbb-p-andn", "rv32uzbb-p-clz", "rv32uzbb-p-cpop", "rv32uzbb-p-ctz",
    "rv32uzbb-p-max", "rv32uzbb-p-maxu", "rv32uzbb-p-min", "rv32uzbb-p-minu",
    "rv32uzbb-p-orc_b", "rv32uzbb-p-orn", "rv32uzbb-p-rev8", "rv32uzbb-p-rol",
    "rv32uzbb-p-ror", "rv32uzbb-p-rori", "rv32uzbb-p-sext_b",
    "rv32uzbb-p-sext_h", "rv32uzbb-p-xnor", "rv32uzbb-p-zext_h",
    "rv32uzbc-p-clmul", "rv32uzbc-p-clmulh", "rv32uzbc-p-clmulr",
    "rv32uzbs-p-bclr", "rv32uzbs-p-bclri", "rv32uzbs-p-bext",
    "rv32uzbs-p-bexti", "rv32uzbs-p-binv", "rv32uzbs-p-binvi",
    "rv32uzbs-p-bset", "rv32uzbs-p-bseti",
    "rv32ua-p-lrsc", "rv32ua-p-amoadd_w", "rv32ua-p-amoand_w",
    "rv32ua-p-amomaxu_w", "rv32ua-p-amomax_w", "rv32ua-p-amominu_w",
    "rv32ua-p-amomin_w", "rv32ua-p-amoor_w", "rv32ua-p-amoswap_w",
    "rv32ua-p-amoxor_w",
]

# Tests taken from ./run_mini_regression.
MINI_RV32_TESTS = ["coremark.rv32o3"]
MINI_CHERIOT_TESTS = [
    "isa_test1",
    "isa_test1a",
    "isa_test2",
    "isa_test2a",
    "coremark.cheriot",
]


class Test(object):
    """One simulation: a binary, a +TEST name and the plusargs it needs."""

    def __init__(self, suite, build, name, variant, args, self_checking=False):
        self.suite = suite
        self.build = build
        self.name = name
        self.variant = variant
        self.args = args
        self.self_checking = self_checking

    @property
    def label(self):
        return "{}.{}".format(self.name, self.variant)

    @property
    def run_label(self):
        return "{}.{}".format(self.build, self.label)

    @property
    def pmode(self):
        modes = [arg for arg in self.args if arg.startswith("+PMODE=")]
        if modes not in (["+PMODE=0"], ["+PMODE=1"]):
            raise ValueError("{} requires exactly one +PMODE=0 or +PMODE=1".format(self.label))
        return int(modes[0][-1])


def build_test_list(suites, riscv_timeout, build="all"):
    """The union of the tests run by run_mini_regression and run_riscv_tests."""
    tests = []

    if "mini" in suites:
        for name in MINI_RV32_TESTS:
            for variant, args in MINI_VARIANTS:
                tests.append(
                    Test("mini", "cheriot", name, variant, ["+PMODE=0"] + list(args))
                )
        for name in MINI_CHERIOT_TESTS:
            for variant, args in MINI_VARIANTS:
                # isa_test2a exercises the interrupt path.
                extra = ["+INTR_INTVL=3"] if name == "isa_test2a" else []
                tests.append(
                    Test("mini", "cheriot", name, variant, ["+PMODE=1"] + extra + list(args))
                )
        tests.append(
            Test("mini", "cheriot", "dbg_test1", "default",
                 ["+PMODE=1", "+DBGROM=debug_rom"])
        )

    if "riscv" in suites:
        for name in RISCV_TESTS:
            tests.append(
                Test(
                    "riscv",
                    "cheriot",
                    name,
                    "default",
                    ["+TIMEOUT={}".format(riscv_timeout), "+PMODE=0", "+RISCV_TEST_SUITE"],
                    self_checking=True,
                )
            )

    selected_builds = list(BUILDS) if build == "all" else [build]
    return [
        Test(test.suite, target, test.name, test.variant, list(test.args), test.self_checking)
        for test in tests for target in selected_builds
        if target == "cheriot" or test.pmode == 0
    ]


def positive_int(value):
    value = int(value)
    if value <= 0:
        raise argparse.ArgumentTypeError("must be greater than zero")
    return value


def sanitize_test_name(name):
    """Return a name that is safe to use as a VCS -cm_name test name."""
    return re.sub(r"[^A-Za-z0-9_]", "_", name)


def make_cov_tag():
    """Unique-per-invocation tag so accumulated test names never collide."""
    return "regr_{}_{}".format(time.strftime("%Y%m%d_%H%M%S"), os.getpid())


def parse_args():
    parser = argparse.ArgumentParser(
        description=(
            "Run the mini-regression and riscv-tests suites and merge the "
            "coverage into separate databases for CHERIoTEn=0 and CHERIoTEn=1."
        )
    )
    parser.add_argument(
        "--build",
        choices=["all"] + list(BUILDS),
        default="all",
        help="hardware builds to exercise (default: all); RV32 tests run on both builds",
    )
    parser.add_argument(
        "--suite",
        choices=["mini", "riscv", "all"],
        default="all",
        help="which suite to run (default: all)",
    )
    parser.add_argument(
        "--only",
        help="run only the tests whose name matches this regular expression",
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="list the selected tests and exit without running anything",
    )
    parser.add_argument(
        "--compile",
        action="store_true",
        help="rebuild every simulator needed by the selected tests first",
    )
    parser.add_argument(
        "--conf",
        choices=["0", "1", "2", "3"],
        help="pipeline configuration passed to ./vcscomp as -conf<N>",
    )
    parser.add_argument(
        "--riscv_timeout",
        type=positive_int,
        default=10000,
        help="+TIMEOUT value for the riscv-tests (default: 10000)",
    )
    parser.add_argument(
        "--work_dir",
        default=DEFAULT_WORK_DIR,
        help="directory the simulations run in (default: {})".format(DEFAULT_WORK_DIR),
    )
    parser.add_argument(
        "--no_cov",
        action="store_true",
        help="run the tests without collecting or merging coverage",
    )
    parser.add_argument(
        "--cov_dir",
        default=DEFAULT_COV_DIR,
        help=(
            "coverage basename; append _rv32.vdb and _cheriot.vdb after "
            "removing an optional .vdb suffix (default: {}). Existing "
            "unsuffixed and PMODE-partitioned databases are not merged".format(DEFAULT_COV_DIR)
        ),
    )
    parser.add_argument(
        "--cov_tag",
        help="name prefix for the recorded tests (default: a timestamped tag)",
    )
    parser.add_argument(
        "--design_vdb",
        help=(
            "compile-time database providing the design data the first time "
            "--cov_dir is created; allowed only with one selected hardware build "
            "(default: simv.vdb for cheriot, simv32.vdb for rv32)"
        ),
    )
    parser.add_argument(
        "--keep_run_cov",
        action="store_true",
        help="keep the raw per-invocation databases after a successful merge",
    )
    parser.add_argument(
        "--continue_on_illegal_bin",
        action="store_true",
        help=(
            "demote illegal_bins hits to warnings (-covg_cont_on_error), which "
            "surveys every bin that fires in one pass instead of aborting"
        ),
    )
    parser.add_argument(
        "--cov_report",
        action="store_true",
        help="report each selected build in urgReport_cheriot or urgReport_rv32",
    )
    parser.add_argument(
        "--keep_traces",
        action="store_true",
        help="keep every per-test trace log (default: only failing tests)",
    )
    return parser.parse_args()


def run_urg(command, run_dir):
    print("+ {}".format(" ".join(command)), flush=True)
    try:
        subprocess.run(command, cwd=run_dir, check=True)
    except FileNotFoundError:
        print("WARNING: urg not found in PATH", file=sys.stderr)
        return False
    except subprocess.CalledProcessError as error:
        print(
            "WARNING: urg failed with exit code {}".format(error.returncode),
            file=sys.stderr,
        )
        return False
    return True


def newest_mtime(directory):
    """Newest modification time in a directory tree.

    A coverage database is a directory whose contents are rewritten in place,
    so the timestamp of the directory itself does not track its contents.
    """
    newest = directory.stat().st_mtime
    for path in directory.rglob("*"):
        newest = max(newest, path.stat().st_mtime)
    return newest


def warn_if_design_is_newer(cov_dir, design_vdbs):
    """Warn when the accumulated database predates the current build.

    The accumulated database carries the design data of the build it was first
    created from. Merging run data from a design that has been recompiled since
    then makes urg fall back on name matching, which silently drops the objects
    that no longer line up, so the accumulated scores stop being comparable.
    """
    if not cov_dir.is_dir():
        return
    cov_mtime = newest_mtime(cov_dir)
    for design_vdb in design_vdbs:
        if design_vdb.is_dir() and newest_mtime(design_vdb) > cov_mtime:
            print(
                "WARNING: {} is newer than {}; if the design was recompiled "
                "since the accumulated database was last merged, start a fresh "
                "--cov_dir instead of merging into stale design data".format(
                    design_vdb.name, cov_dir
                ),
                file=sys.stderr,
                flush=True,
            )


def compile_builds(conf, run_dir):
    """./vcscomp builds both hardware configurations in one invocation."""
    command = ["./vcscomp"] + COMPILE_FLAGS
    if conf is not None:
        command.append("-conf{}".format(conf))
    print("+ {}".format(" ".join(command)), flush=True)
    completed = subprocess.run(command, cwd=run_dir)
    if completed.returncode != 0:
        print(
            "ERROR: simulator compilation failed with exit code {}".format(
                completed.returncode
            ),
            file=sys.stderr,
        )
        return False
    return True


def prepare_work_dir(work_dir, elf_dir):
    """Create the run directory and the bin/ symlink the testbench reads."""
    work_dir.mkdir(parents=True, exist_ok=True)
    link = work_dir / "bin"
    if link.is_symlink():
        if Path(os.readlink(str(link))).resolve() != elf_dir.resolve():
            link.unlink()
    elif link.exists():
        raise RuntimeError("{} exists and is not a symlink".format(link))
    if not link.exists():
        link.symlink_to(os.path.relpath(str(elf_dir), str(work_dir)))


def merge_cov(run_vdbs, cov_dir, design_vdb, run_dir):
    """Merge the raw databases of this invocation into the persistent one.

    A raw simulation database only holds test data, so the merge base is the
    accumulated database when it already exists and a compile-time design
    database the very first time.
    """
    run_vdbs = [vdb for vdb in run_vdbs if vdb.is_dir()]
    if not run_vdbs:
        print("WARNING: no coverage data was produced", file=sys.stderr)
        return False

    base = cov_dir if cov_dir.is_dir() else design_vdb
    if not base.is_dir():
        print(
            "WARNING: neither {} nor {} exists, cannot merge coverage".format(
                cov_dir, design_vdb
            ),
            file=sys.stderr,
        )
        return False

    # urg appends '.vdb' to -dbname unless the name already ends with it.
    base_name = cov_dir.name
    if base_name.endswith(".vdb"):
        base_name = base_name[: -len(".vdb")]
    temp_dir = cov_dir.parent / "cov_temp"
    temp_dir.mkdir(parents=True, exist_ok=True)
    tmp_dir = temp_dir / (base_name + ".merge_tmp.vdb")
    if tmp_dir.exists():
        shutil.rmtree(tmp_dir)

    command = ["urg", "-full64", "-dir", str(base)]
    for run_vdb in run_vdbs:
        command += ["-dir", str(run_vdb)]
    command += ["-dbname", str(tmp_dir), "-noreport"]
    if not run_urg(command, run_dir):
        return False
    if not tmp_dir.is_dir():
        print("WARNING: urg did not create {}".format(tmp_dir), file=sys.stderr)
        return False

    # Only drop the previous database once the merged one is complete.
    backup_dir = temp_dir / (base_name + ".prev.vdb")
    if backup_dir.exists():
        shutil.rmtree(backup_dir)
    if cov_dir.is_dir():
        cov_dir.rename(backup_dir)
    tmp_dir.rename(cov_dir)
    if backup_dir.exists():
        shutil.rmtree(backup_dir)
    return True


def generate_cov_report(cov_dir, run_dir, build):
    report_dir = run_dir / "urgReport_{}".format(build)
    command = ["urg", "-full64", "-dir", str(cov_dir), "-report", str(report_dir)]
    if run_urg(command, run_dir):
        print("Coverage report written to {}".format(report_dir), flush=True)


def clean_trace(work_dir, scripts_dir, label, keep):
    """Post-process and rename the trace logs the way run_mini_regression does."""
    trace = work_dir / TRACE_LOG
    if not trace.is_file():
        return
    if not keep:
        trace.unlink()
        clog = work_dir / TRACE_CLOG
        if clog.is_file():
            clog.unlink()
        return
    subprocess.run(
        [str(scripts_dir / "clean_trace.pl"), TRACE_LOG],
        cwd=work_dir,
        stdout=subprocess.DEVNULL,
    )
    for name, suffix in ((TRACE_LOG, "log"), (TRACE_CLOG, "clog")):
        path = work_dir / name
        if path.is_file():
            path.replace(work_dir / "trace.{}.{}".format(label, suffix))


def run_test(test, run_dir, work_dir, cov_args, log_path):
    """Run one simulation, capture its output and decide whether it passed."""
    command = [str(run_dir / BUILDS[test.build]["simv"]), "+TEST={}".format(test.name)]
    command += test.args + cov_args

    started = time.time()
    with open(str(log_path), "w") as log_file:
        log_file.write("+ {}\n".format(" ".join(command)))
        log_file.flush()
        completed = subprocess.run(
            command,
            cwd=work_dir,
            stdout=log_file,
            stderr=subprocess.STDOUT,
        )
    elapsed = time.time() - started

    failure = None
    if completed.returncode != 0:
        failure = "{} exited with code {}".format(
            BUILDS[test.build]["simv"], completed.returncode
        )
    elif test.self_checking:
        # The tohost model prints the verdict; simv exits 0 either way.
        output = log_path.read_text(errors="replace")
        if "RISCV Test failed" in output:
            failure = "tohost reported a failure"
        elif "RISCV Test passed" not in output:
            failure = "no tohost verdict (timeout?)"
    return failure, elapsed


def main():
    args = parse_args()
    run_dir = Path(__file__).resolve().parent
    scripts_dir = run_dir.parent / "scripts"
    elf_dir = run_dir / "bin"
    work_dir = Path(args.work_dir)
    if not work_dir.is_absolute():
        work_dir = run_dir / work_dir

    suites = ["mini", "riscv"] if args.suite == "all" else [args.suite]
    tests = build_test_list(suites, args.riscv_timeout, args.build)
    if args.only:
        pattern = re.compile(args.only)
        tests = [test for test in tests if pattern.search(test.name)]
    if not tests:
        print("ERROR: no test matches the selection", file=sys.stderr)
        return 1

    # Keep the build order stable so the log reads the same way every time.
    builds = [name for name in BUILDS if any(t.build == name for t in tests)]
    if args.design_vdb and len(builds) != 1:
        print("ERROR: --design_vdb requires one selected hardware build; "
              "use --build cheriot or --build rv32", file=sys.stderr)
        return 1

    if args.list:
        for test in tests:
            print(
                "{:<10} {:<12} pmode{} {}".format(
                    test.suite, test.build, test.pmode, test.label
                ),
                flush=True,
            )
        print("{} test(s)".format(len(tests)))
        return 0

    if args.compile:
        if not compile_builds(args.conf, run_dir):
            return 1
    else:
        print(
            "Reusing the existing simulators ({}); pass --compile to rebuild".format(
                ", ".join("./" + BUILDS[b]["simv"] for b in builds)
            ),
            flush=True,
        )

    missing = [b for b in builds if not (run_dir / BUILDS[b]["simv"]).is_file()]
    if missing:
        for build in missing:
            print(
                "ERROR: ./{} not found, build it with ./vcscomp {}".format(
                    BUILDS[build]["simv"], " ".join(COMPILE_FLAGS)
                ),
                file=sys.stderr,
            )
        return 1

    cov_enabled = not args.no_cov
    cov_base = Path(args.cov_dir)
    if not cov_base.is_absolute():
        cov_base = run_dir / cov_base
    cov_dirs = {build: build_cov_dir(cov_base, build) for build in builds}
    cov_tag = sanitize_test_name(args.cov_tag or make_cov_tag())
    cov_temp = run_dir / "cov_temp"
    # Runtime modes share a database; different hardware elaborations never do.
    run_vdbs = {
        build: cov_temp / "cov_run_{}_{}.vdb".format(cov_tag, build) for build in builds
    }
    design_vdbs = {build: run_dir / BUILDS[build]["vdb"] for build in builds}
    if args.design_vdb:
        design_vdb = Path(args.design_vdb)
        if not design_vdb.is_absolute():
            design_vdb = run_dir / design_vdb
        design_vdbs[builds[0]] = design_vdb

    if cov_enabled:
        cov_temp.mkdir(parents=True, exist_ok=True)
        for run_vdb in run_vdbs.values():
            if run_vdb.exists():
                print(
                    "ERROR: {} already exists; choose a different --cov_tag "
                    "to preserve it".format(run_vdb), file=sys.stderr,
                )
                return 1
        for build, cov_dir in cov_dirs.items():
            warn_if_design_is_newer(cov_dir, [design_vdbs[build]])
            print(
                "Coverage {}: recording into {}, merging into {} ({})".format(
                    build, run_vdbs[build],
                    cov_dir,
                    "existing database" if cov_dir.is_dir() else "new database",
                ),
                flush=True,
            )

    prepare_work_dir(work_dir, elf_dir)
    print(
        "Running {} test(s) from suite(s) {} in {}".format(
            len(tests), "+".join(suites), work_dir
        ),
        flush=True,
    )

    failed_tests = []
    for index, test in enumerate(tests, start=1):
        cov_args = []
        if cov_enabled:
            cov_args = [
                "-cm",
                COV_METRICS,
                "-cm_dir",
                str(run_vdbs[test.build]),
                "-cm_name",
                "{}__{}__pmode{}__{}".format(
                    cov_tag, test.build, test.pmode, sanitize_test_name(test.label)
                ),
            ]
            if args.continue_on_illegal_bin:
                # An illegal_bins hit is a runtime error that aborts the
                # simulation, which is the intended behaviour: every illegal bin
                # in sim/fcov marks a structural invariant of the design. Use
                # this only to survey how many distinct bins fire in one pass.
                cov_args.append("-covg_cont_on_error")
        log_path = work_dir / "sim.{}.log".format(test.run_label)

        # A failing test must not abort the regression: simv writes the coverage
        # of every test it has already run into the raw database, and that data
        # is only moved into --cov_dir by the merge after the loop.
        failure, elapsed = run_test(test, run_dir, work_dir, cov_args, log_path)
        print(
            "[{:>3}/{}] {:<28} {:<8} {:>6.1f}s  {}".format(
                index,
                len(tests),
                test.label,
                test.build,
                elapsed,
                "FAIL: {}".format(failure) if failure else "ok",
            ),
            flush=True,
        )
        if failure is not None:
            failed_tests.append(test.run_label)
        clean_trace(work_dir, scripts_dir, test.run_label, args.keep_traces or failure)

    exit_code = 0
    if failed_tests:
        print(
            "ERROR: {} of {} test(s) failed: {}".format(
                len(failed_tests), len(tests), ", ".join(failed_tests)
            ),
            file=sys.stderr,
            flush=True,
        )
        exit_code = 1
    else:
        print("All {} test(s) passed".format(len(tests)), flush=True)
    print("Simulation logs are in {}".format(work_dir), flush=True)

    if cov_enabled:
        for build, cov_dir in cov_dirs.items():
            run_vdb = run_vdbs[build]
            if merge_cov([run_vdb], cov_dir, design_vdbs[build], run_dir):
                print("Coverage accumulated in {}".format(cov_dir), flush=True)
                if not args.keep_run_cov and run_vdb.is_dir():
                    shutil.rmtree(run_vdb)
                if args.cov_report:
                    generate_cov_report(cov_dir, run_dir, build)
                else:
                    print(
                        "Generate a report with: submit -i urg -full64 -dir {} "
                        "-report urgReport_{}".format(cov_dir, build),
                        flush=True,
                    )
            else:
                print(
                    "ERROR: coverage was not merged; the raw data is kept in {}".format(
                        run_vdb
                    ),
                    file=sys.stderr,
                    flush=True,
                )
                exit_code = 1

    return exit_code


if __name__ == "__main__":
    sys.exit(main())
