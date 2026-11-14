#!/usr/bin/env python3
"""Run the mini-regression and riscv-tests suites with fresh coverage.

This is the coverage-collecting counterpart of ./run_mini_regression and
./run_riscv_tests: it runs the union of the tests those two scripts run and
merges coverage separately into temp_cov_regression/cov_kudu_regr_rv32.vdb
(CHERIoTEn=0) and cov_kudu_regr_cheriot.vdb (CHERIoTEn=1, both runtime modes
together) in the same directory.

Run it from sim/run, on the farm, so that the simulations can reach a licence:

    source ../run_dii/load_module_vcs
    submit -i ./run_cov_regression.py --cov_report

By default RV32 tests run on both ./simv32 and ./simv with +PMODE=0; CHERIoT
and debug tests run on ./simv with +PMODE=1. --build selects all, cheriot or
rv32. Every actual run invokes ./vcscomp -cov -nowave, building both simulators
in a fresh build_<id>/ under --work_dir (default: temp_cov_regression).
--list is read-only; --compile remains accepted but is no longer necessary.
Each hardware build has its own raw and design database. RISC-V tests also
add +RISCV_TEST_SUITE to select the tohost monitor instead of UART termination.
The mini suite includes isa_test_csr (PMODE=1) and rv32_test_csr (PMODE=0),
each with default and delayed memory. Their UART verdict must report
"CSR test passed"; a failure message or missing verdict fails the run.

After compilation and preflight succeed, coverage-enabled runs delete the
selected hardware output databases before the first simulation. Only this
invocation's data is merged with its matching design base. --cov_dir specifies
a basename to which _rv32.vdb and _cheriot.vdb are appended (after removing an
optional .vdb suffix). Reset targets must be real VCS databases inside sim/,
not symlinks, design inputs, DII databases or enclosing output directories.
--list and --no_cov never reset coverage.
Existing unsuffixed and PMODE-partitioned databases are not used or modified.
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import time
import uuid
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
from coverage_builds import BUILDS, build_cov_dir


SIM_ROOT = Path(__file__).resolve().parent.parent
TRACE_LOG = "trace_kudu_core.log"
TRACE_CLOG = "trace_kudu_core.clog"

# Must match the metrics used at compile time by ./vcscomp -cov.
COV_METRICS = "line+cond+tgl+fsm+branch+assert"
# Basename for the two current-invocation hardware-build coverage databases.
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

# Tests from ./run_mini_regression plus directed CSR coverage tests.
MINI_RV32_TESTS = ["coremark.rv32o3", "rv32_test_csr"]
MINI_CHERIOT_TESTS = [
    "isa_test1",
    "isa_test1a",
    "isa_test2",
    "isa_test2a",
    "isa_test_csr",
    "coremark.cheriot",
]
CSR_TESTS = frozenset(("isa_test_csr", "rv32_test_csr"))


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
    """The mini/RISC-V suites plus the directed self-checking CSR tests."""
    tests = []

    if "mini" in suites:
        for name in MINI_RV32_TESTS:
            for variant, args in MINI_VARIANTS:
                tests.append(
                    Test("mini", "cheriot", name, variant, ["+PMODE=0"] + list(args),
                         self_checking=name in CSR_TESTS)
                )
        for name in MINI_CHERIOT_TESTS:
            for variant, args in MINI_VARIANTS:
                # isa_test2a exercises the interrupt path.
                extra = ["+INTR_RATE=4"] if name == "isa_test2a" else []
                tests.append(
                    Test("mini", "cheriot", name, variant, ["+PMODE=1"] + extra + list(args),
                         self_checking=name in CSR_TESTS)
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
    """Unique-per-invocation tag so retained raw database names never collide."""
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
        help="compatibility flag; actual runs always rebuild both simulators",
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
        help=("output base for simulations, fresh builds, raw coverage, reports and "
              "default coverage results (relative to sim/run; default: {})"
              .format(DEFAULT_WORK_DIR)),
    )
    parser.add_argument(
        "--no_cov",
        action="store_true",
        help="run the tests without collecting or merging coverage",
    )
    parser.add_argument(
        "--cov_dir",
        default=None,
        help=(
            "coverage basename; append _rv32.vdb and _cheriot.vdb after "
            "removing an optional .vdb suffix. Existing "
            "unsuffixed and PMODE-partitioned databases are not merged. Selected "
            "outputs are reset after successful compilation/preflight, before "
            "simulation; only non-symlink VCS databases inside sim/ are allowed. Defaults "
            "to --work_dir/{}; explicit relative paths resolve from sim/run"
            .format(DEFAULT_COV_DIR)
        ),
    )
    parser.add_argument(
        "--cov_tag",
        help="name prefix for the recorded tests (default: a timestamped tag)",
    )
    parser.add_argument(
        "--design_vdb",
        help=(
            "compile-time database providing the design data for this invocation; "
            "allowed only with one selected hardware build "
            "(default: fresh build's simv.vdb for cheriot, simv32.vdb for rv32). "
            "Explicit relative paths resolve from sim/run; supply a matching "
            "design-only database, without historical runtime records"
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
        help="report each selected build in --work_dir/urgReport_<build>",
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


def contains_path(parent, child):
    return parent == child or parent in child.parents


def validate_cov_outputs(cov_dirs, design_vdbs, protected_paths):
    """Validate every reset target before allowing any previous result deletion."""
    sim_root = SIM_ROOT.resolve()
    protected = [path.resolve() for path in protected_paths]
    designs = [path.resolve() for path in design_vdbs.values()]
    for design in designs:
        if not design.is_dir():
            raise RuntimeError("design database does not exist: {}".format(design))
    resolved = {}
    for build, path in cov_dirs.items():
        # Check before resolving: resolving alone hides a symlink's identity.
        if any(part.is_symlink() for part in (path, *path.parents)):
            raise RuntimeError("coverage output must not use symlinks: {}".format(path))
        target = path.resolve()
        if not contains_path(sim_root, target):
            raise RuntimeError("coverage output must be inside sim/; refusing automatic "
                               "deletion outside sim/: {}".format(target))
        if target.suffix != ".vdb" or not target.name.endswith("_{}.vdb".format(build)):
            raise RuntimeError("unsafe coverage database name: {}".format(target))
        if (contains_path(sim_root / "run_dii", target)
                or target.name in ("cov_kudu_cheriot.vdb", "cov_kudu_rv32.vdb")
                or any(parent.suffix == ".vdb" for parent in target.parents)):
            raise RuntimeError("coverage output overlaps a DII or source database: {}"
                               .format(target))
        if (any(contains_path(target, path) for path in protected)
                or any(contains_path(target, design) or contains_path(design, target)
                       for design in designs)):
            raise RuntimeError("coverage output overlaps a design or working input: {}"
                               .format(target))
        if target.exists():
            if not target.is_dir() or not (target / "snps/coverage/db").is_dir():
                raise RuntimeError("refusing to remove a non-VCS coverage database: {}"
                                   .format(target))
            if not (target / "snps/coverage/db/testdata").is_dir():
                raise RuntimeError("refusing to remove a design-only coverage database: {}"
                                   .format(target))
            if any(part.is_symlink() for part in target.rglob("*")):
                raise RuntimeError("coverage database contains symlinks: {}".format(target))
        resolved[build] = target
    return resolved


def reset_cov_outputs(cov_dirs):
    """Remove only the selected, preflight-validated hardware result databases."""
    for path in cov_dirs.values():
        if path.exists():
            print("Removing previous regression coverage: {}".format(path), flush=True)
            shutil.rmtree(path)


def compile_builds(conf, run_dir, build_dir):
    """./vcscomp builds both hardware configurations in one invocation."""
    command = ["./vcscomp"] + COMPILE_FLAGS
    if conf is not None:
        command.append("-conf{}".format(conf))
    command.append("-outdir={}".format(build_dir))
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
    """Merge only this invocation's raw data and its matching design database."""
    run_vdbs = [vdb for vdb in run_vdbs if vdb.is_dir()]
    if not run_vdbs:
        print("WARNING: no coverage data was produced", file=sys.stderr)
        return False

    base = design_vdb
    if not base.is_dir():
        print(
            "WARNING: {} does not exist, cannot merge coverage".format(design_vdb),
            file=sys.stderr,
        )
        return False

    # urg appends '.vdb' to -dbname unless the name already ends with it.
    base_name = cov_dir.name
    if base_name.endswith(".vdb"):
        base_name = base_name[: -len(".vdb")]
    temp_dir = cov_dir.parent / "cov_temp"
    temp_dir.mkdir(parents=True, exist_ok=True)
    merge_tag = uuid.uuid4().hex
    tmp_dir = temp_dir / (base_name + "." + merge_tag + ".merge_tmp.vdb")

    command = ["urg", "-full64", "-dir", str(base)]
    for run_vdb in run_vdbs:
        command += ["-dir", str(run_vdb)]
    command += ["-dbname", str(tmp_dir), "-noreport"]
    if not run_urg(command, run_dir):
        return False
    if not tmp_dir.is_dir():
        print("WARNING: urg did not create {}".format(tmp_dir), file=sys.stderr)
        return False

    if cov_dir.exists() or cov_dir.is_symlink():
        print("WARNING: coverage output reappeared after reset; refusing to replace {}"
              .format(cov_dir), file=sys.stderr)
        return False
    tmp_dir.rename(cov_dir)
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
        # UART and tohost verdicts can report failure despite a zero exit code.
        output = log_path.read_text(errors="replace")
        if test.name in CSR_TESTS:
            if "CSR test failed" in output:
                failure = "CSR test reported a failure"
            elif "CSR test passed" not in output:
                failure = "no CSR test verdict (timeout?)"
        elif "RISCV Test failed" in output:
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

    cov_enabled = not args.no_cov
    cov_base = Path(args.cov_dir) if args.cov_dir else work_dir / DEFAULT_COV_DIR
    if not cov_base.is_absolute():
        cov_base = run_dir / cov_base
    cov_dirs = {build: build_cov_dir(cov_base, build) for build in builds}
    cov_tag = sanitize_test_name(args.cov_tag or make_cov_tag())
    cov_temp = work_dir / "cov_temp"
    # Runtime modes share a database; different hardware elaborations never do.
    run_vdbs = {
        build: cov_temp / "cov_run_{}_{}.vdb".format(cov_tag, build) for build in builds
    }
    if cov_enabled:
        for run_vdb in run_vdbs.values():
            if run_vdb.exists() or run_vdb.is_symlink():
                print(
                    "ERROR: {} already exists; choose a different --cov_tag "
                    "to preserve it".format(run_vdb), file=sys.stderr,
                )
                return 1

    # Never reuse an elaboration's database: it may contain old design objects
    # or runtime test records, even when VCS recompiles successfully in place.
    build_dir = work_dir / ("build_" + uuid.uuid4().hex)
    build_dir.mkdir(parents=True)
    if not compile_builds(args.conf, run_dir, build_dir):
        return 1
    missing = [b for b in builds if not (build_dir / BUILDS[b]["simv"]).is_file()]
    if missing:
        for build in missing:
            print("ERROR: compilation did not produce {}".format(
                build_dir / BUILDS[build]["simv"]), file=sys.stderr)
        return 1

    design_vdbs = {build: build_dir / BUILDS[build]["vdb"] for build in builds}
    if args.design_vdb:
        design_vdb = Path(args.design_vdb)
        if not design_vdb.is_absolute():
            design_vdb = run_dir / design_vdb
        design_vdbs[builds[0]] = design_vdb

    try:
        prepare_work_dir(work_dir, elf_dir)
        if cov_enabled:
            cov_dirs = validate_cov_outputs(
                cov_dirs, design_vdbs,
                [run_dir, work_dir, build_dir, elf_dir, cov_temp]
                + [run_dir / spec["vdb"] for spec in BUILDS.values()]
                + list(run_vdbs.values()),
            )
            cov_temp.mkdir(parents=True, exist_ok=True)
            for cov_dir in cov_dirs.values():
                cov_dir.parent.mkdir(parents=True, exist_ok=True)
            reset_cov_outputs(cov_dirs)
    except (OSError, RuntimeError) as error:
        print("ERROR: coverage/run preflight or reset failed: {}".format(error),
              file=sys.stderr)
        return 1

    if cov_enabled:
        for build, cov_dir in cov_dirs.items():
            print(
                "Coverage {}: recording into {}, merging fresh results into {}".format(
                    build, run_vdbs[build], cov_dir,
                ),
                flush=True,
            )

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
        failure, elapsed = run_test(test, build_dir, work_dir, cov_args, log_path)
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
            if merge_cov([run_vdb], cov_dir, design_vdbs[build], work_dir):
                print("Current regression coverage written to {}".format(cov_dir), flush=True)
                if not args.keep_run_cov and run_vdb.is_dir():
                    shutil.rmtree(run_vdb)
                if args.cov_report:
                    generate_cov_report(cov_dir, work_dir, build)
                else:
                    print(
                        "Generate a report with: submit -i urg -full64 -dir {} "
                        "-report {}".format(cov_dir, work_dir / ("urgReport_" + build)),
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
