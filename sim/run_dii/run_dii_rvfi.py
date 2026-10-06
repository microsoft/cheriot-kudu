#!/usr/bin/env python3
"""Run archived ELFs, accumulating coverage separately for each hardware build.

The --cov_dir basename defaults to cov_kudu.vdb, producing
cov_kudu_cheriot.vdb for CHERIoTEn=1 (both runtime modes together), or
cov_kudu_rv32.vdb for CHERIoTEn=0. Existing unsuffixed and PMODE-partitioned
databases are not used or modified.
"""

import argparse
import os
import random
import re
import shutil
import subprocess
import sys
import tarfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
from coverage_builds import BUILDS, build_cov_dir


RVFI_LOG = "rvfi_kudu_core.log"
TRACE_LOG = "trace_kudu_core.log"

# Must match the metrics used at compile time by ./vcscomp -cov.
COV_METRICS = "line+cond+tgl+fsm+branch+assert"
# Basename for the two persistent hardware-build coverage databases.
DEFAULT_COV_DIR = "cov_kudu.vdb"


def positive_int(value):
    value = int(value)
    if value <= 0:
        raise argparse.ArgumentTypeError("must be greater than zero")
    return value


def sanitize_test_name(name):
    """Return a name that is safe to use as a VCS -cm_name test name."""
    return re.sub(r"[^A-Za-z0-9_]", "_", name)


def parse_args():
    parser = argparse.ArgumentParser(
        description=(
            "Compile the Kudu VCS DII simulator, run the ELFs listed in "
            "bin/elfs_no_conflict.list, archive the logs, and accumulate "
            "functional coverage into a hardware-build-specific VCS database."
        )
    )
    parser.add_argument(
        "--build",
        choices=list(BUILDS),
        default="cheriot",
        help="hardware build: cheriot uses simv (default), rv32 uses simv32 with PMODE=0",
    )
    parser.add_argument(
        "--rvfi_max",
        type=positive_int,
        required=True,
        help="maximum number of RVFI packets passed to simv",
    )
    parser.add_argument(
        "--rv32",
        action="store_true",
        help=(
            "select runtime +PMODE=0 without changing --build; with the default "
            "cheriot build this tests RV32 compatibility on CHERIoT hardware"
        ),
    )
    parser.add_argument(
        "--cov_dir",
        default=DEFAULT_COV_DIR,
        help=(
            "coverage basename; append _cheriot.vdb or _rv32.vdb after "
            "removing an optional .vdb suffix (default: {}). Existing "
            "unsuffixed and PMODE-partitioned databases are not merged".format(
                DEFAULT_COV_DIR
            )
        ),
    )
    parser.add_argument(
        "--cov_tag",
        help=(
            "prefix used for the per-test coverage test names; defaults to a "
            "unique timestamp so repeated invocations never overwrite each other"
        ),
    )
    parser.add_argument(
        "--design_vdb",
        help=(
            "compile-time coverage database holding the design data, used as the "
            "merge base the first time --cov_dir is created "
            "(default: simv.vdb for cheriot, simv32.vdb for rv32)"
        ),
    )
    parser.add_argument(
        "--compile",
        action="store_true",
        help="run ./vcscomp -dii -nowave -cov before the sweep",
    )
    parser.add_argument(
        "--keep_run_cov",
        action="store_true",
        help="keep the raw per-invocation coverage database after merging",
    )
    parser.add_argument(
        "--continue_on_illegal_bin",
        action="store_true",
        help=(
            "pass -covg_cont_on_error to simv so a functional coverage "
            "illegal_bins hit is reported as a warning and the run continues, "
            "instead of aborting the simulation"
        ),
    )
    parser.add_argument(
        "--no_cov",
        action="store_true",
        help="disable coverage recording at run time",
    )
    parser.add_argument(
        "--cov_report",
        action="store_true",
        help="report the selected build in urgReport_cheriot or urgReport_rv32",
    )
    return parser.parse_args()


def extract_archive(archive, run_dir):
    with tarfile.open(archive, "r:gz") as tar:
        run_dir_resolved = run_dir.resolve()
        for member in tar.getmembers():
            member_path = (run_dir / member.name).resolve()
            if (
                member_path != run_dir_resolved
                and run_dir_resolved not in member_path.parents
            ):
                raise RuntimeError(
                    "archive member escapes the run directory: {}".format(member.name)
                )
        tar.extractall(run_dir)


def prepare_empty_dir(directory):
    if not directory.exists():
        directory.mkdir()
        return
    if not directory.is_dir() or directory.is_symlink():
        raise RuntimeError("{} exists but is not a regular directory".format(directory))

    for entry in directory.iterdir():
        if entry.is_dir() and not entry.is_symlink():
            shutil.rmtree(entry)
        else:
            entry.unlink()


def read_elf_list(list_path, elf_dir):
    if not list_path.is_file():
        raise FileNotFoundError("ELF list not found: {}".format(list_path))

    available_elfs = sorted(path for path in elf_dir.rglob("*.elf") if path.is_file())
    if not available_elfs:
        raise RuntimeError("no ELF files found in {}".format(elf_dir))

    elf_files = []
    selected = set()
    with list_path.open("r", encoding="utf-8") as list_file:
        for line_number, line in enumerate(list_file, 1):
            entry = line.strip()
            if not entry or entry.startswith("#"):
                continue

            entry_path = Path(entry)
            entry_posix = entry_path.as_posix()
            path_matches = []
            for elf_path in available_elfs:
                relative_path = elf_path.relative_to(elf_dir)
                if entry_path == relative_path or entry_posix.endswith(
                    "/{}".format(relative_path.as_posix())
                ):
                    path_matches.append(elf_path)

            if path_matches:
                longest_match = max(
                    len(path.relative_to(elf_dir).parts) for path in path_matches
                )
                matches = [
                    path
                    for path in path_matches
                    if len(path.relative_to(elf_dir).parts) == longest_match
                ]
            else:
                matches = [
                    path for path in available_elfs if path.name == entry_path.name
                ]

            unique_matches = list(dict.fromkeys(matches))
            if not unique_matches:
                raise FileNotFoundError(
                    "ELF listed at {}:{} was not found in {}: {}".format(
                        list_path, line_number, elf_dir, entry
                    )
                )
            if len(unique_matches) > 1:
                raise RuntimeError(
                    "ELF listed at {}:{} is ambiguous in {}: {}".format(
                        list_path, line_number, elf_dir, entry
                    )
                )

            elf_path = unique_matches[0]
            if elf_path not in selected:
                elf_files.append(elf_path)
                selected.add(elf_path)

    if not elf_files:
        raise RuntimeError("no ELF files listed in {}".format(list_path))
    return elf_files


def make_cov_tag():
    """Unique-per-invocation tag so accumulated test names never collide."""
    return "run_{}_{}".format(time.strftime("%Y%m%d_%H%M%S"), os.getpid())


def run_urg(command, run_dir):
    print("+ {}".format(" ".join(command)), flush=True)
    try:
        subprocess.run(command, cwd=run_dir, check=True)
    except FileNotFoundError:
        print("WARNING: urg not found in PATH", file=sys.stderr)
        return False
    except subprocess.CalledProcessError as error:
        print("WARNING: urg failed with exit code {}".format(error.returncode), file=sys.stderr)
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


def warn_if_design_is_newer(cov_dir, design_vdb):
    """Warn when the accumulated database predates the current build.

    The accumulated database carries the design data of the build it was first
    created from. Merging run data from a design that has been recompiled since
    then makes urg fall back on name matching, which silently drops the objects
    that no longer line up, so the accumulated scores stop being comparable.
    """
    if not (cov_dir.is_dir() and design_vdb.is_dir()):
        return
    if newest_mtime(design_vdb) <= newest_mtime(cov_dir):
        return
    print(
        "WARNING: {} is newer than {}; if the design was recompiled since the "
        "accumulated database was last merged, start a fresh --cov_dir instead "
        "of merging into stale design data".format(design_vdb.name, cov_dir),
        file=sys.stderr,
        flush=True,
    )


def merge_cov(run_vdb, cov_dir, design_vdb, run_dir):
    """Merge the raw database of this invocation into the persistent database.

    A raw simulation database only holds test data, so the merge base is the
    accumulated database when it already exists and the compile-time design
    database the very first time.
    """
    if not run_vdb.is_dir():
        print(
            "WARNING: no coverage data was produced in {}".format(run_vdb),
            file=sys.stderr,
        )
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

    command = [
        "urg",
        "-full64",
        "-dir",
        str(base),
        "-dir",
        str(run_vdb),
        "-dbname",
        str(tmp_dir),
        "-noreport",
    ]
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


def main():
    args = parse_args()
    run_dir = Path(__file__).resolve().parent
    archive = run_dir / "bin.tar.gz"
    elf_dir = run_dir / "bin"
    elf_list = elf_dir / "elfs_no_conflict.list"
    results = run_dir / "results"
    results_archive = run_dir / "results.tar.gz"

    cov_enabled = not args.no_cov
    build = args.build
    pmode = 0 if args.rv32 or build == "rv32" else 1
    simv_bin = "./" + BUILDS[build]["simv"]
    cov_dir = build_cov_dir(args.cov_dir, build)
    if not cov_dir.is_absolute():
        cov_dir = run_dir / cov_dir
    design_vdb = Path(args.design_vdb or BUILDS[build]["vdb"])
    if not design_vdb.is_absolute():
        design_vdb = run_dir / design_vdb
    cov_tag = sanitize_test_name(args.cov_tag or make_cov_tag())
    cov_temp = run_dir / "cov_temp"
    # Raw database for this invocation only; it is merged into cov_dir at the end.
    run_vdb = cov_temp / "cov_run_{}_{}.vdb".format(cov_tag, build)

    compile_command = ["./vcscomp", "-dii", "-nowave", "-cov"]
    print("+ {}".format(" ".join(compile_command)), flush=True)
    if args.compile:
        subprocess.run(compile_command, cwd=run_dir, check=True)
    else:
        print(
            "  (skipped: pass --compile to rebuild, otherwise {} is reused)".format(
                simv_bin
            ),
            flush=True,
        )

    if not (run_dir / simv_bin).is_file():
        print(
            "ERROR: {} not found, compile it with {}".format(
                simv_bin, " ".join(compile_command)
            ),
            file=sys.stderr,
        )
        return 1

    if cov_enabled:
        cov_temp.mkdir(parents=True, exist_ok=True)
        warn_if_design_is_newer(cov_dir, design_vdb)
        if run_vdb.exists():
            raise RuntimeError(
                "{} already exists; choose a different --cov_tag to preserve it".format(
                    run_vdb
                )
            )
        print(
            "Coverage: recording into {}, merging into {} ({})".format(
                run_vdb,
                cov_dir,
                "existing database" if cov_dir.is_dir() else "new database",
            ),
            flush=True,
        )

    if not archive.is_file():
        print("ERROR: {} not found".format(archive), file=sys.stderr)
        return 1

    print("Extracting {}".format(archive.name), flush=True)
    prepare_empty_dir(elf_dir)
    extract_archive(archive, run_dir)
    if not elf_dir.is_dir():
        print("ERROR: {} was not found after extraction".format(elf_dir), file=sys.stderr)
        return 1

    elf_files = read_elf_list(elf_list, elf_dir)
    print("Selected {} ELF file(s) from {}".format(len(elf_files), elf_list), flush=True)

    prepare_empty_dir(results)

    instr_gnt_wmax = random.randint(0, 1)
    instr_resp_wmax = random.randint(0, 1)
    data_gnt_wmax = random.randint(0, 2)
    data_resp_wmax = random.randint(0, 1)
    print(
        "WMAX: INSTR_GNT={}, INSTR_RESP={}, DATA_GNT={}, DATA_RESP={}".format(
            instr_gnt_wmax,
            instr_resp_wmax,
            data_gnt_wmax,
            data_resp_wmax,
        ),
        flush=True,
    )

    failed_tests = []
    archived = 0
    for elf_path in elf_files:
        relative_test = elf_path.relative_to(elf_dir).with_suffix("")
        test_arg = relative_test.as_posix()
        result_name = "__".join(relative_test.parts)

        for log_name in (RVFI_LOG, TRACE_LOG):
            stale_log = run_dir / log_name
            if stale_log.exists():
                stale_log.unlink()

        command = [
            simv_bin,
            "+TEST={}".format(test_arg),
            "+RVFI_MAX={}".format(args.rvfi_max),
            "+INSTR_GNT_WMAX={}".format(instr_gnt_wmax),
            "+INSTR_RESP_WMAX={}".format(instr_resp_wmax),
            "+DATA_GNT_WMAX={}".format(data_gnt_wmax),
            "+DATA_RESP_WMAX={}".format(data_resp_wmax),
            "+PMODE={}".format(pmode),
        ]
        if cov_enabled:
            command += [
                "-cm",
                COV_METRICS,
                "-cm_dir",
                str(run_vdb),
                "-cm_name",
                "{}__{}__pmode{}__{}".format(
                    cov_tag, build, pmode, sanitize_test_name(result_name)
                ),
            ]
            if args.continue_on_illegal_bin:
                # An illegal_bins hit is a runtime error that aborts the
                # simulation, which is the intended behaviour: every illegal bin
                # in sim/fcov marks a structural invariant of the design. Use
                # this only to survey how many distinct bins fire in one pass.
                command.append("-covg_cont_on_error")
        print("+ {}".format(" ".join(command)), flush=True)
        # A failing test must not abort the sweep: simv writes the coverage of
        # every test it has already run into run_vdb, and an aborted run still
        # contributes the data collected up to the abort. Stopping here would
        # throw all of it away, because run_vdb is only merged after the loop.
        completed = subprocess.run(command, cwd=run_dir)
        failure = None
        if completed.returncode != 0:
            failure = "{} exited with code {}".format(simv_bin, completed.returncode)

        for log_name, suffix in ((RVFI_LOG, "rvfi"), (TRACE_LOG, "trace")):
            log_path = run_dir / log_name
            if log_path.is_file():
                shutil.copy2(log_path, results / "{}.{}".format(result_name, suffix))
                archived += 1
            elif failure is None:
                failure = "simulation log {} was not produced".format(log_name)

        if failure is not None:
            print("ERROR: {}: {}".format(test_arg, failure), file=sys.stderr, flush=True)
            failed_tests.append(test_arg)

    if results_archive.exists():
        results_archive.unlink()
    with tarfile.open(results_archive, "w:gz") as tar:
        tar.add(results, arcname=results.name)

    print(
        "Archived {} log file(s) for {} test(s) in {}".format(
            archived, len(elf_files), results_archive
        )
    )

    exit_code = 0
    if failed_tests:
        print(
            "ERROR: {} of {} test(s) failed: {}".format(
                len(failed_tests), len(elf_files), ", ".join(failed_tests)
            ),
            file=sys.stderr,
            flush=True,
        )
        exit_code = 1

    if cov_enabled:
        if merge_cov(run_vdb, cov_dir, design_vdb, run_dir):
            print("Coverage accumulated in {}".format(cov_dir), flush=True)
            if not args.keep_run_cov and run_vdb.is_dir():
                shutil.rmtree(run_vdb)
            if args.cov_report:
                generate_cov_report(cov_dir, run_dir, build)
            else:
                print(
                    "Generate a report with: submit -i urg -full64 -dir {} "
                    "-report urgReport_{}".format(
                        cov_dir, build
                    ),
                    flush=True,
                )
        else:
            print(
                "ERROR: coverage merge failed, raw data kept in {}".format(run_vdb),
                file=sys.stderr,
            )
            exit_code = 1
    return exit_code


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, subprocess.CalledProcessError, tarfile.TarError) as error:
        print("ERROR: {}".format(error), file=sys.stderr)
        sys.exit(1)
