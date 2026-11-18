#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Shared runner for the directed RTL-bug tests in sim/tests_2.

Every sim/tests_2/<test>/run.py describes its test as a `Test` and calls
`main([TEST])`. `run_all.py` passes every test to the same `main`.

The flow, for any set of tests:
  1. Work directory: --work, or a fresh scratch directory
     ($KUDU_SCRATCH, default /home/scratch/fortress/$USER/kudu_temp,
     /tests_2_<timestamp>). Nothing is written to the repository.
  2. RTL builds: `submit -i ./vcscomp -nowave -outdir=...`, from sim/run for
     the stock testbench, or from a shadow tree (repository copy plus the
     test's patches / extra checker files) for tests that need one. --build
     reuses an existing stock build directory holding simv and simv32.
  3. Test programs: built locally with common/build_prog.sh.
  4. Simulations: packed into --jobs batches (default up to 10) of similar
     estimated run time; each batch is one `submit -i` job.
  5. Verdict per run, from the sim.log (plus the output of the test's `post`
     hook, if any):
       PASS   the pass regex matched
       XFAIL  every failing check maps to a bug the bug logs list as Open
       DEFER  every failing check maps to a Deferred/Waived bug
       FAIL   anything else (wrong result, timeout, crash, a failing check of a
              bug listed as Fixed, or a failing line no check explains)

Exit code: 0 when every run is PASS, 1 when the only failures are known bugs
(XFAIL/DEFER, i.e. the bug reproduces), 2 otherwise.
"""

import argparse
import hashlib
import importlib.util
import os
import re
import shlex
import shutil
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.dont_write_bytecode = True

COMMON = Path(__file__).resolve().parent
TESTS2 = COMMON.parent
SIM_ROOT = TESTS2.parent
REPO = SIM_ROOT.parent
RUN_DIR = SIM_ROOT / "run"
BUILD_PROG = COMMON / "build_prog.sh"
BUG_LOGS = [SIM_ROOT / "testplan" / n for n in ("bug_logs_1.md", "bug_logs_2.md", "bug_logs_3.md")]
DEFERRED = ("Deferred", "Waived")
VERDICTS = ("PASS", "XFAIL", "DEFER", "FAIL")
TRACE_FILES = ("trace_kudu_core.log", "rvfi_kudu_core.log")
FAIL_LINE = re.compile(r"\bFAIL\b")
SUMMARY_LINE = re.compile(r"SUMMARY FAIL|FAIL failures=")

# Memory wait-state presets shared by several tests.
DLY_DATA = ["+DATA_GNT_WMAX=3", "+DATA_RESP_WMAX=5"]
DLY_ALL3 = [f"+{k}_{p}_WMAX=3" for k in ("INSTR", "DATA") for p in ("GNT", "RESP")]
DLY_DBG = ["+INSTR_GNT_WMAX=2", "+INSTR_RESP_WMAX=2", "+DATA_GNT_WMAX=3", "+DATA_RESP_WMAX=3"]
DLY_SLOT1 = ["+INSTR_GNT_WMAX=3", "+INSTR_RESP_WMAX=5"] + DLY_DATA
T1M = ["+TIMEOUT=1000000"]
HW_BOTH = (("rv32", "simv32"), ("cheriot", "simv"))  # RV32 build, CHERIoT build at PMODE=0


class Run(object):
    """One simulation (or, with `script`, one shell command) of a test.

    simv:    "simv" or "simv32"; None for a script run
    flavour: build_prog.sh flavour (rv32, cheri, dbg, asm, plus +DEFINE=VAL
             suffixes); None when the run needs no test program
    script:  bash text executed in the run directory instead of a simulator;
             "$TEST_DIR", "$WORK" and "$REPO" are exported to it
    est:     estimated run time in seconds, for batch balancing
    """

    def __init__(self, variant, simv, flavour, plusargs=(), script=None, est=5):
        self.variant = variant
        self.simv = simv
        self.flavour = flavour
        self.plusargs = list(plusargs)
        self.script = script
        self.est = est


def rv32_both(args, est=5):
    """An RV32 program on both builds: simv32, and simv at PMODE=0."""
    return [Run(hw, sim, "rv32", ["+PMODE=0"] + args, est=est) for hw, sim in HW_BOTH]


def cheri_dly(args, est=5):
    """A CHERIoT program at PMODE=1, with and without data-side wait states."""
    return [Run("default", "simv", "cheri", ["+PMODE=1"] + args, est=est),
            Run("delayed", "simv", "cheri", ["+PMODE=1"] + args + DLY_DATA, est=est)]


class Shadow(object):
    """A testbench variant: the repository's rtl/ and sim/ with `patches`
    (unified diffs relative to the repository root, applied with patch -p1)
    and `extra` source files appended to the VCS file list."""

    def __init__(self, patches=(), extra=()):
        self.patches = [Path(p).resolve() for p in patches]
        self.extra = [Path(p).resolve() for p in extra]

    def key(self):
        digest = hashlib.sha1()
        for path in self.patches + self.extra:
            digest.update(path.name.encode())
            digest.update(path.read_bytes())
        return "shadow_" + digest.hexdigest()[:10]


class Test(object):
    """A directed test.

    name:       directory name under sim/tests_2 (also the program name)
    bugs:       KUDU ids the test reproduces
    runs:       list of Run
    passed:     regex whose presence means every check of a run passed
    checks:     (regex, KUDU id) pairs mapping each failing line to its bug
    shadow:     Shadow, if the stock testbench cannot reproduce the bug
    conf:       pipeline configuration the test needs ("0".."3"), or None
    post:       optional post(run_dir, sim_log_text) -> extra text, appended to
                the log before the verdict (e.g. a trace analysis)
    regression: include the test in run_full_regression.py's bug suite
                (only plain stock-testbench program tests qualify)
    known:      status of check ids that are not KUDU bugs in the bug logs,
                e.g. {"SAIL-ZBKB": "Waived"} for a documented model divergence
    """

    def __init__(self, name, bugs, runs, passed, checks=(), shadow=None, conf=None,
                 post=None, regression=None, known=None, src=None):
        self.name = name
        self.bugs = list(bugs)
        self.runs = runs
        self.passed_rx = passed
        self.passed = re.compile(passed, re.M)
        self.check_rx = list(checks)
        self.checks = [(re.compile(rx), bug) for rx, bug in checks]
        self.shadow = shadow
        self.conf = conf
        self.post = post
        self.known = dict(known or {})
        self.src = Path(src).resolve() if src else TESTS2 / name
        simple = (shadow is None and conf is None and post is None
                  and all(r.script is None and r.simv for r in runs))
        self.regression = simple if regression is None else (regression and simple)

    def build_key(self, conf):
        return (self.conf or conf, self.shadow.key() if self.shadow else None)


class Job(object):
    def __init__(self, test, run, build_key):
        self.test = test
        self.run = run
        self.build_key = build_key
        self.label = "{}.{}".format(test.name, run.variant)
        self.verdict = None
        self.detail = ""
        self.elapsed = 0.0


def load_tests(root=TESTS2):
    """Import every <root>/*/run.py and return their TEST objects, sorted by name."""
    tests = []
    for path in sorted(root.glob("*/run.py")):
        spec = importlib.util.spec_from_file_location("tests2_" + path.parent.name, str(path))
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        tests.append(module.TEST)
    return tests


def read_bug_status():
    """KUDU id -> 'Open', 'Deferred', 'Waived' or 'Fixed', from the bug-log summary tables."""
    status = {}
    for bug_log in BUG_LOGS:
        if not bug_log.is_file():
            continue
        for line in bug_log.read_text(errors="replace").splitlines():
            match = re.match(r"\|\s*(KUDU-\d+)\s*\|([^|]*)\|", line)
            if match and match[1] not in status:
                state = match[2]
                status[match[1]] = next((s for s in ("Open",) + DEFERRED if s in state), "Fixed")
    return status


def run_logged(command, cwd, log, env=None):
    with open(str(log), "w") as out:
        out.write("+ {}\n".format(" ".join(str(c) for c in command)))
        out.flush()
        return subprocess.run([str(c) for c in command], cwd=str(cwd), stdout=out,
                              stderr=subprocess.STDOUT, env=env).returncode


def make_shadow(shadow, dest):
    """Copy rtl/ and sim/{tb,run file lists} into dest, apply the patches, and
    append the extra sources to the file lists. Returns dest/sim/run."""
    shutil.copytree(str(REPO / "rtl"), str(dest / "rtl"), symlinks=True)
    shutil.copytree(str(SIM_ROOT / "tb"), str(dest / "sim" / "tb"), symlinks=True)
    for name in ("prim", "dw"):
        if (REPO / name).exists():
            (dest / name).symlink_to(REPO / name, target_is_directory=True)
    (dest / "sim" / "fcov").symlink_to(SIM_ROOT / "fcov", target_is_directory=True)
    run = dest / "sim" / "run"
    run.mkdir()
    for name in ("vcscomp", "kudu.vcs.f", "kudu_dw.vcs.f", "cm_hier.cfg"):
        shutil.copy2(str(RUN_DIR / name), str(run / name))
    for patch in shadow.patches:
        log = dest / ("patch_" + patch.name + ".log")
        if run_logged(["patch", "-p1", "--no-backup-if-mismatch", "-i", patch], dest, log):
            raise RuntimeError("patch {} does not apply; see {}".format(patch, log))
    for name in ("kudu.vcs.f", "kudu_dw.vcs.f"):
        with open(str(run / name), "a") as filelist:
            for extra in shadow.extra:
                filelist.write("\n{}\n".format(extra))
    return run


def compile_build(key, out, root):
    """Compile simv and simv32 for build key (conf, shadow key) into out."""
    conf, shadow_key = key
    out.mkdir(parents=True)
    src_run = RUN_DIR
    if shadow_key:
        shadow = next(s for s in root["shadows"] if s.key() == shadow_key)
        src_run = make_shadow(shadow, out / "src")
    command = ["submit", "-i", "./vcscomp", "-nowave"]
    if conf is not None:
        command.append("-conf" + conf)
    command.append("-outdir={}".format(out / "bin"))
    log = out / "compile.log"
    code = run_logged(command, src_run, log)
    missing = [s for s in ("simv", "simv32") if not (out / "bin" / s).is_file()]
    if code or missing:
        raise RuntimeError("compile failed for {} (exit {}, missing {}); see {}".format(
            key, code, missing or "none", log))
    return out / "bin"


def build_program(test, flavour, out):
    out.mkdir(parents=True)
    log = out / "build.log"
    code = run_logged(["bash", BUILD_PROG, flavour, test.src, out], out, log)
    if code or not (out / (test.src.name + ".vhx")).is_file():
        raise RuntimeError("program build failed for {} ({}); see {}".format(test.name, flavour, log))
    return out


def classify(job, text, status):
    test = job.test
    status = dict(status, **test.known)
    failing = [line.strip() for line in text.splitlines() if FAIL_LINE.search(line)]
    detailed = [line for line in failing if not SUMMARY_LINE.search(line)]
    failing = detailed or failing
    if test.passed.search(text) and not detailed:
        return "PASS", ""
    if not failing:
        return "FAIL", "no pass verdict and no failing check reported"
    failed_bugs, unmapped = set(), []
    for line in failing:
        ids = {kid for rx, kid in test.checks if rx.search(line)}
        failed_bugs |= ids
        if not ids:
            unmapped.append(line)
    known = ("Open",) + DEFERRED
    regressed = sorted(kid for kid in failed_bugs if status.get(kid) not in known)
    if unmapped or regressed:
        parts = []
        if regressed:
            parts.append("fixed bug(s) failing: " + ", ".join(regressed))
        if unmapped:
            parts.append("unexpected: " + unmapped[0][:120])
        return "FAIL", "; ".join(parts)
    detail = "; ".join("{}: {}".format(state.lower(), ", ".join(ids)) for state, ids in (
        (state, sorted(k for k in failed_bugs if status.get(k) == state)) for state in known)
        if ids)
    if any(status.get(kid) == "Open" for kid in failed_bugs):
        return "XFAIL", detail
    return "DEFER", detail


def finish(job, run_dir, status, keep_traces):
    log = run_dir / "sim.log"
    text = log.read_text(errors="replace") if log.is_file() else ""
    fields = (run_dir / "sim.exit").read_text().split() if (run_dir / "sim.exit").is_file() else []
    code = int(fields[0]) if fields else None
    if len(fields) >= 3:
        job.elapsed = float(fields[2]) - float(fields[1])
    if job.test.post and code is not None:
        try:
            extra = job.test.post(run_dir, text)
        except Exception as error:  # report, do not crash the other runs
            extra = "POST ERROR {}: {}\n".format(type(error).__name__, error)
        (run_dir / "post.log").write_text(extra)
        text += "\n" + extra
    if code is None:
        job.verdict, job.detail = "FAIL", "run did not complete (no sim.exit)"
    elif job.run.simv and "TB> Simulation timed out" in text:
        job.verdict, job.detail = "FAIL", "timeout"
    elif job.run.simv and "$finish at" not in text:
        job.verdict, job.detail = "FAIL", "simulation did not finish (exit {})".format(code)
    else:
        job.verdict, job.detail = classify(job, text, status)
    if job.verdict == "PASS" and not keep_traces:
        for name in TRACE_FILES:
            if (run_dir / name).is_file():
                (run_dir / name).unlink()
    return job


def run_command(job, run_dir, simv_dir):
    if job.run.script is not None:
        (run_dir / "run.sh").write_text(job.run.script)
        return "bash run.sh"
    args = list(job.run.plusargs)
    if job.run.flavour and not any(a.startswith("+TEST=") for a in args):
        args.insert(0, "+TEST=" + job.test.src.name)
    if not any(a.startswith("+ntb_random_seed") for a in args):
        args.append("+ntb_random_seed=1")
    return " ".join(shlex.quote(c) for c in [str(simv_dir / job.run.simv)] + args)


def write_batch(path, batch, work, builds):
    lines = ["#!/bin/bash", "export REPO={}".format(shlex.quote(str(REPO))),
             "export WORK={}".format(shlex.quote(str(work)))]
    for job in batch:
        run_dir = work / "runs" / job.label
        command = run_command(job, run_dir, builds.get(job.build_key))
        lines += [
            "cd {} || exit 1".format(shlex.quote(str(run_dir))),
            "export TEST_DIR={}".format(shlex.quote(str(job.test.src))),
            "echo {} > sim.log".format(shlex.quote("+ " + command)),
            "s=$(date +%s.%N)",
            "{} >> sim.log 2>&1 < /dev/null".format(command),
            "rc=$?",
            'echo "$rc $s $(date +%s.%N)" > sim.exit',
        ]
    path.write_text("\n".join(lines) + "\n")
    path.chmod(0o755)


def pack(jobs, count):
    batches = [[] for _ in range(max(1, min(count, len(jobs))))]
    loads = [0.0] * len(batches)
    for job in sorted(jobs, key=lambda j: -j.run.est):
        i = loads.index(min(loads))
        batches[i].append(job)
        loads[i] += job.run.est + 2
    return batches, loads


def parse_args(argv, tests):
    parser = argparse.ArgumentParser(
        description="Run sim/tests_2 directed test(s): " + ", ".join(t.name for t in tests[:4])
        + (" ..." if len(tests) > 4 else ""))
    parser.add_argument("--build", help="existing stock build directory with simv and simv32 "
                        "(from ./vcscomp -nowave -outdir=...); used for every test that needs "
                        "the stock testbench; shadow and --conf builds are always compiled")
    parser.add_argument("--work", help="new output directory (default: a fresh scratch dir)")
    parser.add_argument("--conf", choices=["0", "1", "2", "3"],
                        help="pipeline configuration (vcscomp -conf<N>) for builds made here")
    parser.add_argument("--only", help="run only runs whose label (<test>.<variant>) matches")
    parser.add_argument("--jobs", type=int, default=10, help="farm batches (default 10)")
    parser.add_argument("--list", action="store_true", help="list the runs and exit")
    parser.add_argument("--keep_traces", action="store_true",
                        help="keep trace/RVFI logs of passing runs")
    return parser.parse_args(argv)


def default_work():
    scratch = Path(os.environ.get("KUDU_SCRATCH",
                                  "/home/scratch/fortress/{}/kudu_temp".format(
                                      os.environ.get("USER", "unknown"))))
    return scratch / time.strftime("tests_2_%Y%m%d_%H%M%S")


def main(tests, argv=None):
    args = parse_args(sys.argv[1:] if argv is None else argv, tests)
    jobs = [Job(t, r, t.build_key(args.conf) if r.simv else None) for t in tests for r in t.runs]
    if args.only:
        rx = re.compile(args.only)
        jobs = [j for j in jobs if rx.search(j.label)]
    if not jobs:
        print("ERROR: no run selected", file=sys.stderr)
        return 2
    if args.list:
        for job in jobs:
            print("{:<8} {:<16} {}".format(job.run.simv or "script",
                                           job.run.flavour or "-", job.label))
        print("{} run(s)".format(len(jobs)))
        return 0

    work = Path(args.work).resolve() if args.work else default_work()
    try:
        work.mkdir(parents=True)
    except FileExistsError:
        print("ERROR: {} already exists; choose a new --work".format(work), file=sys.stderr)
        return 2
    print("Work directory: {}".format(work), flush=True)
    status = read_bug_status()

    keys = sorted({j.build_key for j in jobs if j.build_key}, key=str)
    stock = (args.conf, None)
    builds = {}
    if args.build:
        if stock in keys:
            builds[stock] = Path(args.build).resolve()
    root = {"shadows": [t.shadow for t in tests if t.shadow]}
    programs = sorted({(j.test.name, j.run.flavour) for j in jobs if j.run.flavour})
    by_name = {t.name: t for t in tests}
    errors = []
    prog_dirs = {}
    with ThreadPoolExecutor(max_workers=8) as pool:
        futures = {}
        for i, key in enumerate(k for k in keys if k not in builds):
            print("Compiling build {} ({}) ...".format(i, key), flush=True)
            futures[pool.submit(compile_build, key, work / "builds" / "b{}".format(i), root)] = \
                ("build", key)
        for name, flavour in programs:
            out = work / "programs" / "{}.{}".format(name, re.sub(r"[^\w.=-]", "_", flavour))
            futures[pool.submit(build_program, by_name[name], flavour, out)] = \
                ("prog", (name, flavour))
        for future in as_completed(futures):
            kind, key = futures[future]
            try:
                (builds if kind == "build" else prog_dirs)[key] = future.result()
            except Exception as error:
                errors.append(str(error))
    for error in errors:
        print("ERROR: {}".format(error), file=sys.stderr)

    results, runnable = [], []
    for job in jobs:
        if job.build_key and job.build_key not in builds:
            job.verdict, job.detail = "FAIL", "RTL build failed"
        elif job.run.flavour and (job.test.name, job.run.flavour) not in prog_dirs:
            job.verdict, job.detail = "FAIL", "test program build failed"
        else:
            run_dir = work / "runs" / job.label
            run_dir.mkdir(parents=True)
            if job.run.flavour:
                (run_dir / "bin").symlink_to(prog_dirs[(job.test.name, job.run.flavour)],
                                             target_is_directory=True)
            runnable.append(job)
            continue
        results.append(job)

    (work / "batches").mkdir()
    batches, loads = pack(runnable, args.jobs)
    if runnable:
        print("Running {} run(s) in {} farm job(s), estimated {:.0f}-{:.0f}s each".format(
            len(runnable), len(batches), min(loads), max(loads)), flush=True)
    lock = threading.Lock()

    def run_batch(index, batch):
        script = work / "batches" / "batch_{:02d}.sh".format(index)
        write_batch(script, batch, work, builds)
        run_logged(["submit", "-i", script], work / "batches", script.with_suffix(".log"))
        for job in batch:
            run_dir = work / "runs" / job.label
            for _ in range(12):  # results written on the farm host can lag over NFS
                if "sim.exit" in os.listdir(str(run_dir)):
                    break
                time.sleep(5)
            finish(job, run_dir, status, args.keep_traces)
            with lock:
                results.append(job)
                print("{:<5} {:<52} {:>5.0f}s {}".format(job.verdict, job.label, job.elapsed,
                                                       job.detail), flush=True)

    with ThreadPoolExecutor(max_workers=max(1, len(batches))) as pool:
        for future in as_completed([pool.submit(run_batch, i, b)
                                    for i, b in enumerate(batches) if b]):
            future.result()

    order = {j.label: i for i, j in enumerate(jobs)}
    results.sort(key=lambda j: order[j.label])
    counts = {v: sum(j.verdict == v for j in results) for v in VERDICTS}
    lines = ["{:<5} {:<52} {}".format(j.verdict, j.label, j.detail) for j in results]
    lines.append("")
    lines.append("Summary: {} run(s): {} PASS, {} XFAIL (open bugs), {} DEFER "
                 "(deferred/waived bugs), {} FAIL".format(len(results), counts["PASS"],
                                                          counts["XFAIL"], counts["DEFER"],
                                                          counts["FAIL"]))
    (work / "results.txt").write_text("\n".join(lines) + "\n")
    print("\n".join(lines[-1:]) + "\nResults: {}".format(work / "results.txt"), flush=True)
    if counts["FAIL"] or errors:
        return 2
    return 1 if counts["XFAIL"] or counts["DEFER"] else 0
