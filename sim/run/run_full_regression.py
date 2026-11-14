#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Full functional regression, without coverage, run in parallel on LSF.

Runs three suites against one fresh build of the current rtl/:

  mini   the ./run_mini_regression tests plus the directed CSR tests
  riscv  the riscv-tests suite (self-checking through tohost)
  bug    the KUDU-0xx reproducers in sim/tests/rtl_bug_*/

The mini and riscv lists come from run_cov_regression.py so both scripts stay in
sync. The simulations are packed into --lsf_jobs batches (default 10) of
similar estimated run time, and each batch is one `submit -i` job that runs its
simulations back to back; all batches are submitted at once. This avoids paying
the LSF dispatch overhead (about a minute) for every simulation. Compilation
also goes through `submit -i`; test programs are
built locally in private mirrors, so sim/run/bin and sim/tests/work are never
written. Run it locally from any directory with the VCS modules loaded:

    source ../run_dii/load_module_vcs
    ./run_full_regression.py                 # everything, 10 LSF jobs
    ./run_full_regression.py --suite bug --lsf_jobs 4
    ./run_full_regression.py --times_from <old work dir>   # measured balancing
    ./run_full_regression.py --list --only isa_test

Verdicts:
  PASS   test passed (mini tests with a cheriot-ibex golden must also match it)
  XFAIL  every failing check belongs to a known bug, at least one of them Open
  DEFER  every failing check belongs to a bug that is Deferred or Waived
  FAIL   anything else: wrong result, timeout, crash, trace mismatch, or a
         failing check of a bug that the bug logs list as Fixed
Bug status comes from the summary tables of bug_logs.md and bug_logs_2.md.
A note is printed when a check for an Open or Deferred bug passes, which usually
means the bug has been fixed and the bug log needs updating. The script exits 1
if any test FAILs.

Each invocation writes to a new --work_dir (default
temp_full_regression/run_<timestamp>). Traces of passing tests are deleted
unless --keep_traces is given; traces of failing tests are always kept.
"""

import argparse
import os
import re
import shlex
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

RUN_DIR = Path(__file__).resolve().parent
SIM_ROOT = RUN_DIR.parent
sys.dont_write_bytecode = True  # keep __pycache__ out of sim/run
sys.path.insert(0, str(RUN_DIR))
import run_cov_regression as cov_regr  # noqa: E402  (shared mini/riscv lists)

BUG_LOGS = [SIM_ROOT / "testplan" / name for name in ("bug_logs.md", "bug_logs_2.md")]
DEFERRED = ("Deferred", "Waived")
VERDICTS = ("PASS", "XFAIL", "DEFER", "FAIL")
IBEX_DIR = SIM_ROOT / "run_ibex"
TRACE_FILES = ("trace_kudu_core.log", "trace_kudu_core.clog", "rvfi_kudu_core.log")

# Same pairs and options as ./run_mini_diff. isa_test2a and dbg_test1 have no
# usable golden (interrupt timing differs from cheriot-ibex).
MINI_GOLDENS = {
    "coremark.rv32o3": ("trace.coremark.rv32o3.clog", []),
    "coremark.cheriot": ("trace.coremark.cheriot.clog", []),
    "isa_test1": ("trace.isa_test1.clog", ["--isa-test1-clc-tag"]),
    "isa_test1a": ("trace.isa_test1a.clog", []),
    "isa_test2": ("trace.isa_test2.clog", []),
}

# Estimated simulator CPU seconds (from earlier sim.log "CPU Time" lines), used
# to pack the simulations into evenly loaded LSF batches. First match wins.
EST_SECONDS = [
    ("step_exec", 400), ("coremark.cheriot", 120), ("isa_test_csr", 120), ("rv32_test_csr", 85),
    ("coremark", 75), ("rtl_bug_alt_err", 70), ("rtl_bug_issuer_debug", 17),
    ("rtl_bug_debug_mode", 13), ("rtl_bug_jalr_odd_epc", 12),
    ("rtl_bug_fetch_slot1_err", 11), ("dbg_test1", 8), ("rtl_bug_csr_rmw", 7),
    ("rtl_bug_umode_priv", 7), ("isa_test2.", 5),
]
EST_DEFAULT = 2
EST_PER_SIM = 2  # simulator start-up and licence checkout
CPU_TIME = re.compile(r"CPU Time:\s*([0-9.]+)")

DLY_DATA = ["+DATA_GNT_WMAX=3", "+DATA_RESP_WMAX=5"]
DLY_ALL3 = [f"+{k}_{p}_WMAX=3" for k in ("INSTR", "DATA") for p in ("GNT", "RESP")]
DLY_DBG = ["+INSTR_GNT_WMAX=2", "+INSTR_RESP_WMAX=2", "+DATA_GNT_WMAX=3", "+DATA_RESP_WMAX=3"]
DLY_SLOT1 = ["+INSTR_GNT_WMAX=3", "+INSTR_RESP_WMAX=5"] + DLY_DATA

BUILD_SCRIPTS = {"rv32": "build_test_rv32.sh", "cheri": "build_test.sh", "dbg": "build_dbg_test.sh"}


class BugTest(object):
    """A self-checking directed test in sim/tests: an rtl_bug_* reproducer (mirroring
    the settings of its run.py/README) or a test with no bug mapping (checks empty).

    runs:   (variant, simulator, program flavour, plusargs)
    passed: regex whose presence means every check passed
    checks: (regex, KUDU id) mapping each failing check line to its bug
    """

    def __init__(self, name, runs, passed, checks):
        self.name = name
        self.runs = runs
        self.passed = re.compile(passed)
        self.checks = [(re.compile(rx), bug) for rx, bug in checks]


def _rv32_both(args):
    return [("rv32", "simv32", "rv32", ["+PMODE=0"] + args),
            ("cheriot", "simv", "rv32", ["+PMODE=0"] + args)]


def _cheri_dly(args):
    return [("default", "simv", "cheri", ["+PMODE=1"] + args),
            ("delayed", "simv", "cheri", ["+PMODE=1"] + args + DLY_DATA)]


T1M = ["+TIMEOUT=1000000"]

BUG_TESTS = [
    BugTest("rtl_bug_csr_rmw",
            [(hw + "_" + v, sim, "rv32", ["+PMODE=0"] + T1M + d)
             for hw, sim in (("rv32", "simv32"), ("cheriot", "simv"))
             for v, d in (("default", []), ("delayed", DLY_ALL3))],
            r"CSR RMW PASS failures=0x0+ cases=0x0000001b", [(r"", "KUDU-001")]),
    BugTest("rtl_bug_trap_csr_values",
            [("rv32", "simv32", "rv32", ["+PMODE=0"] + T1M)],
            r"TRAP CSR VALUES PASS failures=0x0+ cases=0x00000006",
            [(r"\bdret_", "KUDU-004"), (r"\becall_mtval\b", "KUDU-005")]),
    BugTest("rtl_bug_rtype_rev8_reserved",
            [("rv32", "simv32", "rv32", ["+PMODE=0"] + T1M)],
            r"RTYPE REV8 RESERVED .* PASS", [(r"", "KUDU-006")]),
    BugTest("rtl_bug_misaligned_amo", _rv32_both(T1M),
            r"MISALIGNED AMO PASS failures=0x0+ cases=0x00000002", [(r"", "KUDU-007")]),
    BugTest("rtl_bug_amo_access_fault", _rv32_both(T1M),
            r"AMO ACCESS FAULT PASS failures=0x0+ cases=0x00000001", [(r"", "KUDU-008")]),
    BugTest("rtl_bug_trvk_boundary",
            [("cheriot", "simv", "cheri", ["+PMODE=1"] + T1M)],
            r"TRVK_BOUNDARY PASS failures=0x0+ cases=0x00000002", [(r"", "KUDU-009")]),
    BugTest("rtl_bug_mret_asr_mtval",
            [("cheriot", "simv", "cheri", ["+PMODE=1"] + T1M)],
            r"MRET_ASR_MTVAL PASS failures=0x0+ cases=0x00000001", [(r"", "KUDU-010")]),
    BugTest("rtl_bug_jal_pdt_off",
            [("rv32", "simv32", "rv32", ["+PMODE=0"] + T1M)],
            r"JAL PDT OFF .* PASS", [(r"", "KUDU-011")]),
    BugTest("rtl_bug_debug_irq_not_ignored",
            [("cheriot", "simv", "dbg",
              ["+PMODE=1", "+DBGROM=debug_rom", "+INTR_RATE=6", "+TIMEOUT=300000"])],
            r"DEBUG IRQ PASS cases=0x00000001", [(r"", "KUDU-012")]),
    BugTest("rtl_bug_sc_forwarding",
            _rv32_both(T1M) + [("cheriot_delayed", "simv", "rv32", ["+PMODE=0"] + T1M + DLY_DATA)],
            r"SC FORWARDING PASS failures=0x0+ cases=0x00000002", [(r"", "KUDU-014")]),
    BugTest("rtl_bug_cap_misaligned_mtval", _cheri_dly(T1M),
            r"CAP ALIGN MTVAL PASS failures=0x0+ cases=0x00000002", [(r"", "KUDU-015")]),
    BugTest("rtl_bug_mshwm_csr_store_order", _cheri_dly(T1M),
            r"MSHWM ORDER PASS failures=0 cases=6",
            [(r"^FAIL store-csrw-", "KUDU-016")]),
    BugTest("rtl_bug_csr_asr_allowlist", _cheri_dly(T1M),
            r"CSR ASR PASS failures=0 cases=8",
            [(r"^FAIL csrw 0x0b[08][02]\b", "KUDU-017"), (r"^FAIL csr[rw] 0x0323\b", "KUDU-018")]),
    BugTest("rtl_bug_minstret_write_order", _cheri_dly(T1M),
            r"MINSTRET INCREMENT PASS failures=0 cases=1", [(r"", "KUDU-019")]),
    BugTest("rtl_bug_misa_value",
            [("rv32", "simv32", "rv32", T1M),
             ("pmode0", "simv", "rv32", ["+PMODE=0"] + T1M),
             ("pmode1", "simv", "cheri", ["+PMODE=1"] + T1M)],
            r"MISA VALUE .* PASS", [(r"", "KUDU-020")]),
    BugTest("rtl_bug_debug_mode",
            [(v, "simv", "dbg", ["+PMODE=1", "+DBGROM=debug_rom", "+TIMEOUT=400000"] + d)
             for v, d in (("default", []), ("delayed", DLY_DBG))],
            r"DEBUG MODE SUMMARY PASS",
            [(r"DEBUG MODE D1[ab] ", "KUDU-021"), (r"DEBUG MODE D2 ", "KUDU-022"),
             (r"DEBUG MODE D3 ", "KUDU-023"), (r"DEBUG MODE D4 ", "KUDU-024"),
             (r"DEBUG MODE P1 ", "KUDU-025")]),
    BugTest("rtl_bug_issuer_debug",
            [(v, "simv", "dbg", ["+PMODE=1", "+DBGROM=debug_rom", "+INTR_RATE=6",
                                 "+TIMEOUT=400000"] + d)
             for v, d in (("default", []), ("delayed", DLY_DBG))],
            r"ISSUER DBG SUMMARY PASS",
            [(r"ISSUER DBG I1 ", "KUDU-026"), (r"ISSUER DBG I2 ", "KUDU-028"),
             (r"ISSUER DBG I3 ", "KUDU-029"), (r"ISSUER DBG I4 ", "KUDU-030"),
             (r"ISSUER DBG I5 ", "KUDU-003"), (r"ISSUER DBG I6 ", "KUDU-027")]),
    BugTest("rtl_bug_umode_priv",
            [(hw + "_" + v, sim, "rv32", ["+PMODE=0", "+INTR_RATE=3"] + T1M + d)
             for hw, sim in (("rv32", "simv32"), ("cheriot", "simv"))
             for v, d in (("default", []), ("delayed", DLY_ALL3))],
            r"UPRIV PASS failures=0 cases=4",
            [(r"UPRIV [AB] ", "KUDU-034"), (r"UPRIV C ", "KUDU-038")]),
    BugTest("rtl_bug_debug_ecall",
            [(v, "simv", "dbg", ["+PMODE=1", "+DBGROM=debug_rom", "+TIMEOUT=400000"] + d)
             for v, d in (("default", []), ("delayed", DLY_DBG))],
            r"DEBUG ECALL PASS failures=0 cases=2", [(r"DEBUG ECALL E1 ", "KUDU-035")]),
    BugTest("rtl_bug_jalr_odd_epc",
            [(hw + "_" + v, sim, "rv32", ["+PMODE=0", "+INTR_RATE=4"] + T1M + d)
             for hw, sim in (("rv32", "simv32"), ("cheriot", "simv"))
             for v, d in (("default", []), ("delayed", DLY_ALL3))],
            r"JALR ODD EPC PASS failures=0 cases=3", [(r"JALR ODD EPC J1 ", "KUDU-039")]),
    BugTest("rtl_bug_halt_step_cause",
            [(v, "simv", "dbg", ["+PMODE=1", "+DBGROM=debug_rom", "+TIMEOUT=400000"] + d)
             for v, d in (("default", []), ("delayed", DLY_DBG))],
            r"HALT STEP CAUSE PASS failures=0 cases=3", [(r"HALT STEP CAUSE H1 ", "KUDU-040")]),
    # dcsr.step over mixed workloads; results must match unstepped reference runs
    BugTest("step_exec",
            [(v, "simv", "dbg", ["+PMODE=1", "+DBGROM=debug_rom", "+TIMEOUT=10000000"] + d)
             for v, d in (("default", []), ("delayed", DLY_ALL3))],
            r"STEP EXEC PASS failures=0x0+\b", []),
    BugTest("rtl_bug_fetch_slot1_err",
            [(hw + "_" + v, sim, "rv32",
              ["+PMODE=0", "+INSTR_ERR_ADDR=80010060", "+TIMEOUT=300000"] + d)
             for hw, sim in (("rv32", "simv32"), ("cheriot", "simv"))
             for v, d in (("default", []), ("delayed", DLY_SLOT1))],
            r"FSLOT1 PASS failures=", [(r"^FSLOT1_KUDU013_SLOT1_ERR ", "KUDU-013")]),
    BugTest("rtl_bug_alt_err",
            [(hw + "_" + v, sim, "rv32",
              ["+PMODE=0", "+INSTR_ERR_ADDR=80010100", "+TIMEOUT=3000000"] + d)
             for hw, sim in (("rv32", "simv32"), ("cheriot", "simv"))
             for v, d in (("default", []), ("delayed", DLY_SLOT1))],
            r"ALTERR PASS failures=0x0+\b", [(r"^ALTERR FAIL KUDU013 ", "KUDU-013")]),
    BugTest("rtl_bug_misaligned_sc_rv32",
            [(hw + "_" + v, sim, "rv32", ["+PMODE=0"] + T1M + d)
             for hw, sim in (("rv32", "simv32"), ("cheriot", "simv"))
             for v, d in (("default", []), ("delayed", DLY_DATA))],
            r"MISALIGNED SC RV32 PASS failures=0 cases=7", [(r"^FAIL misaligned-sc ", "KUDU-031")]),
    BugTest("rtl_bug_amo_cheri_fault", _cheri_dly(T1M),
            r"AMO CHERI FAULT PASS failures=0 cases=8",
            [(r"^FAIL amo-rd ", "KUDU-032"), (r"^FAIL amo-mpie ", "KUDU-036")]),
    BugTest("rtl_bug_dcache_split_store",
            [(hw + "_" + v, sim, flavour, [pm] + T1M + d)
             for hw, sim, flavour, pm in (("rv32", "simv32", "rv32", "+PMODE=0"),
                                          ("pmode0", "simv", "rv32", "+PMODE=0"),
                                          ("pmode1", "simv", "cheri", "+PMODE=1"))
             for v, d in (("default", []), ("delayed", DLY_DATA))],
            r"DCACHE SPLIT STORE PASS failures=0 cases=[34]", [(r"^FAIL split-store ", "KUDU-033")]),
    BugTest("rtl_bug_sc_mshwm", _cheri_dly(T1M),
            r"SC MSHWM PASS failures=0 cases=4", [(r"^FAIL sc-mshwm ", "KUDU-037")]),
    BugTest("rtl_bug_csr_mtval_mstatush",
            [("rv32", "simv32", "rv32", ["+PMODE=0"] + T1M)]
            + [(pm + "_" + v, "simv", flavour, ["+PMODE=" + pm[-1]] + T1M + d)
               for pm, flavour in (("pmode0", "rv32"), ("pmode1", "cheri"))
               for v, d in (("default", []), ("delayed", DLY_DATA))],
            r"CSR MTVAL MSTATUSH PMODE=\S+ PASS failures=0 cases=16",
            [(r"^FAIL MTVAL ", "KUDU-041"), (r"^FAIL MSTATUSH ", "KUDU-042"),
             (r"^FAIL CDBG ", "KUDU-043")]),
]

FAIL_LINE = re.compile(r"\bFAIL\b")
SUMMARY_LINE = re.compile(r"SUMMARY FAIL|FAIL failures=")


class Job(object):
    """One simulation in the work directory."""

    def __init__(self, suite, label, simv, args, bindir, test=None, golden=None,
                 checker=None):
        self.suite = suite
        self.label = label
        self.simv = simv
        self.args = args
        self.bindir = bindir        # None: sim/run/bin
        self.test = test            # cov_regr.Test for mini/riscv
        self.golden = golden
        self.checker = checker      # BugTest for the bug suite
        self.verdict = None
        self.detail = ""
        self.notes = []
        self.failed_bugs = None     # KUDU ids with a failing check (bug suite)
        self.elapsed = 0.0

    def estimate(self, measured):
        if self.label in measured:
            return measured[self.label] + EST_PER_SIM
        return next((s for key, s in EST_SECONDS if key in self.label), EST_DEFAULT) + EST_PER_SIM


def read_bug_status():
    """KUDU id -> 'Open', 'Deferred', 'Waived' or 'Fixed', from the bug-log summary tables."""
    status = {}
    for bug_log in BUG_LOGS:
        if not bug_log.is_file():
            continue
        for line in bug_log.read_text(errors="replace").splitlines():
            # Only the summary table has a status column; later tables reuse
            # the KUDU ids, so the first row of each id wins.
            match = re.match(r"\|\s*(KUDU-\d+)\s*\|([^|]*)\|", line)
            if match and match[1] not in status:
                state = match[2]
                status[match[1]] = next((s for s in ("Open",) + DEFERRED if s in state),
                                        "Fixed")
    return status


def build_jobs(args):
    jobs = []
    suites = ["mini", "riscv", "bug"] if "all" in args.suite else args.suite
    cov_suites = [s for s in suites if s in ("mini", "riscv")]
    if cov_suites:
        for test in cov_regr.build_test_list(cov_suites, args.riscv_timeout, args.build):
            simv = cov_regr.BUILDS[test.build]["simv"]
            golden = MINI_GOLDENS.get(test.name) if test.suite == "mini" else None
            jobs.append(Job(test.suite, test.run_label, simv,
                            ["+TEST=" + test.name] + test.args, None,
                            test=test, golden=golden))
    if "bug" in suites:
        for bug in BUG_TESTS:
            for variant, simv, flavour, plusargs in bug.runs:
                if args.build != "all" and (simv == "simv32") != (args.build == "rv32"):
                    continue
                jobs.append(Job("bug", "{}.{}".format(bug.name, variant), simv,
                                ["+TEST=" + bug.name] + plusargs,
                                (bug.name, flavour), checker=bug))
    if args.only:
        pattern = re.compile(args.only)
        jobs = [job for job in jobs if pattern.search(job.label)]
    if args.skip:
        pattern = re.compile(args.skip)
        jobs = [job for job in jobs if not pattern.search(job.label)]
    return jobs


def run_logged(command, cwd, log, env=None):
    with open(str(log), "w") as out:
        out.write("+ {}\n".format(" ".join(str(c) for c in command)))
        out.flush()
        return subprocess.run([str(c) for c in command], cwd=str(cwd), stdout=out,
                              stderr=subprocess.STDOUT, env=env).returncode


def compile_simv(args, build_dir):
    command = ["submit", "-i", "./vcscomp", "-nowave", "-outdir={}".format(build_dir)]
    if args.conf is not None:
        command.insert(4, "-conf" + args.conf)
    log = build_dir.parent / "compile.log"
    build_dir.mkdir(parents=True)
    code = run_logged(command, RUN_DIR, log)
    missing = [s for s in ("simv", "simv32") if not (build_dir / s).is_file()]
    if code or missing:
        raise RuntimeError("compilation failed (exit {}, missing {}); see {} and {}/compile_*.log"
                           .format(code, missing or "none", log, build_dir))


def build_program(name, flavour, prog_root, env):
    """Build one test program in a private mirror of sim/tests and sim/scripts."""
    mirror = prog_root / "{}.{}".format(name, flavour)
    (mirror / "tests").mkdir(parents=True)
    (mirror / "run" / "bin").mkdir(parents=True)
    (mirror / "scripts").symlink_to(SIM_ROOT / "scripts", target_is_directory=True)
    tests = SIM_ROOT / "tests"
    for item in ("csrc_cheri", "csrc_rv32", "link_test.ld", "link_test_rv32.ld",
                 "link_dbgrom.ld", name):
        (mirror / "tests" / item).symlink_to(tests / item)
    log = mirror / "build.log"
    code = run_logged(["bash", "../scripts/" + BUILD_SCRIPTS[flavour], name],
                      mirror / "tests", log, env)
    if code or not (mirror / "run" / "bin" / (name + ".vhx")).is_file():
        raise RuntimeError("program build failed for {} ({}); see {}".format(name, flavour, log))
    return mirror / "run" / "bin"


def classify_bug(job, text, status):
    bug = job.checker
    failing = [line.strip() for line in text.splitlines() if FAIL_LINE.search(line.strip())]
    detailed = [line for line in failing if not SUMMARY_LINE.search(line)]
    failing = detailed or failing

    failed_bugs = set()
    unmapped = []
    for line in failing:
        ids = {kid for rx, kid in bug.checks if rx.search(line)}
        failed_bugs |= ids
        if not ids:
            unmapped.append(line)

    job.failed_bugs = failed_bugs
    if bug.passed.search(text):
        return "PASS", ""
    if not failing:
        return "FAIL", "no pass verdict and no failing check reported"
    known = ("Open",) + DEFERRED
    regressed = sorted(kid for kid in failed_bugs if status.get(kid) not in known)
    if unmapped or regressed:
        parts = []
        if regressed:
            parts.append("fixed bug(s) failing: " + ", ".join(regressed))
        if unmapped:
            parts.append("unexpected: " + unmapped[0])
        return "FAIL", "; ".join(parts)
    detail = "; ".join("{}: {}".format(state.lower(), ", ".join(ids)) for state, ids in (
        (state, sorted(k for k in failed_bugs if status.get(k) == state)) for state in known)
        if ids)
    if any(status.get(kid) == "Open" for kid in failed_bugs):
        return "XFAIL", detail
    return "DEFER", detail


def check_trace(job, run_dir):
    trace = run_dir / "trace_kudu_core.log"
    if not trace.is_file():
        return "no trace_kudu_core.log for the golden comparison"
    subprocess.run([str(SIM_ROOT / "scripts" / "clean_trace.pl"), trace.name],
                   cwd=str(run_dir), stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    # diff_files.py's isa_test1 rule requires the run_mini_regression naming.
    clog = "trace.{}.{}.clog".format(job.test.name, job.test.variant)
    if not (run_dir / "trace_kudu_core.clog").is_file():
        return "clean_trace.pl produced no trace_kudu_core.clog"
    (run_dir / "trace_kudu_core.clog").replace(run_dir / clog)
    golden, options = job.golden
    result = subprocess.run(
        [sys.executable, str(SIM_ROOT / "scripts" / "diff_files.py"), "--ignore-extra-lines", "5"]
        + options + [clog, str(IBEX_DIR / golden)],
        cwd=str(run_dir), stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        universal_newlines=True)
    (run_dir / "trace_diff.txt").write_text(result.stdout)
    if "Files match (with given ignore rules)." not in result.stdout:
        return "trace differs from run_ibex/{} (see trace_diff.txt)".format(golden)
    return None


def setup_run(job, work, prog_bins):
    run_dir = work / "runs" / job.label
    run_dir.mkdir(parents=True)
    bindir = prog_bins[job.bindir] if job.bindir else RUN_DIR / "bin"
    (run_dir / "bin").symlink_to(bindir, target_is_directory=True)
    return run_dir


def sim_command(job, simv_dir):
    return [str(simv_dir / job.simv)] + job.args + ["+ntb_random_seed=1"]


def has_sim_output(text):
    return "Compiler version" in text or "$finish" in text


def write_batch_script(path, batch, work, simv_dir):
    """A bash script that runs the batch's simulations back to back.

    Each run gets its own sim.log, plus sim.exit holding '<exit code> <start> <end>',
    so one failing simulation never hides the rest of the batch.
    """
    lines = ["#!/bin/bash"]
    for job in batch:
        run_dir = work / "runs" / job.label
        command = " ".join(shlex.quote(c) for c in sim_command(job, simv_dir))
        lines += [
            "cd {} || exit 1".format(shlex.quote(str(run_dir))),
            "echo {} > sim.log".format(shlex.quote("+ " + command)),
            "s=$(date +%s.%N)",
            "{} >> sim.log 2>&1 < /dev/null".format(command),
            "rc=$?",
            'echo "$rc $s $(date +%s.%N)" > sim.exit',
        ]
    path.write_text("\n".join(lines) + "\n")
    path.chmod(0o755)


def run_single(job, run_dir, simv_dir):
    """Rerun one simulation as its own LSF job (after a batch lost it)."""
    log = run_dir / "sim.log"
    started = time.time()
    code = run_logged(["submit", "-i"] + sim_command(job, simv_dir), run_dir, log)
    job.elapsed = time.time() - started
    return code, log.read_text(errors="replace")


def finish_job(job, run_dir, code, text, status, keep_traces):
    if "TB> Simulation timed out" in text:
        job.verdict, job.detail = "FAIL", "timeout"
    elif "$finish at" not in text:
        job.verdict, job.detail = "FAIL", "simulation did not finish (exit {})".format(code)
    elif code:
        job.verdict, job.detail = "FAIL", "simulator exited with code {}".format(code)
    elif job.checker:
        job.verdict, job.detail = classify_bug(job, text, status)
    else:
        job.verdict, job.detail = "PASS", ""
        if job.test.name in cov_regr.CSR_TESTS:
            if "CSR test failed" in text or "CSR test passed" not in text:
                job.verdict, job.detail = "FAIL", "CSR test did not report 'CSR test passed'"
        elif job.test.self_checking and "RISCV Test passed" not in text:
            job.verdict, job.detail = "FAIL", "tohost did not report 'RISCV Test passed'"
        if job.verdict == "PASS" and job.golden:
            mismatch = check_trace(job, run_dir)
            if mismatch:
                job.verdict, job.detail = "FAIL", mismatch

    if job.verdict == "PASS" and not keep_traces:
        for path in [run_dir / name for name in TRACE_FILES] + list(run_dir.glob("trace.*.clog")):
            if path.is_file():
                path.unlink()
    return job


def pack_batches(jobs, count, measured):
    """Longest-processing-time-first packing into `count` evenly loaded batches."""
    batches = [[] for _ in range(min(count, len(jobs)))]
    loads = [0.0] * len(batches)
    for job in sorted(jobs, key=lambda j: -j.estimate(measured)):
        i = loads.index(min(loads))
        batches[i].append(job)
        loads[i] += job.estimate(measured)
    return batches, loads


def run_batch(index, batch, work, simv_dir, status, keep_traces, report):
    """Run one batch as a single LSF job, reporting each test as soon as it ends."""
    script = work / "batches" / "batch_{:02d}.sh".format(index)
    write_batch_script(script, batch, work, simv_dir)
    log = open(str(script.with_suffix(".log")), "w")
    proc = subprocess.Popen(["submit", "-i", str(script)], cwd=str(work / "batches"),
                            stdout=log, stderr=subprocess.STDOUT)
    pending = list(batch)

    def collect(final):
        for job in list(pending):
            run_dir = work / "runs" / job.label
            exit_file = run_dir / "sim.exit"
            # Listing the directory refreshes NFS's cached "file does not exist".
            present = "sim.exit" in os.listdir(str(run_dir))
            fields = exit_file.read_text().split() if present else []
            if len(fields) >= 3:
                code = int(fields[0])
                job.elapsed = float(fields[2]) - float(fields[1])
                text = (run_dir / "sim.log").read_text(errors="replace")
                if not has_sim_output(text):
                    job.notes.append("{}: LSF batch returned no simulator output; rerun alone"
                                     .format(job.label))
                    code, text = run_single(job, run_dir, simv_dir)
            elif final:
                job.notes.append("{}: LSF batch {:02d} ended before running it; rerun alone"
                                 .format(job.label, index))
                code, text = run_single(job, run_dir, simv_dir)
            else:
                continue
            pending.remove(job)
            report(finish_job(job, run_dir, code, text, status, keep_traces))

    while proc.poll() is None:
        time.sleep(5)
        collect(False)
    log.close()
    # Results written on the LSF host can take a while to appear over NFS.
    for _ in range(12):
        collect(False)
        if not pending:
            break
        time.sleep(5)
    collect(True)


def parse_args():
    parser = argparse.ArgumentParser(
        description="Full no-coverage regression (mini + riscv-tests + KUDU bug "
                    "reproducers), packed into --lsf_jobs balanced LSF batches.")
    parser.add_argument("--suite", nargs="+", choices=["all", "mini", "riscv", "bug"],
                        default=["all"], help="suites to run (default: all)")
    parser.add_argument("--build", choices=["all", "cheriot", "rv32"], default="all",
                        help="hardware builds to exercise (default: all)")
    parser.add_argument("--only", help="run only jobs whose label matches this regex")
    parser.add_argument("--skip", default="",
                        help="skip jobs whose label matches this regex (default: none)")
    parser.add_argument("--list", action="store_true",
                        help="list the selected jobs and exit")
    parser.add_argument("--lsf_jobs", "--jobs", dest="lsf_jobs", type=cov_regr.positive_int,
                        default=10,
                        help="number of LSF jobs; the simulations are packed into this "
                             "many batches of similar estimated run time, all submitted "
                             "at once (default: 10)")
    parser.add_argument("--times_from",
                        help="earlier work directory whose runs/*/sim.log CPU times "
                             "replace the built-in run-time estimates")
    parser.add_argument("--conf", choices=["0", "1", "2", "3"],
                        help="pipeline configuration passed to ./vcscomp as -conf<N>")
    parser.add_argument("--simv_dir",
                        help="reuse an existing build directory holding simv and simv32 "
                             "instead of compiling")
    parser.add_argument("--work_dir",
                        help="new output directory (default: "
                             "temp_full_regression/run_<timestamp> under sim/run)")
    parser.add_argument("--riscv_timeout", type=cov_regr.positive_int, default=10000,
                        help="+TIMEOUT for riscv-tests (default: 10000)")
    parser.add_argument("--keep_traces", action="store_true",
                        help="keep trace/RVFI logs of passing tests")
    return parser.parse_args()


def main():
    args = parse_args()
    jobs = build_jobs(args)
    if not jobs:
        print("ERROR: no test matches the selection", file=sys.stderr)
        return 1
    if args.list:
        for job in jobs:
            print("{:<6} {:<7} {}".format(job.suite, job.simv, job.label))
        print("{} job(s)".format(len(jobs)))
        return 0

    work = Path(args.work_dir) if args.work_dir else (
        RUN_DIR / "temp_full_regression" / time.strftime("run_%Y%m%d_%H%M%S"))
    if not work.is_absolute():
        work = RUN_DIR / work
    work = work.resolve()
    try:
        work.mkdir(parents=True)
    except FileExistsError:
        print("ERROR: {} already exists; choose a new --work_dir".format(work), file=sys.stderr)
        return 1
    env = dict(os.environ, TMPDIR=str(work / "tmp"))
    (work / "tmp").mkdir()
    print("Work directory: {}".format(work), flush=True)

    status = read_bug_status()
    programs = sorted({job.bindir for job in jobs if job.bindir})
    prog_bins = {}
    simv_dir = Path(args.simv_dir).resolve() if args.simv_dir else work / "build"

    with ThreadPoolExecutor(max_workers=8) as pool:
        compile_future = None
        if not args.simv_dir:
            print("Compiling (vcscomp -nowave) into {} ...".format(simv_dir), flush=True)
            compile_future = pool.submit(compile_simv, args, simv_dir)
        futures = {pool.submit(build_program, name, flavour, work / "programs", env):
                   (name, flavour) for name, flavour in programs}
        errors = []
        for future in as_completed(futures):
            try:
                prog_bins[futures[future]] = future.result()
            except RuntimeError as error:
                errors.append(str(error))
        if programs:
            print("Built {} of {} test program(s)".format(len(prog_bins), len(programs)),
                  flush=True)
        if compile_future:
            try:
                compile_future.result()
            except RuntimeError as error:
                print("ERROR: {}".format(error), file=sys.stderr)
                return 1
    for name in ("simv", "simv32"):
        if any(job.simv == name for job in jobs) and not (simv_dir / name).is_file():
            print("ERROR: {} not found".format(simv_dir / name), file=sys.stderr)
            return 1

    results = []
    for error in errors:
        print("ERROR: {}".format(error), file=sys.stderr)
    runnable = []
    for job in jobs:
        if job.bindir and job.bindir not in prog_bins:
            job.verdict, job.detail = "FAIL", "test program build failed"
            results.append(job)
        else:
            runnable.append(job)

    measured = {}
    if args.times_from:
        for log in Path(args.times_from).glob("runs/*/sim.log"):
            match = CPU_TIME.search(log.read_text(errors="replace"))
            if match:
                measured[log.parent.name] = float(match[1])
    for job in runnable:
        setup_run(job, work, prog_bins)
    (work / "batches").mkdir()
    batches, loads = pack_batches(runnable, args.lsf_jobs, measured)

    print("Running {} simulation(s) in {} LSF job(s), estimated {:.0f}-{:.0f}s of "
          "simulation each".format(len(runnable), len(batches), min(loads or [0]),
                                   max(loads or [0])), flush=True)
    lock = threading.Lock()
    total = len(jobs)

    def report(job):
        with lock:
            results.append(job)
            print("[{:>3}/{}] {:<5} {:<46} {:>6.0f}s {}".format(
                len(results), total, job.verdict, job.label, job.elapsed, job.detail),
                flush=True)

    with ThreadPoolExecutor(max_workers=max(1, len(batches))) as pool:
        futures = [pool.submit(run_batch, i, batch, work, simv_dir, status,
                               args.keep_traces, report)
                   for i, batch in enumerate(batches)]
        for future in as_completed(futures):
            try:
                future.result()
            except Exception as error:  # keep the remaining batches running
                print("ERROR: batch crashed: {}".format(error), file=sys.stderr)

    order = {job.label: i for i, job in enumerate(jobs)}
    results.sort(key=lambda job: order[job.label])
    counts = {v: sum(job.verdict == v for job in results) for v in VERDICTS}
    lines = ["{:<5} {:<6} {:<46} {}".format(job.verdict, job.suite, job.label, job.detail)
             for job in results]
    notes = sorted({note for job in results for note in job.notes})
    for bug in BUG_TESTS:
        runs = [job for job in results if job.checker is bug]
        # Only judge a bug when every run of its test produced a verdict.
        if not runs or any(job.failed_bugs is None for job in runs):
            continue
        failed = set().union(*(job.failed_bugs for job in runs))
        for kid in sorted({kid for _, kid in bug.checks}):
            if kid not in failed and status.get(kid) in ("Open", "Deferred"):
                notes.append("{}: its checks in {} all pass, but the bug log lists it as {}"
                             .format(kid, bug.name, status[kid]))
    summary = ["", "Summary: {} job(s): {} PASS, {} XFAIL (open bugs), {} DEFER "
               "(deferred/waived bugs), {} FAIL".format(
                   len(jobs), counts["PASS"], counts["XFAIL"], counts["DEFER"], counts["FAIL"])]
    summary += ["  FAIL  {:<46} {}".format(job.label, job.detail)
                for job in results if job.verdict == "FAIL"]
    summary += ["  XFAIL {:<46} {}".format(job.label, job.detail)
                for job in results if job.verdict == "XFAIL"]
    summary += ["  DEFER {:<46} {}".format(job.label, job.detail)
                for job in results if job.verdict == "DEFER"]
    summary += ["  NOTE  " + note for note in notes]
    summary.append("Results: {}".format(work / "results.txt"))
    (work / "results.txt").write_text("\n".join(lines + summary) + "\n")
    print("\n".join(summary), flush=True)
    return 1 if counts["FAIL"] or len(results) != len(jobs) else 0


if __name__ == "__main__":
    raise SystemExit(main())
