"""Exercise both coverage runners without invoking licensed tools.

Run: PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover \
         -s scripts -p test_coverage_builds.py -v
"""

import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

from coverage_builds import BUILDS, build_cov_dir


SIM = Path(__file__).resolve().parent.parent


def load_runner(name, relative_path):
    spec = importlib.util.spec_from_file_location(name, SIM / relative_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


DII = load_runner("dii_coverage_runner", "run_dii/run_dii_rvfi.py")
REGRESSION = load_runner("regression_coverage_runner", "run/run_cov_regression.py")


class CoverageBuildTests(unittest.TestCase):
    def setUp(self):
        (SIM / "temp").mkdir(exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="coverage_builds_", dir=SIM / "temp")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.commands = []
        self.command_cwds = []
        self.fail_tests = set()
        self.fail_merge_builds = set()
        self.no_data_builds = set()
        self.fail_compile = False
        self.missing_compiled_builds = set()
        self.missing_design_builds = set()
        self.command_observer = None
        self.output = io.StringIO()
        self.run_dir = self.root / "run"
        self.run_dir.mkdir()
        self.work_dir = self.run_dir / "temp_cov_regression"
        for build, spec in BUILDS.items():
            (self.run_dir / spec["simv"]).touch()
            design = self.run_dir / spec["vdb"]
            design.mkdir()
            (design / "design.txt").write_text(build)
        (self.run_dir / "bin").mkdir()
        with tarfile.open(self.run_dir / "bin.tar.gz", "w:gz") as archive:
            for name, data in (
                    ("bin/a.elf", b"ELF"),
                    ("bin/b.elf", b"ELF"),
                    ("bin/elfs_no_conflict.list", b"a.elf\nb.elf\n")):
                info = tarfile.TarInfo(name)
                info.size = len(data)
                archive.addfile(info, io.BytesIO(data))

    def records(self, path):
        record_file = Path(path) / "records.json"
        return json.loads(record_file.read_text()) if record_file.exists() else []

    def save_records(self, path, records):
        path = Path(path)
        path.mkdir(parents=True, exist_ok=True)
        (path / "snps/coverage/db/testdata").mkdir(parents=True, exist_ok=True)
        (path / "records.json").write_text(json.dumps(records))

    def fake_run(self, command, cwd, **kwargs):
        command = [str(arg) for arg in command]
        self.commands.append(command)
        if self.command_observer is not None:
            self.command_observer(command)
        cwd = Path(cwd)
        self.command_cwds.append(cwd)
        status = 0
        if Path(command[0]).name in ("simv", "simv32"):
            build = "rv32" if Path(command[0]).name == "simv32" else "cheriot"
            modes = [arg for arg in command if arg.startswith("+PMODE=")]
            self.assertEqual(len(modes), 1)
            pmode = int(modes[0].split("=")[1])
            if build == "rv32":
                self.assertEqual(pmode, 0)
            name = next(arg.split("=", 1)[1] for arg in command if arg.startswith("+TEST="))
            if "-cm_dir" in command and build not in self.no_data_builds:
                raw = Path(command[command.index("-cm_dir") + 1])
                self.assertTrue(raw.name.endswith("_{}.vdb".format(build)))
                self.assertNotIn("_pmode", raw.name)
                tag = command[command.index("-cm_name") + 1]
                self.assertIn("__pmode{}__".format(pmode), tag)
                self.assertIn("__{}__".format(build), tag)
                self.save_records(raw, self.records(raw) +
                                  [{"build": build, "pmode": pmode, "test": name}])
            if kwargs.get("stdout") is not None:
                kwargs["stdout"].write("RISCV Test passed :)\n")
            else:
                for log in (DII.RVFI_LOG, DII.TRACE_LOG):
                    (cwd / log).write_text("test {}\n".format(name))
            status = 1 if name in self.fail_tests else 0
        elif command[0] == "urg":
            inputs = [Path(command[i + 1]) for i, arg in enumerate(command) if arg == "-dir"]
            records = [record for path in inputs for record in self.records(path)]
            builds = {record["build"] for record in records}
            self.assertLessEqual(len(builds), 1)
            for path in inputs:
                if (path / "design.txt").exists() and records:
                    self.assertEqual(builds, {(path / "design.txt").read_text()})
            if "-dbname" in command:
                target = Path(command[command.index("-dbname") + 1])
                if any("_{}".format(build) in target.name for build in self.fail_merge_builds):
                    status = 1
                else:
                    self.save_records(target, records)
            else:
                report = Path(command[command.index("-report") + 1])
                self.save_records(report, records)
        elif command[0] == "./vcscomp":
            status = 1 if self.fail_compile else 0
            output = next((arg.split("=", 1)[1] for arg in command
                           if arg.startswith("-outdir=")), None)
            if output and not status:
                output = Path(output)
                self.assertEqual(cwd, self.run_dir)
                self.assertEqual(list(output.iterdir()), [])
                for build, spec in BUILDS.items():
                    if build in self.missing_compiled_builds:
                        continue
                    (output / spec["simv"]).touch()
                    if build in self.missing_design_builds:
                        continue
                    (output / spec["vdb"]).mkdir()
                    (output / spec["vdb"] / "design.txt").write_text(build)
        else:
            self.fail("Unexpected external command: {}".format(command))
        if status and kwargs.get("check"):
            raise subprocess.CalledProcessError(status, command)
        return subprocess.CompletedProcess(command, status)

    def invoke(self, runner, *args):
        defaults = (["--rvfi_max", "5"] if runner is DII else
                    ["--only", r"^(coremark\.rv32o3|isa_test1)$"])
        with patch.object(runner, "__file__", str(self.run_dir / "runner.py")), \
                patch.object(REGRESSION, "SIM_ROOT", self.root), \
                patch.object(sys, "argv", ["runner.py", *defaults, *args]), \
                patch.object(runner.subprocess, "run", side_effect=self.fake_run), \
                contextlib.redirect_stdout(self.output), \
                contextlib.redirect_stderr(self.output):
            return runner.main()

    def assert_build_records(self, path, build, modes, count):
        records = self.records(path)
        self.assertEqual(len(records), count, path)
        self.assertEqual({record["build"] for record in records}, {build})
        self.assertEqual({record["pmode"] for record in records}, set(modes))

    def test_basename_rules(self):
        for base in ("campaign", "campaign.vdb", "nested/campaign.vdb",
                     str(self.root / "campaign.vdb")):
            for build in BUILDS:
                expected = Path(base).with_name("campaign_{}.vdb".format(build))
                self.assertEqual(build_cov_dir(base, build), expected)
        with self.assertRaises(ValueError):
            build_cov_dir("campaign.vdb", "pmode0")

    def test_all_regression_tests_have_explicit_valid_modes(self):
        tests = REGRESSION.build_test_list(["mini", "riscv"], 10000)
        self.assertTrue(tests)
        for test in tests:
            expected = 0 if test.suite == "riscv" or test.name in REGRESSION.MINI_RV32_TESTS else 1
            self.assertEqual(test.pmode, expected, test.label)
            if test.build == "rv32":
                self.assertEqual(test.pmode, 0)
        self.assertEqual(len({test.run_label for test in tests}), len(tests))
        cheri_tests = REGRESSION.build_test_list(["mini", "riscv"], 10000, "cheriot")
        rv32_tests = REGRESSION.build_test_list(["mini", "riscv"], 10000, "rv32")
        self.assertEqual(len(tests), len(cheri_tests) + len(rv32_tests))
        self.assertEqual({test.pmode for test in cheri_tests}, {0, 1})
        self.assertEqual({test.pmode for test in rv32_tests}, {0})
        for args in ([], ["+PMODE=2"], ["+PMODE=0", "+PMODE=1"]):
            test = REGRESSION.Test("mini", "cheriot", "bad", "default", args)
            with self.assertRaises(ValueError):
                _ = test.pmode

    def test_regression_build_separation_runtime_union_and_reports(self):
        legacy = [self.run_dir / name for name in (
            "cov_kudu_regr.vdb", "cov_kudu_regr_pmode0.vdb", "cov_kudu_regr_pmode1.vdb")]
        for path in legacy:
            self.save_records(path, [{"build": "legacy"}])
        self.assertEqual(self.invoke(REGRESSION, "--cov_tag", "first", "--cov_report"), 0)
        for build, modes, count in (("cheriot", (0, 1), 4), ("rv32", (0,), 2)):
            self.assert_build_records(self.work_dir / "cov_kudu_regr_{}.vdb".format(build),
                                      build, modes, count)
            self.assert_build_records(self.work_dir / "urgReport_{}".format(build),
                                      build, modes, count)
        for path in legacy:
            self.assertEqual(self.records(path), [{"build": "legacy"}])
        self.assertEqual(len(list((self.run_dir / "temp_cov_regression").glob("sim.*.log"))), 6)
        self.assertFalse(list((self.work_dir / "cov_temp").glob("cov_run_*.vdb")))

    def test_regression_resets_each_build_before_first_simulation(self):
        outputs = [self.work_dir / "cov_kudu_regr_{}.vdb".format(build) for build in BUILDS]
        preserved = [
            self.work_dir / "cov_temp/cov_run_old_cheriot.vdb",
            self.work_dir / "build_old/simv.vdb",
            self.run_dir / "cov_kudu_cheriot.vdb",
            self.root / "run_dii/cov_kudu.vdb",
        ]
        for path in preserved:
            self.save_records(path, [{"test": "preserved"}])
        for tag in ("first", "second"):
            self.assertEqual(self.invoke(REGRESSION, "--cov_tag", tag,
                                         "--keep_run_cov"), 0)
        self.assert_build_records(outputs[0], "cheriot", (0, 1), 4)
        self.assert_build_records(outputs[1], "rv32", (0,), 2)
        observations = []

        def observe(command):
            if command[0] == "./vcscomp":
                self.assertTrue(all(path.is_dir() for path in outputs))
                observations.append("compile")
            elif Path(command[0]).name in ("simv", "simv32"):
                self.assertFalse(outputs[0].exists())
                self.assertTrue(outputs[1].is_dir())
                observations.append("simulate")

        self.command_observer = observe
        self.assertEqual(self.invoke(REGRESSION, "--cov_tag", "third",
                                     "--only", "^isa_test1$"), 0)
        self.assertEqual(observations[0], "compile")
        self.assertIn("simulate", observations)
        self.assert_build_records(outputs[0], "cheriot", (1,), 2)
        # No RV32 tests selected: its previous output and all old raw/build data survive.
        self.assert_build_records(outputs[1], "rv32", (0,), 2)
        for path in preserved:
            self.assertEqual(self.records(path), [{"test": "preserved"}])
        for build in BUILDS:
            self.assertTrue((self.work_dir / "cov_temp" /
                             "cov_run_first_{}.vdb".format(build)).is_dir())
        merges = [cmd for cmd in self.commands if cmd[0] == "urg" and "-dbname" in cmd]
        for cmd in merges:
            inputs = [Path(cmd[i + 1]) for i, arg in enumerate(cmd) if arg == "-dir"]
            self.assertEqual(len(inputs), 2)
            self.assertTrue(inputs[0].parent.name.startswith("build_"))
            self.assertNotIn(inputs[0], outputs)

    def test_regression_subset_only_updates_selected_build(self):
        other = self.work_dir / "cov_kudu_regr_cheriot.vdb"
        previous = [{"build": "cheriot", "pmode": 1, "test": "previous"}]
        self.save_records(other, previous)
        self.assertEqual(self.invoke(REGRESSION, "--suite", "riscv",
                                     "--build", "rv32", "--only", "^rv32ui-p-add$",
                                     "--cov_report"), 0)
        self.assert_build_records(self.work_dir / "cov_kudu_regr_rv32.vdb", "rv32", (0,), 1)
        self.assertEqual(self.records(other), previous)
        self.assertFalse((self.work_dir / "urgReport_cheriot").exists())

    def test_regression_resets_all_selected_outputs_after_compile(self):
        outputs = [self.work_dir / "cov_kudu_regr_{}.vdb".format(build) for build in BUILDS]
        for path in outputs:
            self.save_records(path, [{"test": "previous"}])

        def observe(command):
            if command[0] == "./vcscomp":
                self.assertTrue(all(path.is_dir() for path in outputs))
            elif Path(command[0]).name in ("simv", "simv32"):
                self.assertFalse(any(path.exists() for path in outputs))

        self.command_observer = observe
        self.assertEqual(self.invoke(REGRESSION), 0)
        self.assertEqual(self.commands[0][0], "./vcscomp")
        for path in outputs:
            self.assertTrue(path.is_dir())

    def test_regression_does_not_replace_output_recreated_during_simulation(self):
        target = self.work_dir / "cov_kudu_regr_cheriot.vdb"

        def observe(command):
            if Path(command[0]).name == "simv":
                self.save_records(target, [{"test": "another invocation"}])

        self.command_observer = observe
        self.assertEqual(self.invoke(REGRESSION, "--cov_tag", "reappeared"), 1)
        self.assertEqual(self.records(target), [{"test": "another invocation"}])
        self.assertIn("reappeared after reset", self.output.getvalue())
        self.assert_build_records(self.work_dir / "cov_temp/cov_run_reappeared_cheriot.vdb",
                                  "cheriot", (0, 1), 4)
        self.assert_build_records(self.work_dir / "cov_kudu_regr_rv32.vdb",
                                  "rv32", (0,), 2)

    def test_regression_simulation_failure_still_merges_both_builds(self):
        for build in BUILDS:
            self.save_records(self.work_dir / "cov_kudu_regr_{}.vdb".format(build),
                              [{"test": "previous"}])
        self.fail_tests.add("coremark.rv32o3")
        self.assertEqual(self.invoke(REGRESSION, "--cov_tag", "failed"), 1)
        self.assert_build_records(self.work_dir / "cov_kudu_regr_cheriot.vdb", "cheriot", (0, 1), 4)
        self.assert_build_records(self.work_dir / "cov_kudu_regr_rv32.vdb", "rv32", (0,), 2)

    def test_regression_merge_failure_preserves_raw_and_merges_other_build(self):
        self.fail_merge_builds.add("cheriot")
        previous = self.work_dir / "cov_kudu_regr_cheriot.vdb"
        records = [{"build": "cheriot", "pmode": 0, "test": "previous"}]
        self.save_records(previous, records)
        self.assertEqual(self.invoke(REGRESSION, "--cov_tag", "failed"), 1)
        self.assertFalse(previous.exists())
        self.assert_build_records(self.work_dir / "cov_temp/cov_run_failed_cheriot.vdb",
                                  "cheriot", (0, 1), 4)
        self.assert_build_records(self.work_dir / "cov_kudu_regr_rv32.vdb", "rv32", (0,), 2)
        self.assertFalse((self.work_dir / "cov_temp/cov_run_failed_rv32.vdb").exists())

    def test_missing_build_data_does_not_block_other_merge(self):
        self.no_data_builds.add("cheriot")
        self.assertEqual(self.invoke(REGRESSION, "--cov_tag", "missing"), 1)
        self.assert_build_records(self.work_dir / "cov_kudu_regr_rv32.vdb", "rv32", (0,), 2)

    def test_dii_runtime_modes_accumulate_together_hardware_builds_separately(self):
        legacy = [self.run_dir / name for name in
                  ("cov_kudu.vdb", "cov_kudu_pmode0.vdb", "cov_kudu_pmode1.vdb")]
        for path in legacy:
            self.save_records(path, [{"build": "legacy"}])
        for tag, options in (("first", []), ("second", ["--rv32"]),
                             ("third", ["--build", "rv32"])):
            self.assertEqual(self.invoke(DII, "--cov_tag", tag, "--cov_report", *options), 0)
        for build, modes, count in (("cheriot", (0, 1), 4), ("rv32", (0,), 2)):
            self.assert_build_records(self.run_dir / "cov_kudu_{}.vdb".format(build),
                                      build, modes, count)
            self.assert_build_records(self.run_dir / "urgReport_{}".format(build),
                                      build, modes, count)
        for path in legacy:
            self.assertEqual(self.records(path), [{"build": "legacy"}])
        with tarfile.open(self.run_dir / "results.tar.gz") as archive:
            self.assertEqual(len([name for name in archive.getnames()
                                  if name.endswith((".trace", ".rvfi"))]), 4)

    def test_dii_failed_simulation_still_archives_and_merges(self):
        self.fail_tests.add("a")
        self.assertEqual(self.invoke(DII, "--rv32"), 1)
        self.assert_build_records(self.run_dir / "cov_kudu_cheriot.vdb", "cheriot", (0,), 2)
        self.assertTrue((self.run_dir / "results.tar.gz").is_file())

    def test_dii_merge_failure_keeps_raw(self):
        self.fail_merge_builds.add("cheriot")
        self.assertEqual(self.invoke(DII, "--cov_tag", "failed"), 1)
        self.assert_build_records(self.run_dir / "cov_temp/cov_run_failed_cheriot.vdb",
                                  "cheriot", (1,), 2)

    def test_custom_basenames_and_keep_raw(self):
        for runner in (DII, REGRESSION):
            for absolute in (False, True):
                with self.subTest(runner=runner.__name__, absolute=absolute):
                    name = "{}_{}".format(runner.__name__, absolute)
                    base = self.run_dir / "custom" / name if absolute else Path("custom") / name
                    self.assertEqual(self.invoke(runner, "--cov_dir", str(base),
                                                 "--cov_tag", name, "--keep_run_cov"), 0)
                    self.assert_build_records(self.run_dir / "custom" / (name + "_cheriot.vdb"),
                                              "cheriot", (1,) if runner is DII else (0, 1),
                                              2 if runner is DII else 4)
                    raw_base = self.run_dir if runner is DII else self.work_dir
                    self.assertTrue(list((raw_base / "cov_temp").glob(
                        "cov_run_{}*.vdb".format(name))))

    def test_no_coverage_still_passes_pmode_without_calling_urg(self):
        for runner in (DII, REGRESSION):
            with self.subTest(runner=runner.__name__):
                self.commands.clear()
                self.assertEqual(self.invoke(runner, "--no_cov", "--cov_report"), 0)
                self.assertTrue(self.commands)
                self.assertTrue(all(command[0] != "urg" and "-cm_dir" not in command
                                    for command in self.commands))
                if runner is REGRESSION:
                    self.assertEqual(self.commands[0][0:3], ["./vcscomp", "-cov", "-nowave"])
                    self.assertFalse(list(self.work_dir.glob("cov_kudu_regr_*.vdb")))

    def test_raw_name_collision_is_preserved(self):
        for runner, raw_name in (
                (REGRESSION, "cov_run_same_cheriot.vdb"),
                (DII, "cov_run_same_cheriot.vdb")):
            with self.subTest(runner=runner.__name__):
                raw_base = self.run_dir if runner is DII else self.work_dir
                raw = raw_base / "cov_temp" / raw_name
                self.save_records(raw, [{"pmode": "preserve"}])
                self.commands.clear()
                if runner is DII:
                    with self.assertRaisesRegex(RuntimeError, "already exists"):
                        self.invoke(runner, "--cov_tag", "same")
                else:
                    self.assertEqual(self.invoke(runner, "--cov_tag", "same"), 1)
                self.assertEqual(self.records(raw), [{"pmode": "preserve"}])
                self.assertEqual(self.commands, [])

    def test_compile_runs_once_for_both_regression_builds(self):
        for flags in ([], ["--compile"]):
            self.commands.clear()
            self.assertEqual(self.invoke(REGRESSION, *flags, "--conf", "2"), 0)
            commands = [cmd for cmd in self.commands if cmd[0] == "./vcscomp"]
            self.assertEqual(len(commands), 1)
            self.assertEqual(commands[0][:-1], ["./vcscomp", "-cov", "-nowave", "-conf2"])
            output = Path(commands[0][-1].split("=", 1)[1])
            self.assertEqual(output.parent, self.work_dir)
            simulations = [cmd for cmd in self.commands
                           if Path(cmd[0]).name in ("simv", "simv32")]
            self.assertEqual({Path(cmd[0]).parent for cmd in simulations}, {output})
        self.assertEqual(len(list(self.work_dir.glob("build_*"))), 2)

    def test_compile_failure_stops_before_simulation(self):
        previous = self.work_dir / "cov_kudu_regr_cheriot.vdb"
        self.save_records(previous, [{"test": "previous"}])
        self.fail_compile = True
        self.assertEqual(self.invoke(REGRESSION), 1)
        self.assertEqual(len(self.commands), 1)
        self.assertEqual(self.records(previous), [{"test": "previous"}])

    def test_regression_preflight_failure_preserves_all_previous_results(self):
        previous = self.work_dir / "cov_kudu_regr_cheriot.vdb"
        self.save_records(previous, [{"test": "previous"}])
        for failure in ("missing_design", "missing_simulator", "bad_bin", "bad_output"):
            with self.subTest(failure=failure):
                self.commands.clear()
                self.missing_design_builds = {"rv32"} if failure == "missing_design" else set()
                self.missing_compiled_builds = {"rv32"} if failure == "missing_simulator" else set()
                if failure == "bad_bin":
                    link = self.work_dir / "bin"
                    if link.is_symlink():
                        link.unlink()
                    link.mkdir()
                if failure == "bad_output":
                    (self.work_dir / "cov_kudu_regr_rv32.vdb").mkdir()
                self.assertEqual(self.invoke(REGRESSION), 1)
                self.assertEqual(len(self.commands), 1)
                self.assertEqual(self.records(previous), [{"test": "previous"}])
                if failure == "bad_bin":
                    (self.work_dir / "bin").rmdir()

    def test_regression_list_and_no_cov_preserve_existing_results(self):
        previous = self.work_dir / "cov_kudu_regr_cheriot.vdb"
        self.save_records(previous, [{"test": "previous"}])
        before = sorted(self.run_dir.rglob("*"))
        self.assertEqual(self.invoke(REGRESSION, "--list", "--compile"), 0)
        self.assertEqual(sorted(self.run_dir.rglob("*")), before)
        self.assertEqual(self.invoke(REGRESSION, "--no_cov"), 0)
        self.assertEqual(self.records(previous), [{"test": "previous"}])

    def test_regression_custom_outputs_are_reset_only_for_selected_build(self):
        for absolute in (False, True):
            with self.subTest(absolute=absolute):
                base = self.run_dir / "custom/campaign.vdb"
                selected = build_cov_dir(base, "rv32")
                other = build_cov_dir(base, "cheriot")
                for path in (base, selected, other):
                    self.save_records(path, [{"test": "previous"}])
                option = str(base if absolute else base.relative_to(self.run_dir))
                self.assertEqual(self.invoke(REGRESSION, "--build", "rv32",
                                             "--cov_dir", option), 0)
                self.assert_build_records(selected, "rv32", (0,), 2)
                for path in (base, other):
                    self.assertEqual(self.records(path), [{"test": "previous"}])

    def test_regression_rejects_unsafe_reset_targets(self):
        previous = self.work_dir / "cov_kudu_regr_cheriot.vdb"
        self.save_records(previous, [{"test": "previous"}])
        design = self.run_dir / "design_cheriot.vdb"
        self.save_records(design, [{"test": "design"}])
        link = self.run_dir / "link_cheriot.vdb"
        link.symlink_to(design)
        broken = self.run_dir / "broken_cheriot.vdb"
        broken.symlink_to(self.root / "missing")
        linked_parent = self.run_dir / "linked"
        linked_parent.symlink_to(self.work_dir, target_is_directory=True)
        source = self.run_dir / "source_cheriot.vdb"
        source.mkdir()
        (source / "source.sv").write_text("preserve source")
        file_target = self.run_dir / "file_cheriot.vdb"
        file_target.write_text("preserve file")
        design_only = self.run_dir / "design_only_cheriot.vdb"
        (design_only / "snps/coverage/db/design").mkdir(parents=True)
        linked_contents = self.run_dir / "linked_contents_cheriot.vdb"
        self.save_records(linked_contents, [{"test": "previous"}])
        (linked_contents / "input").symlink_to(design)
        cases = [
            (["--cov_dir", "link"], "symlinks"),
            (["--cov_dir", "broken"], "symlinks"),
            (["--cov_dir", "linked/cov_kudu_regr"], "symlinks"),
            (["--cov_dir", "source"], "non-VCS"),
            (["--cov_dir", "file"], "non-VCS"),
            (["--cov_dir", "design_only"], "design-only"),
            (["--cov_dir", "linked_contents"], "symlinks"),
            (["--cov_dir", "design", "--design_vdb", str(design)], "design"),
            (["--cov_dir", str(self.root / "run_dii/campaign")], "DII"),
            (["--cov_dir", "cov_kudu"], "DII"),
            (["--cov_dir", str(design / "nested")], "source database"),
            (["--cov_dir", str(self.root.parent / "outside_sim")], "inside sim/"),
            (["--cov_dir", "broad",
              "--work_dir", str(self.run_dir / "broad_cheriot.vdb")], "working input"),
        ]
        for options, message in cases:
            with self.subTest(options=options):
                self.commands.clear()
                self.output.truncate(0)
                self.output.seek(0)
                self.assertEqual(self.invoke(REGRESSION, "--build", "cheriot", *options), 1)
                self.assertNotIn("urg", [cmd[0] for cmd in self.commands])
                self.assertFalse(any(Path(cmd[0]).name in ("simv", "simv32")
                                     for cmd in self.commands))
                self.assertIn(message, self.output.getvalue())
                self.assertEqual(self.records(previous), [{"test": "previous"}])
                self.assertEqual(self.records(design), [{"test": "design"}])
        self.assertTrue(link.is_symlink())
        self.assertTrue(broken.is_symlink())
        self.assertEqual((source / "source.sv").read_text(), "preserve source")
        self.assertEqual(file_target.read_text(), "preserve file")
        self.assertTrue((design_only / "snps/coverage/db/design").is_dir())
        self.assertTrue((linked_contents / "input").is_symlink())

    def test_regression_reset_failure_is_explicit_and_stops_simulation(self):
        previous = self.work_dir / "cov_kudu_regr_cheriot.vdb"
        self.save_records(previous, [{"test": "previous"}])
        with patch.object(REGRESSION.shutil, "rmtree", side_effect=PermissionError("denied")):
            self.assertEqual(self.invoke(REGRESSION), 1)
        self.assertEqual(len(self.commands), 1)
        self.assertIn("reset failed: denied", self.output.getvalue())
        self.assertEqual(self.records(previous), [{"test": "previous"}])

    def test_design_override_requires_single_build(self):
        self.assertEqual(self.invoke(REGRESSION, "--design_vdb", "custom.vdb"), 1)
        self.assertEqual(self.commands, [])
        custom = self.run_dir / "custom.vdb"
        custom.mkdir()
        (custom / "design.txt").write_text("rv32")
        self.assertEqual(self.invoke(REGRESSION, "--build", "rv32",
                                     "--design_vdb", str(custom)), 0)
        merges = [cmd for cmd in self.commands if cmd[0] == "urg" and "-dbname" in cmd]
        self.assertEqual(merges[0][merges[0].index("-dir") + 1], str(custom))

    def test_missing_rv32_simulator_is_not_replaced_by_cheriot(self):
        (self.run_dir / "simv32").unlink()
        self.missing_compiled_builds.add("rv32")
        self.assertEqual(self.invoke(REGRESSION, "--build", "rv32"), 1)
        self.assertEqual(len(self.commands), 1)
        self.commands.clear()
        self.assertEqual(self.invoke(DII, "--build", "rv32"), 1)
        self.assertEqual(self.commands, [])

    def test_list_is_read_only_even_with_compile_flag(self):
        before = sorted(self.run_dir.rglob("*"))
        self.assertEqual(self.invoke(REGRESSION, "--list", "--compile"), 0)
        self.assertEqual(self.commands, [])
        self.assertEqual(sorted(self.run_dir.rglob("*")), before)
        self.assertFalse(self.work_dir.exists())

    def test_listing_custom_paths_does_not_create_them(self):
        self.assertEqual(self.invoke(REGRESSION, "--list", "--work_dir", "not_created",
                                     "--cov_dir", "also_not_created/campaign",
                                     "--cov_report"), 0)
        self.assertFalse((self.run_dir / "not_created").exists())
        self.assertFalse((self.run_dir / "also_not_created").exists())
        self.assertEqual(self.commands, [])

    def test_fresh_design_and_output_routing_leave_old_artifacts_untouched(self):
        for build, spec in BUILDS.items():
            self.save_records(self.run_dir / spec["vdb"], [{"build": "stale"}])
            self.save_records(self.run_dir / "cov_kudu_regr_{}.vdb".format(build),
                              [{"build": "old campaign"}])
        old_build = self.work_dir / "build_previous"
        self.save_records(old_build / "simv.vdb", [{"build": "stale"}])
        before = {p: p.read_bytes() for p in self.run_dir.rglob("*") if p.is_file()}
        self.assertEqual(self.invoke(REGRESSION, "--cov_report"), 0)
        for p, content in before.items():
            self.assertEqual(p.read_bytes(), content, p)
        merges = [cmd for cmd in self.commands if cmd[0] == "urg" and "-dbname" in cmd]
        for cmd in merges:
            design = Path(cmd[cmd.index("-dir") + 1])
            self.assertEqual(design.parent.parent, self.work_dir)
            self.assertNotEqual(design.parent, old_build)
        for cmd, cwd in zip(self.commands, self.command_cwds):
            self.assertEqual(cwd, self.run_dir if cmd[0] == "./vcscomp" else self.work_dir)
        self.assertFalse((self.run_dir / "cov_temp").exists())
        self.assertFalse((self.run_dir / "urgReport_cheriot").exists())

    def test_work_dir_routes_all_default_outputs(self):
        for absolute in (False, True):
            with self.subTest(absolute=absolute):
                work = self.root / "absolute" if absolute else Path("relative")
                expected = work if absolute else self.run_dir / work
                self.commands.clear()
                self.command_cwds.clear()
                self.assertEqual(self.invoke(REGRESSION, "--work_dir", str(work),
                                             "--keep_run_cov", "--cov_report"), 0)
                self.assert_build_records(expected / "cov_kudu_regr_cheriot.vdb",
                                          "cheriot", (0, 1), 4)
                self.assertEqual(len(list(expected.glob("build_*/simv*.vdb"))), 2)
                self.assertEqual(len(list((expected / "cov_temp").glob("cov_run_*.vdb"))), 2)
                self.assertTrue((expected / "urgReport_cheriot").is_dir())
                self.assertTrue((expected / "bin").is_symlink())
                self.assertEqual((expected / "bin").resolve(), self.run_dir / "bin")
                for cmd, cwd in zip(self.commands, self.command_cwds):
                    self.assertEqual(cwd, self.run_dir if cmd[0] == "./vcscomp" else expected)
                self.assertFalse(self.work_dir.exists())

    def test_vcscomp_routes_both_builds_and_resolves_inputs(self):
        source = self.root / "native" / "sim" / "run"
        source.mkdir(parents=True)
        for name in ("vcscomp", "kudu.vcs.f", "kudu_dw.vcs.f", "cm_hier.cfg"):
            shutil.copy2(SIM / "run" / name, source / name)
        for name in ("fcov", "tb"):
            (source.parent / name).symlink_to(SIM / name, target_is_directory=True)
        (source.parent.parent / "rtl").symlink_to(SIM.parent / "rtl", target_is_directory=True)
        mock_bin = self.root / "mock_bin"
        mock_bin.mkdir()
        vcs = mock_bin / "vcs"
        vcs.write_text("""#!%s
import json
import os
from pathlib import Path
import sys
args = sys.argv[1:]
output = args[args.index("-o") + 1]
for i, arg in enumerate(args):
    if arg == "-f":
        file_list = Path(args[i + 1])
        assert file_list.is_file(), file_list
        for line in file_list.read_text().splitlines():
            if line.startswith("$"):
                path = Path(os.path.expandvars(line))
                assert path.is_file(), path
assert Path(args[args.index("-cm_hier") + 1]).is_file()
with open("invocations.jsonl", "a") as log:
    log.write(json.dumps({"args": args, "cwd": os.getcwd(),
                         "roots": {key: os.environ[key]
                                   for key in ("rtlRoot", "verifRoot", "dwRoot")}}) + "\\n")
if os.environ.get("MOCK_FAIL_RV32") and output == "./simv32":
    sys.exit(17)
Path(output).touch()
Path(output + ".vdb").mkdir()
Path(output + ".daidir").mkdir()
mdir = next((arg.split("=", 1)[1] for arg in args if arg.startswith("-Mdir=")), "csrc")
Path(mdir).mkdir(exist_ok=True)
if "-l" in args:
    Path(args[args.index("-l") + 1]).touch()
""" % sys.executable)
        vcs.chmod(0o755)
        env = dict(os.environ, PATH=str(mock_bin) + os.pathsep + os.environ["PATH"])
        output = self.root / "native output"
        before = {p: p.read_bytes() for p in source.iterdir()}
        command = [shutil.which("bash"), "./vcscomp", "-cov", "-nowave", "-conf3",
                   "-outdir={}".format(output)]
        subprocess.run(command, cwd=source, env=env, check=True, capture_output=True)
        calls = [json.loads(line) for line in (output / "invocations.jsonl").read_text().splitlines()]
        self.assertEqual(len(calls), 2)
        for call, name in zip(calls, ("simv32", "simv")):
            args = call["args"]
            self.assertEqual(Path(call["cwd"]), output)
            self.assertEqual(args[args.index("-o") + 1], "./" + name)
            self.assertIn("+define+KUDU_PPL_CFG=3", args)
            self.assertIn("+define+NO_FSDB", args)
            self.assertEqual("+define+CHERIoT" in args, name == "simv")
            self.assertEqual(args[args.index("-cm") + 1], REGRESSION.COV_METRICS)
            self.assertEqual(Path(call["roots"]["verifRoot"]).resolve(), source.parent)
            self.assertEqual(Path(call["roots"]["rtlRoot"]).resolve(), SIM.parent / "rtl")
            self.assertEqual(Path(call["roots"]["dwRoot"]).resolve(), source.parent.parent / "dw")
            self.assertTrue((output / (name + ".vdb")).is_dir())
            self.assertTrue((output / (name + ".daidir")).is_dir())
        for name in ("csrc", "csrc32", "compile_rv32.log", "compile_cheriot.log"):
            self.assertTrue((output / name).exists())
        self.assertEqual({p: p.read_bytes() for p in source.iterdir()}, before)
        failed = self.root / "failed native output"
        result = subprocess.run(command[:-1] + ["-outdir={}".format(failed)],
                                cwd=source, env=dict(env, MOCK_FAIL_RV32="1"),
                                capture_output=True)
        self.assertEqual(result.returncode, 17)
        self.assertEqual(len((failed / "invocations.jsonl").read_text().splitlines()), 1)
        # Without -outdir, callers such as run_dii keep their historical cwd outputs.
        subprocess.run(command[:-1], cwd=source, env=env, check=True, capture_output=True)
        self.assertTrue((source / "simv").is_file())
        self.assertTrue((source / "simv32").is_file())


if __name__ == "__main__":
    unittest.main()
