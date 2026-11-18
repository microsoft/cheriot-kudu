import contextlib
import io
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

import diff_files


def clc_line(pc="80000618", tag=0, mnemonic="c.CH.clc"):
    return (
        f"{pc} 7004 {mnemonic} c9,32(c8) "
        f"x8:0x80010000+0x17e1a0000 x9=0x80001000+0x{tag}7e380000 "
        "PA:0x80010020 load:0x80001000+0x17e380000"
    )


class IsaTest1ClcTagTests(unittest.TestCase):
    def apply(self, actual, expected):
        return diff_files.apply_isa_test1_clc_tag_rule([actual], [expected])[0]

    def test_three_pcs_and_clc_spellings(self):
        for pc in ("80000618", "80000624", "80000638"):
            for mnemonic in ("clc", "CH.clc", "c.CH.clc"):
                with self.subTest(pc=pc, mnemonic=mnemonic):
                    actual = clc_line(pc, 0, mnemonic)
                    expected = clc_line(pc, 1, mnemonic)
                    self.assertEqual(self.apply(actual, expected), expected)

    def test_equal_tags_and_reverse_direction(self):
        for actual_tag, reference_tag in ((0, 0), (1, 1), (1, 0)):
            with self.subTest(tags=(actual_tag, reference_tag)):
                actual = clc_line(tag=actual_tag)
                expected = clc_line(tag=reference_tag)
                self.assertEqual(self.apply(actual, expected), actual)

    def test_other_pcs_and_instructions_are_not_ignored(self):
        for pc, mnemonic in (
            ("80000614", "c.CH.clc"), ("80000620", "c.CH.clc"),
            ("80000628", "c.CH.clc"), ("8000063c", "c.CH.clc"),
            ("80000618", "CH.cmove"), ("80000618", "lw"),
            ("80000618", "clc.invalid"),
        ):
            with self.subTest(pc=pc, mnemonic=mnemonic):
                actual = clc_line(pc, 0, mnemonic)
                self.assertEqual(self.apply(actual, clc_line(pc, 1, mnemonic)), actual)

    def test_no_other_difference_is_masked(self):
        expected = clc_line(tag=1)
        changes = (
            ("x9=0x80001000", "x9=0x80001004"),
            ("x9=", "x10="),
            ("+0x07e380000", "+0x07e380001"),
            ("x8:0x80010000", "x8:0x80010004"),
            ("x8:0x80010000+0x17e1a0000", "x8:0x80010000+0x07e1a0000"),
            ("PA:0x80010020", "PA:0x80010024"),
            ("load:0x80001000+0x17e380000", "load:0x80001000+0x07e380000"),
            ("7004", "7008"),
        )
        for old, new in changes:
            with self.subTest(change=(old, new)):
                actual = clc_line().replace(old, new)
                self.assertEqual(self.apply(actual, expected), actual)

    def test_traps_and_multiple_capability_writes_are_not_ignored(self):
        for suffix in (" --> trap", " x10=0x80001000+0x17e380000"):
            actual, expected = clc_line() + suffix, clc_line(tag=1) + suffix
            self.assertEqual(self.apply(actual, expected), actual)

    def test_requires_opt_in_and_exact_test_name(self):
        self.assertTrue(diff_files.is_isa_test1_pair(
            "trace.isa_test1.memdly.clog", "../run_ibex/trace.isa_test1.clog"))
        self.assertFalse(diff_files.is_isa_test1_pair(
            "trace.isa_test1a.default.clog", "../run_ibex/trace.isa_test1a.clog"))
        self.assertFalse(diff_files.is_isa_test1_pair(
            "trace.isa_test1.clog", "trace.isa_test1.default.clog"))
        with tempfile.TemporaryDirectory(dir=Path(__file__).parent) as directory:
            actual = Path(directory) / "trace.isa_test1.default.clog"
            expected = Path(directory) / "trace.isa_test1.clog"
            actual.write_text(clc_line() + "\n")
            expected.write_text(clc_line(tag=1) + "\n")
            before = (actual.read_bytes(), expected.read_bytes())
            for flags, matches in (([], False), (["--isa-test1-clc-tag"], True)):
                output = io.StringIO()
                with mock.patch("sys.argv", ["diff_files.py", *flags, str(actual),
                                             str(expected)]), contextlib.redirect_stdout(output):
                    self.assertEqual(diff_files.main(), 0)
                self.assertEqual("Files match" in output.getvalue(), matches)
            self.assertEqual((actual.read_bytes(), expected.read_bytes()), before)
        with mock.patch("sys.argv", ["diff_files.py", "--isa-test1-clc-tag",
                                    "trace.isa_test1a.default.clog", "trace.isa_test1a.clog"]), \
                contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
            diff_files.main()
        self.assertEqual(error.exception.code, 2)

    def test_gui_receives_the_same_normalized_lines_and_cleans_up(self):
        with tempfile.TemporaryDirectory(dir=Path(__file__).parent) as directory:
            actual = Path(directory) / "trace.isa_test1.default.clog"
            expected = Path(directory) / "trace.isa_test1.clog"
            actual.write_text(clc_line() + "\n")
            expected.write_text(clc_line(tag=1) + "\n")
            copies = []

            def tkdiff(command, check):
                self.assertEqual(command[0], "tkdiff")
                self.assertFalse(check)
                left, right = map(Path, command[1:])
                self.assertEqual(left.read_text(), expected.read_text())
                self.assertEqual(right.read_text(), expected.read_text())
                copies.extend((left, right))
                return subprocess.CompletedProcess(command, 0)

            with mock.patch("sys.argv", ["diff_files.py", "--isa-test1-clc-tag",
                                        "--tkdiff", str(actual), str(expected)]), \
                    mock.patch.object(diff_files.subprocess, "run", side_effect=tkdiff):
                self.assertEqual(diff_files.main(), 0)
            self.assertTrue(all(not path.exists() for path in copies))
            self.assertEqual(actual.read_text(), clc_line() + "\n")
            self.assertEqual(expected.read_text(), clc_line(tag=1) + "\n")

    def test_existing_ignore_rules(self):
        trapped = "80000000 CH.clc c1,0(c2) --> trap PA:0x10 load:0x42"
        self.assertEqual(diff_files.normalize_line(trapped, True),
                         "80000000 CH.clc c1,0(c2) --> trap")
        self.assertEqual(
            diff_files.normalize_line("80000000 c.addi x0,1 x0:0x0", True),
            diff_files.normalize_line("80000000 c.addi x0,1 x9:0xff", True),
        )


if __name__ == "__main__":
    unittest.main()
