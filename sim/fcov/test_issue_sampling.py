# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Fast structural tripwires for the issuer's single multi-event covergroup."""

from pathlib import Path
import re
import unittest

from count_cov import census, strip_comments


class IssueSamplingTests(unittest.TestCase):
    def setUp(self):
        self.source = (Path(__file__).parent / "kudu_fcov_issue.sv").read_text()

    def test_single_group_preserves_census(self):
        groups, _ = census([self.source])
        self.assertEqual(set(groups), {"FC_MA_ISSUE"})
        row = groups["FC_MA_ISSUE"]
        self.assertEqual([row[k] for k in
                          ("types", "new_decls", "cps", "crosses", "bins",
                           "illegal_bins", "ignore_bins")], [1, 1, 113, 17, 440, 10, 11])

    def test_all_forwarding_pairs_are_normal_in_every_register(self):
        for r in range(1, 32):
            declaration = re.search(
                rf"cp_fwd_wrsv_r{r}:.*?(?=\n    \}})", self.source, re.S)[0]
            with self.subTest(register=r):
                for pair, bits in ((0, "00"), (1, "01"), (2, "10"), (3, "11")):
                    self.assertIn(f"bins pair_{pair} = {{2'b{bits}}};", declaration)
                self.assertNotIn("illegal_bins", declaration)
        self.assertNotIn("AssertFwdRequiresReservation", self.source)
        self.assertNotIn("g_fwd_wrsv_assert", self.source)

    def test_every_point_and_cross_is_event_qualified(self):
        event_points = {
            "ISSUE_OPERAND": ("cp_consumer_slot", "cp_operand", "cp_operand_outcome",
                              "cp_producer", "cp_consumer_class", "cp_issued",
                              "x_operand_outcome_issue", "x_fwd_producer_consumer"),
            "ISSUE_BP_RESOLUTION": ("cp_resolution_slot", "cp_resolution_kind",
                                    "cp_predicted_taken", "cp_actual_taken",
                                    "cp_recovery", "x_prediction_resolution_recovery"),
            "ISSUE_CHERI_DEP": ("cp_cheri_slot", "cp_cheri_temporal_outcome",
                                "cp_cheri_temporal_issued", "x_cheri_temporal_issue",
                                "cp_cheri_dep_class", "x_cheri_dep_consumer"),
        }
        modes = {name: mode for mode, names in event_points.items() for name in names}
        source = strip_comments(self.source)
        group = re.search(r"\bcovergroup cg_ma_issue\b(.*?)\bendgroup\b", source, re.S)[1]
        declarations = list(re.finditer(r"\b(\w+)\s*:\s*(coverpoint|cross)\b", group))
        self.assertEqual(len(declarations), 130)
        for index, match in enumerate(declarations):
            end = declarations[index + 1].start() if index + 1 < len(declarations) else len(group)
            declaration = group[match.end():end]
            header = re.split(r"\b(?:option|bins|ignore_bins|illegal_bins)\b", declaration)[0]
            mode = modes.get(match[1], "ISSUE_CYCLE")
            with self.subTest(point=match[1]):
                self.assertRegex(header, r"\biff\s*\(\s*event_kind\s*==\s*" + mode + r"\b")


if __name__ == "__main__":
    unittest.main()
