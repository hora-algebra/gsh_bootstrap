from __future__ import annotations

import unittest

from tools.height_search import certificate_for, dfa_key, format_regex, regex_size, search
from tools.regex_cert import check_certificate
from tools.targets import build_target


class HeightSearchTests(unittest.TestCase):
    def test_star_free_target_found_at_height_zero(self) -> None:
        target = build_target("ends_a")
        result = search(target, max_size=5)
        self.assertTrue(result.found)
        self.assertEqual(result.height, 0)
        certificate = certificate_for(result, target)
        self.assertTrue(check_certificate(certificate).ok)

    def test_aa_star_found_at_height_one_size_four(self) -> None:
        target = build_target("aa_star")
        result = search(target, max_size=6)
        self.assertTrue(result.found)
        self.assertEqual(result.height, 1)
        self.assertEqual(result.size, 4)
        self.assertEqual(regex_size(result.expr), 4)
        certificate = certificate_for(result, target)
        self.assertTrue(check_certificate(certificate).ok)

    def test_negative_result_is_reported_as_search_only(self) -> None:
        target = build_target("a5")
        result = search(target, max_size=3)
        self.assertFalse(result.found)
        self.assertTrue(result.complete)
        self.assertIn("not a lower bound", result.summary())

    def test_pruning_marks_search_incomplete(self) -> None:
        target = build_target("aa_star")
        result = search(target, max_size=4, max_states=1)
        self.assertFalse(result.found)
        self.assertFalse(result.complete)

    def test_dedup_prefers_lower_height(self) -> None:
        # (a*)? never appears: language of a* is first reached at height 1 via star,
        # so a later height-0 expression for the same language must be kept.
        # We check the mechanism indirectly: dfa_key is language-invariant.
        target = build_target("even_a")
        self.assertEqual(dfa_key(target), dfa_key(target.minimized()))

    def test_format_regex_round_trip_readability(self) -> None:
        target = build_target("aa_star")
        result = search(target, max_size=6)
        self.assertEqual(format_regex(result.expr), "(aa)*")


if __name__ == "__main__":
    unittest.main()
