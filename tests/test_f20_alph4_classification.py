"""Acceptance tests for the exact F_20 four-letter classification."""

import unittest

from scripts.ci.f20_alph4_classification import audit


class F20AlphabetFourClassificationTests(unittest.TestCase):
    def test_all_full_phase_sections_and_complements(self) -> None:
        result = audit()
        self.assertEqual(result["sections"], 625)
        self.assertEqual(result["distinct_sections"], 625)
        self.assertEqual(result["subgroup_orders"], {4: 5, 20: 620})
        self.assertEqual(result["complements"], 5)
        self.assertTrue(result["exceptional_match_complements"])

    def test_automorphism_orbits_are_complete(self) -> None:
        result = audit()
        self.assertEqual(result["automorphisms"], 20)
        self.assertEqual(result["automorphism_candidates"], 40)
        self.assertTrue(result["phase_preserved"])
        self.assertEqual(result["orbits"], 32)
        self.assertEqual(result["orbit_profile"], {(5, 4): 1, (20, 20): 31})
        self.assertEqual(result["orbit_coverage"], 625)
        self.assertEqual(result["projective_keys"], 31)
        self.assertTrue(result["invariant_matches_orbits"])

    def test_false_identity_exception_rule_is_rejected(self) -> None:
        result = audit()
        self.assertEqual(result["identity_containing"], 125)
        self.assertNotEqual(
            result["identity_containing"], result["subgroup_orders"][4]
        )


if __name__ == "__main__":
    unittest.main()
