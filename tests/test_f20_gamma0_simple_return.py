"""Acceptance tests for the exact Gamma_0 simple-first-return token audit."""

import unittest

from scripts.ci.f20_gamma0_simple_return import (
    OLD_WITNESSES,
    SKELETON_NAMES,
    candidate_audit,
    first_return_control_audit,
    old_cut_audit,
    skeleton_audit,
    two_letter_audit,
)


EXPECTED_SKELETONS = (
    "bbbb",
    "bbc",
    "bcb",
    "bcdc",
    "bd",
    "cbb",
    "cbcd",
    "cc",
    "cdcb",
    "cdd",
    "db",
    "dcbc",
    "dcd",
    "ddc",
    "dddd",
)

EXPECTED_OLD_WITNESSES = (
    "bbdd",
    "a",
    "dab",
    "cbb",
    "bcb",
    "db",
    "cac",
    "bbc",
    "cc",
    "ddc",
    "bad",
    "bd",
    "dcd",
    "cdd",
)


class F20GammaZeroSimpleReturnTests(unittest.TestCase):
    def test_exact_simple_first_return_skeletons(self) -> None:
        result = skeleton_audit()
        self.assertEqual(SKELETON_NAMES, EXPECTED_SKELETONS)
        self.assertEqual(result["skeletons"], 15)
        self.assertTrue(result["all_first_return"])
        self.assertTrue(result["all_nonzero_states_distinct"])
        self.assertEqual(result["first_excluded_first_return"], "bbdd")

    def test_minimal_dfa_and_complete_transition_monoid(self) -> None:
        result = candidate_audit()
        self.assertEqual(result["reachable_states"], 15)
        self.assertEqual(result["minimal_states"], 15)
        self.assertEqual(result["transition_monoid"], 50)
        self.assertTrue(result["finite_star_free_construction"])
        self.assertTrue(result["aperiodic"])
        self.assertEqual(result["maximum_period"], 1)
        self.assertEqual(result["maximum_stabilization_index"], 5)
        self.assertEqual(
            result["stabilization_index_distribution"],
            {1: 3, 2: 36, 3: 5, 4: 4, 5: 2},
        )

    def test_complete_product_comparison_with_old_fourteen(self) -> None:
        result = old_cut_audit()
        self.assertEqual(result["languages"], 14)
        self.assertEqual(result["inequivalent"], 14)
        self.assertEqual(result["product_reachable_states"], 331)
        self.assertEqual(result["product_state_range"], (19, 26))
        self.assertEqual(OLD_WITNESSES, EXPECTED_OLD_WITNESSES)
        self.assertTrue(result["witnesses_match"])
        self.assertTrue(result["all_witnesses_distinguish"])
        self.assertTrue(result["all_old_nonaperiodic"])

    def test_two_letter_restriction_is_the_known_positive_token(self) -> None:
        result = two_letter_audit()
        self.assertEqual(result["candidate_minimal_states"], 6)
        self.assertEqual(result["reference_minimal_states"], 6)
        self.assertEqual(result["product_reachable_states"], 6)
        self.assertTrue(result["equivalent"])
        self.assertEqual(result["transition_monoid"], 16)
        self.assertTrue(result["aperiodic"])

    def test_unrestricted_first_return_has_period_two(self) -> None:
        result = first_return_control_audit()
        self.assertEqual(result["minimal_states"], 6)
        self.assertEqual(result["transition_monoid"], 62)
        self.assertEqual(result["maximum_period"], 2)
        self.assertEqual(result["periodic_letter"], "c")
        self.assertEqual(result["periodic_letter_period"], 2)
        self.assertEqual(result["hierarchy_witness"], "bbdd")
        self.assertTrue(result["natural_accepts_witness"])
        self.assertFalse(result["candidate_accepts_witness"])


if __name__ == "__main__":
    unittest.main()
