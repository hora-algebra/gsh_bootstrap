"""Acceptance tests for the exact F_20 Gamma_r equivalence classification."""

import unittest

from scripts.ci.f20_gamma4_equivalence import (
    exact_language_matrices,
    fixed_context_audit,
    length_six_control_audit,
    structural_image_matrices,
)


DIRECT = (
    (1, 0, 0, 0),
    (0, 1, 0, 0),
    (0, 0, 1, 0),
    (0, 0, 0, 1),
)
REVERSED = (
    (1, 0, 0, 0),
    (0, 0, 0, 1),
    (0, 0, 1, 0),
    (0, 1, 0, 0),
)


class F20GammaFourEquivalenceTests(unittest.TestCase):
    def test_all_automorphisms_and_anti_automorphisms_have_expected_images(self) -> None:
        result = structural_image_matrices()
        self.assertEqual(result["automorphism"], DIRECT)
        self.assertEqual(result["anti_automorphism"], REVERSED)
        self.assertEqual(result["automorphisms"], 20)
        self.assertEqual(result["anti_automorphisms"], 20)
        self.assertTrue(result["all_distinct"])
        self.assertTrue(result["all_bijective"])
        self.assertTrue(result["hom_and_anti_laws"])

    def test_all_letter_maps_are_decided_by_complete_product_reachability(self) -> None:
        result = exact_language_matrices()
        self.assertEqual(result["maps_checked_each_mode"], 4096)
        self.assertEqual(result["direct"], DIRECT)
        self.assertEqual(result["reversed"], REVERSED)
        self.assertEqual(result["largest_reachable_product"], 400)
        self.assertEqual(result["reachable_states_each_mode"], (1_152_000, 1_152_000))
        self.assertEqual(result["transitions_each_mode"], (4_608_000, 4_608_000))
        expected_lengths = {2: 4074, 3: 2, 4: 12, 5: 3, 6: 1}
        self.assertEqual(result["direct_witness_lengths"], expected_lengths)
        self.assertEqual(result["reversed_witness_lengths"], expected_lengths)
        self.assertTrue(result["accepted_maps_match_structure"])

    def test_length_six_control_rejects_bounded_word_and_order_mutations(self) -> None:
        result = length_six_control_audit()
        self.assertEqual(result["length"], 6)
        self.assertTrue(result["source_nonidentity"])
        self.assertTrue(result["direct_target_identity"])
        self.assertTrue(result["reversed_target_identity"])
        self.assertEqual(result["direct_shortest_length"], 6)
        self.assertEqual(result["reversed_shortest_length"], 6)
        self.assertTrue(result["both_mutations_rejected"])

    def test_fixed_contexts_create_no_new_identity_fibre_equivalence(self) -> None:
        result = fixed_context_audit()
        self.assertEqual(result["contexts"], 400)
        self.assertEqual(result["empty_rejected"], 380)
        self.assertEqual(result["identity_contexts"], 20)
        self.assertTrue(result["all_identity_contexts_are_conjugation"])


if __name__ == "__main__":
    unittest.main()
