"""Acceptance tests for the sharp F_20 five-letter reduction."""

import unittest

from scripts.ci.f20_alph5_reduction import (
    construction_audit,
    control_audit,
    erased_alphabet_audit,
    homomorphism_formula_audit,
)


class F20AlphabetFiveReductionTests(unittest.TestCase):
    def test_all_sixteen_maps_have_exactly_five_images_and_form_a_section(self) -> None:
        result = construction_audit()
        self.assertEqual(result["coordinates"], 16)
        self.assertEqual(result["distinct_alphabets"], 4)
        self.assertTrue(result["all_images_exactly_five"])
        self.assertEqual(result["letters_checked"], 20)
        self.assertTrue(result["section_on_all_letters"])

    def test_erasure_leaves_four_generating_four_letter_alphabets(self) -> None:
        result = erased_alphabet_audit()
        self.assertEqual(result["sizes"], (4, 4, 4, 4))
        self.assertEqual(result["generated_orders"], (20, 20, 20, 20))
        self.assertTrue(result["all_generate_f20"])

    def test_rho_homomorphism_formula_on_all_scalar_summaries(self) -> None:
        result = homomorphism_formula_audit()
        self.assertEqual(result["scalar_summaries"], 400)
        self.assertTrue(result["all_hold"])

    def test_load_bearing_mutations_fail(self) -> None:
        result = control_audit()
        self.assertTrue(result["dropping_level_four_breaks_beta_four"])
        self.assertTrue(result["unlocalized_threshold_has_eight_images"])
        self.assertTrue(result["one_value_mutation_breaks_section"])


if __name__ == "__main__":
    unittest.main()
