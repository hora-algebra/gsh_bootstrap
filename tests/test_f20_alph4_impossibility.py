"""Acceptance tests for the F_20 four-letter impossibility support audit."""

import unittest

from scripts.ci.f20_alph4_impossibility import (
    character_orthogonality_audit,
    four_image_fibre_audit,
    same_phase_power_audit,
)


class F20AlphabetFourImpossibilityTests(unittest.TestCase):
    def test_every_same_phase_difference_survives_fourth_power(self) -> None:
        result = same_phase_power_audit()
        self.assertEqual(result["pairs"], 80)
        self.assertTrue(result["all_nonidentity_kernel"])
        self.assertTrue(result["all_order_five"])
        self.assertTrue(result["fourth_powers_nonidentity"])

    def test_wrong_fifth_power_control_loses_the_contradiction(self) -> None:
        result = same_phase_power_audit()
        self.assertTrue(result["fifth_powers_identity"])

    def test_four_images_collapse_fibres_but_five_need_not(self) -> None:
        result = four_image_fibre_audit()
        self.assertEqual(result["sections"], 625)
        self.assertEqual(result["collisions"], 50_000)
        self.assertTrue(result["all_collapse"])
        self.assertTrue(result["five_image_control"])

    def test_nontrivial_character_sums_vanish(self) -> None:
        result = character_orthogonality_audit()
        self.assertEqual(result["image_orders"], (2, 4))
        self.assertEqual(result["root_sums"], {2: 0, 4: 0})
        self.assertTrue(result["all_zero"])


if __name__ == "__main__":
    unittest.main()
