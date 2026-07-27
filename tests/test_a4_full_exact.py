import unittest

from scripts.ci.completeness_upgrade import (
    check_a4_full_alphabet,
    check_a4_full_feature_equations,
    check_a4_full_reconstruction,
    check_a4_full_step4,
    check_a4_full_token_aperiodicity,
    check_a4_full_token_factorization,
)


class A4FullExactTests(unittest.TestCase):
    """Acceptance tests for replacing the sampled A4 reconstruction checks."""

    def test_every_used_token_dfa_is_aperiodic(self):
        ok, universe, _ = check_a4_full_token_aperiodicity()
        self.assertTrue(ok)
        self.assertGreater(universe, 0)

    def test_aperiodicity_rejects_the_excluded_repeat_pattern(self):
        ok, _, _ = check_a4_full_token_aperiodicity(
            include_forbidden_repeat=True
        )
        self.assertFalse(ok)

    def test_cut_parity_has_the_claimed_one_star_factorization(self):
        ok, universe, _ = check_a4_full_token_factorization()
        self.assertTrue(ok)
        self.assertGreater(universe, 0)

    def test_factorization_rejects_single_blocks_in_the_parity_loop(self):
        ok, _, _ = check_a4_full_token_factorization(pair_power=1)
        self.assertFalse(ok)

    def test_factorization_requires_the_zero_cut_even_case(self):
        ok, _, _ = check_a4_full_token_factorization(
            include_zero_cut_case=False
        )
        self.assertFalse(ok)

    def test_feature_equations_hold_for_every_reachable_state(self):
        ok, universe, _ = check_a4_full_feature_equations()
        self.assertTrue(ok)
        self.assertGreater(universe, 0)

    def test_feature_equations_reject_a_wrong_pattern_target(self):
        ok, _, _ = check_a4_full_feature_equations(pattern_target_shift=1)
        self.assertFalse(ok)

    def test_feature_equations_reject_every_registered_control(self):
        controls = (
            {"pattern_target_shift": 1},
            {"claimed_arrival_shift": 1},
            {"nonmover_exception_shift": 1},
        )
        for control in controls:
            with self.subTest(control=control):
                ok, _, _ = check_a4_full_feature_equations(**control)
                self.assertFalse(ok)

    def test_reconstruction_holds_for_every_reachable_state(self):
        ok, universe, _ = check_a4_full_reconstruction()
        self.assertTrue(ok)
        self.assertGreater(universe, 0)

    def test_reconstruction_rejects_a_wrong_backward_shift(self):
        ok, _, _ = check_a4_full_reconstruction(backward_n_shift=1)
        self.assertFalse(ok)

    def test_reconstruction_rejects_every_registered_control(self):
        controls = (
            {"forward_n_shift": 1},
            {"backward_n_shift": 1},
            {"forward_boundary_shift": 1},
            {"backward_boundary_shift": 1},
            {"letter_count_flip": 1},
            {"successor_orientation_flip": True},
            {"successor_phase_shift": 1},
        )
        for control in controls:
            with self.subTest(control=control):
                ok, _, _ = check_a4_full_reconstruction(**control)
                self.assertFalse(ok)

    def test_concrete_alphabet_is_exactly_a4(self):
        ok, universe, _ = check_a4_full_alphabet()
        self.assertTrue(ok)
        self.assertEqual(universe, 24)

    def test_alphabet_check_rejects_a_missing_letter(self):
        ok, _, _ = check_a4_full_alphabet(omit_last_letter=True)
        self.assertFalse(ok)

    def test_alphabet_check_rejects_a_shifted_decomposition(self):
        ok, _, _ = check_a4_full_alphabet(decomposition_shift=1)
        self.assertFalse(ok)

    def test_group_formula_holds_at_every_reachable_state(self):
        ok, universe, _ = check_a4_full_step4()
        self.assertTrue(ok)
        self.assertEqual(universe, 12)

    def test_group_formula_rejects_every_registered_control(self):
        controls = ({"shift": 1}, {"phase_stride": 2})
        for control in controls:
            with self.subTest(control=control):
                ok, _, _ = check_a4_full_step4(**control)
                self.assertFalse(ok)


if __name__ == "__main__":
    unittest.main()
