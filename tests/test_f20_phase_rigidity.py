"""Acceptance tests for the F_20 phase-rigidity support calculations."""

import unittest

from scripts.ci.f20_phase_rigidity import (
    check_conjugation_action,
    check_phase_only_binary_control,
    generating_pair_audit,
)


class F20PhaseRigidityTests(unittest.TestCase):
    def test_conjugation_character_in_repository_convention(self) -> None:
        ok, pairs, _ = check_conjugation_action()
        self.assertTrue(ok)
        self.assertEqual(pairs, 20 * 5)

    def test_phase_quotient_alone_has_a_two_binary_coordinate_model(self) -> None:
        ok, cases, _ = check_phase_only_binary_control()
        self.assertTrue(ok)
        self.assertEqual(cases, 4**4 + 4)

    def test_wrong_phase_recovery_coefficient_is_rejected(self) -> None:
        ok, _, _ = check_phase_only_binary_control(coefficient=1)
        self.assertFalse(ok)

    def test_all_generating_pairs_and_standard_automorphism_orbit(self) -> None:
        audit = generating_pair_audit()
        self.assertEqual(audit["two_subsets"], 190)
        self.assertEqual(audit["generating"], 120)
        self.assertEqual(audit["profiles"], {(4, 5): 40, (4, 4): 40, (2, 4): 40})
        self.assertEqual(audit["automorphisms"], 20)
        self.assertEqual(audit["standard_orbit"], 20)
        self.assertEqual(audit["uncovered"], 100)


if __name__ == "__main__":
    unittest.main()
