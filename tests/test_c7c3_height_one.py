"""Acceptance tests for the finite core of the ``C_7 : C_3`` proof.

The mathematical target is the full ``HeightOneForGroup`` statement, not the
old bounded-word reconstruction.  The only finite obligations checked here are
the ones used by the Schuetzenberger/token-factorisation proof.
"""

import unittest

from scripts.ci.c7c3_height_one import (
    check_atom_coverage,
    check_residue_factorization,
    check_token_aperiodicity,
)


class C7C3HeightOneTests(unittest.TestCase):
    def test_every_first_and_post_cut_token_is_aperiodic(self):
        ok, cases, _ = check_token_aperiodicity()
        self.assertTrue(ok)
        # 17 used pattern signatures, 3 cut phases, 2 initial-state roles.
        self.assertEqual(cases, 17 * 3 * 2)

    def test_aperiodicity_check_covers_first_tokens(self):
        ok, _, _ = check_token_aperiodicity(include_first_tokens=False)
        self.assertFalse(ok)

    def test_aperiodicity_rejects_a_periodic_repeat_pattern(self):
        ok, _, _ = check_token_aperiodicity(use_repeat_control=True)
        self.assertFalse(ok)

    def test_mod_seven_factorization_is_exact(self):
        ok, cases, _ = check_residue_factorization()
        self.assertTrue(ok)
        # Every used pattern signature, cut phase, and residue is decided.
        self.assertEqual(cases, 17 * 3 * 7)

    def test_factorization_rejects_six_token_loops(self):
        ok, _, _ = check_residue_factorization(loop_power=6)
        self.assertFalse(ok)

    def test_factorization_requires_the_zero_cut_case(self):
        ok, _, _ = check_residue_factorization(include_zero_cut_case=False)
        self.assertFalse(ok)

    def test_all_57_arithmetic_atoms_are_covered(self):
        ok, atoms, _ = check_atom_coverage()
        self.assertTrue(ok)
        self.assertEqual(atoms, 57)

    def test_atom_coverage_requires_reversal(self):
        ok, _, _ = check_atom_coverage(allow_reversal=False)
        self.assertFalse(ok)


if __name__ == "__main__":
    unittest.main()
