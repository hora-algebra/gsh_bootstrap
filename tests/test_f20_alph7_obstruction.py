"""Acceptance tests for the seven-letter F_20 cut-mechanism audit.

The target is deliberately negative and mechanism-scoped: the seven-letter
alphabet reduction does not repair the pattern-conditioned cuts of
``F20-FULL-OBS-01``.  It is not a lower bound on generalized star height.
"""

import unittest

from scripts.ci.f20_alph7_obstruction import (
    DELTA7,
    TWO_GENERATOR,
    check_collision_witness,
    check_pattern_universe,
    check_shortest_collision,
)


class F20AlphabetSevenObstructionTests(unittest.TestCase):
    def test_all_seventeen_pattern_signatures_are_nonaperiodic(self) -> None:
        ok, signatures, _ = check_pattern_universe(DELTA7)
        self.assertTrue(ok)
        self.assertEqual(signatures, 17)

    def test_pattern_judge_can_accept_the_two_generator_control(self) -> None:
        ok, _, _ = check_pattern_universe(TWO_GENERATOR)
        self.assertFalse(ok)

    def test_explicit_length_four_words_collide_in_every_certified_feature(self) -> None:
        ok, fields, _ = check_collision_witness()
        self.assertTrue(ok)
        self.assertGreater(fields, 0)

    def test_collision_requires_distinct_group_images(self) -> None:
        ok, _, _ = check_collision_witness(force_same_word=True)
        self.assertFalse(ok)

    def test_the_collision_is_shortest(self) -> None:
        ok, words, _ = check_shortest_collision()
        self.assertTrue(ok)
        self.assertEqual(words, 1 + 7 + 7**2 + 7**3)

    def test_shortest_check_notices_missing_letter_counts(self) -> None:
        ok, _, _ = check_shortest_collision(include_letter_counts=False)
        self.assertFalse(ok)


if __name__ == "__main__":
    unittest.main()
