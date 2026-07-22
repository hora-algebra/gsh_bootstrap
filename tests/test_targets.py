from __future__ import annotations

import itertools
import unittest

from tools.targets import (
    build_target,
    cycles_to_permutation,
    scattered_subword_count,
    subword_count_mod_dfa,
    word_problem_dfa,
)


def all_words(alphabet: str, max_length: int):
    for length in range(max_length + 1):
        for word in itertools.product(alphabet, repeat=length):
            yield "".join(word)


class WordProblemTests(unittest.TestCase):
    def test_group_orders_match_state_counts(self) -> None:
        for name, order in [("z3", 3), ("a4_std", 12), ("a4_two_3cycles", 12), ("s4", 24), ("a5", 60)]:
            with self.subTest(name=name):
                self.assertEqual(len(build_target(name).states), order)

    def test_word_problem_acceptance_is_morphism_kernel(self) -> None:
        a = cycles_to_permutation(4, [(0, 1, 2)])
        b = cycles_to_permutation(4, [(0, 1), (2, 3)])
        machine = word_problem_dfa({"a": a, "b": b})
        identity = tuple(range(4))
        for word in all_words("ab", 6):
            image = identity
            for letter in word:
                perm = a if letter == "a" else b
                image = tuple(image[perm[i]] for i in range(4))
            self.assertEqual(machine.accepts(word), image == identity, word)

    def test_rejects_mismatched_degrees(self) -> None:
        with self.assertRaises(ValueError):
            word_problem_dfa({"a": (1, 0), "b": (0, 1, 2)})


class SubwordCountTests(unittest.TestCase):
    def test_matches_reference_count_mod_n(self) -> None:
        machine = subword_count_mod_dfa("aab", 0, 4)
        for word in all_words("ab", 8):
            expected = scattered_subword_count(word, "aab") % 4 == 0
            self.assertEqual(machine.accepts(word), expected, word)

    def test_reference_count_small_cases(self) -> None:
        self.assertEqual(scattered_subword_count("aab", "aab"), 1)
        self.assertEqual(scattered_subword_count("aaab", "aab"), 3)
        self.assertEqual(scattered_subword_count("abab", "ab"), 3)
        self.assertEqual(scattered_subword_count("bbb", "aab"), 0)


if __name__ == "__main__":
    unittest.main()
