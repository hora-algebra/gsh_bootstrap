"""Acceptance tests for star-free-labelled automata (``tools.sf_automaton``).

The tests are the machine-checked form of the statements in
``notes/sf_labeled_automata.md``:

* T1  labels are star-free, i.e. syntactic star height 0 (definition);
* T2  ``star_height(to_expression()) <= loop_complexity()`` — the relativized
      Eggan upper bound, checked on every automaton built here;
* T3  loop complexity agrees with hand-computed values on small graphs;
* T4  the rank-1 calibration automata really define their target languages;
* T5  the four-diagonal automaton of ``L2`` has loop complexity 1 and its
      eliminated first-return / escape expressions agree with the ones
      printed in ``notes/weis_l2_full_height_one.md`` §3;
* T6  the letter-labelled minimal DFA of ``L2`` has loop complexity 2, so the
      drop to 1 is caused by the star-free labels, not by the language alone.
"""

from __future__ import annotations

import unittest

from tools import sf_automaton as sfa
from tools.regex_cert import compile_regex, equivalence_witness
from tools.targets import build_target


def _language_equal(left, right, alphabet) -> bool:
    return equivalence_witness(
        compile_regex(left, alphabet).minimized(),
        compile_regex(right, alphabet).minimized(),
    ) is None


class LabelValidationTests(unittest.TestCase):
    def test_star_free_label_accepted(self) -> None:
        machine = sfa.SFAutomaton(
            alphabet=("a", "b"),
            states=(0,),
            start=frozenset({0}),
            accept=frozenset({0}),
            edges={(0, 0): sfa.words_avoiding(("b",), ("a", "b"))},
        )
        self.assertEqual(machine.loop_complexity(), 1)

    def test_label_containing_a_star_is_rejected(self) -> None:
        with self.assertRaises(sfa.SFAutomatonError):
            sfa.SFAutomaton(
                alphabet=("a", "b"),
                states=(0,),
                start=frozenset({0}),
                accept=frozenset({0}),
                edges={(0, 0): sfa.star(sfa.letter("a"))},
            )

    def test_label_using_an_undeclared_letter_is_rejected(self) -> None:
        # Otherwise `to_expression` emits an expression mentioning `b`, which
        # `tools.regex_cert` then rejects when the certificate is checked
        # against the declared alphabet -- a failure far from its cause.
        with self.assertRaises(sfa.SFAutomatonError):
            sfa.SFAutomaton(
                alphabet=("a",),
                states=(0,),
                start=frozenset({0}),
                accept=frozenset({0}),
                edges={(0, 0): sfa.letter("b")},
            )

    def test_undeclared_letter_is_found_inside_a_compound_label(self) -> None:
        with self.assertRaises(sfa.SFAutomatonError):
            sfa.SFAutomaton(
                alphabet=("a",),
                states=(0, 1),
                start=frozenset({0}),
                accept=frozenset({1}),
                edges={(0, 1): sfa.compl(sfa.concat(sfa.letter("a"), sfa.letter("c")))},
            )


class StarConstructionTests(unittest.TestCase):
    """The automaton-side reading of "apply one more star" (note §3)."""

    def _dag(self):
        # Rank 0: two initial vertices, two accepting vertices, all four edges.
        return sfa.SFAutomaton(
            alphabet=("a", "b"),
            states=("i1", "i2", "f1", "f2"),
            start=frozenset({"i1", "i2"}),
            accept=frozenset({"f1", "f2"}),
            edges={
                (i, f): sfa.letter("a" if f == "f1" else "b")
                for i in ("i1", "i2")
                for f in ("f1", "f2")
            },
        )

    def test_naive_back_edges_can_raise_the_rank_by_two(self) -> None:
        """Why ``apply_star`` adds a hub instead of wiring finals to initials.

        This is the counterexample that the method's docstring cites: the
        bidirected ``K_{2,2}`` has cycle rank 2, so "add an edge from every
        accepting vertex to every initial one" does NOT raise the rank by at
        most one.
        """

        dag = self._dag()
        self.assertEqual(dag.loop_complexity(), 0)
        naive = dict(dag.edges)
        for f in dag.accept:
            for i in dag.start:
                naive[(f, i)] = sfa.EPS
        self.assertEqual(sfa.cycle_rank(dag.states, naive), 2)

    def test_hub_construction_raises_the_rank_by_at_most_one(self) -> None:
        for name, machine in [("dag", self._dag()), *sfa.CALIBRATION.items()]:
            with self.subTest(name=name):
                before = machine.loop_complexity()
                after = machine.apply_star().loop_complexity()
                self.assertLessEqual(after, before + 1)

    def test_hub_construction_accepts_the_star_of_the_language(self) -> None:
        dag = self._dag()
        starred = dag.apply_star()
        self.assertEqual(starred.loop_complexity(), 1)
        self.assertTrue(
            _language_equal(
                starred.to_expression(),
                sfa.star(dag.to_expression()),
                dag.alphabet,
            )
        )


class LoopComplexityTests(unittest.TestCase):
    def _machine(self, states, edge_pairs):
        return sfa.SFAutomaton(
            alphabet=("a",),
            states=tuple(states),
            start=frozenset({states[0]}),
            accept=frozenset({states[-1]}),
            edges={pair: sfa.letter("a") for pair in edge_pairs},
        )

    def test_acyclic_has_rank_zero(self) -> None:
        self.assertEqual(self._machine([0, 1, 2], [(0, 1), (1, 2), (0, 2)]).loop_complexity(), 0)

    def test_single_self_loop_has_rank_one(self) -> None:
        self.assertEqual(self._machine([0, 1], [(0, 0), (0, 1)]).loop_complexity(), 1)

    def test_disjoint_loops_stay_rank_one(self) -> None:
        self.assertEqual(
            self._machine([0, 1, 2], [(0, 0), (0, 1), (1, 2), (2, 2)]).loop_complexity(), 1
        )

    def test_one_vertex_cutting_every_cycle_stays_rank_one(self) -> None:
        # 0 <-> 1 with a self-loop at 1: deleting vertex 1 destroys the
        # 2-cycle and the self-loop at once, so the rank is 1, not 2.
        self.assertEqual(
            self._machine([0, 1], [(0, 1), (1, 0), (1, 1)]).loop_complexity(), 1
        )

    def test_two_self_loops_inside_one_component_has_rank_two(self) -> None:
        # Both states carry a self-loop and the component is strongly
        # connected, so no single deletion makes the graph acyclic.  This is
        # the shape of the minimal DFA of "even number of a".
        self.assertEqual(
            self._machine([0, 1], [(0, 0), (0, 1), (1, 0), (1, 1)]).loop_complexity(), 2
        )


class RankBoundTests(unittest.TestCase):
    """T2: the construction never exceeds the loop complexity.

    The inequality is the invariant that ``to_expression`` enforces on every
    call.  The equality asserted below is the sharper statement of
    Sakarovitch §3.6 (Property 3.12 with Proposition 3.13): the minimum over
    elimination orders equals the loop complexity, and the order derived from
    the cycle-rank recursion is meant to attain it.  A failure here would mean
    the witness-vertex choice is not realizing the rank, which is worth
    knowing -- so this is deliberately an assertEqual, not an assertLessEqual.
    """

    def test_bound_holds_on_every_calibration_automaton(self) -> None:
        for name, machine in sfa.CALIBRATION.items():
            with self.subTest(name=name):
                rank = machine.loop_complexity()
                expression = machine.to_expression()
                self.assertLessEqual(expression.star_height(), rank)
                self.assertEqual(expression.star_height(), rank)

    def test_bound_holds_on_letter_labelled_targets(self) -> None:
        for name in ("even_a", "z3", "aa_star", "ends_a"):
            with self.subTest(name=name):
                dfa = build_target(name)
                machine = sfa.from_dfa(dfa)
                self.assertEqual(
                    machine.to_expression().star_height(), machine.loop_complexity()
                )


class CalibrationTests(unittest.TestCase):
    """T4: the rank-1 automata define the intended languages."""

    def test_even_a_rank_one(self) -> None:
        machine = sfa.CALIBRATION["even_a"]
        self.assertEqual(machine.loop_complexity(), 1)
        expression = machine.to_expression()
        self.assertEqual(expression.star_height(), 1)
        self.assertIsNone(
            equivalence_witness(
                compile_regex(expression, machine.alphabet).minimized(),
                build_target("even_a"),
            )
        )

    def test_z3_rank_one(self) -> None:
        machine = sfa.CALIBRATION["z3"]
        self.assertEqual(machine.loop_complexity(), 1)
        self.assertIsNone(
            equivalence_witness(
                compile_regex(machine.to_expression(), machine.alphabet).minimized(),
                build_target("z3"),
            )
        )

    def test_self_loop_absorption_preserves_language_and_drops_rank(self) -> None:
        alphabet = ("a", "b")
        dfa = build_target("even_a")
        letter_labelled = sfa.from_dfa(dfa)
        self.assertEqual(letter_labelled.loop_complexity(), 2)
        absorbed = letter_labelled
        for state in dfa.states:
            absorbed = absorbed.absorb_self_loop(
                state, sfa.words_avoiding(("a",), alphabet)
            )
        self.assertEqual(absorbed.loop_complexity(), 1)
        self.assertIsNone(
            equivalence_witness(
                compile_regex(absorbed.to_expression(), alphabet).minimized(), dfa
            )
        )


class WeisL2Tests(unittest.TestCase):
    """T5/T6: the L2 measurement."""

    def test_diagonal_automaton_has_rank_one(self) -> None:
        machine = sfa.CALIBRATION["weis_l2_diagonals"]
        self.assertEqual(machine.loop_complexity(), 1)
        self.assertEqual(machine.to_expression().star_height(), 1)

    def test_first_return_matches_published_note(self) -> None:
        """``R_{D2} = (a | b a* b a* b)(a | b)`` — notes/weis_l2_full_height_one.md §3."""

        alphabet = ("a", "b")
        a_star = sfa.words_avoiding(("b",), alphabet)
        expected = sfa.concat(
            sfa.union(
                sfa.letter("a"),
                sfa.concat(
                    sfa.letter("b"), a_star, sfa.letter("b"), a_star, sfa.letter("b")
                ),
            ),
            sfa.union(sfa.letter("a"), sfa.letter("b")),
        )
        actual = sfa.first_return(sfa.WEIS_L2_DIAGONAL_GRAPH, "D2")
        self.assertEqual(actual.star_height(), 0)
        self.assertTrue(_language_equal(actual, expected, alphabet))

    def test_escape_languages_match_published_note(self) -> None:
        alphabet = ("a", "b")
        a_star = sfa.words_avoiding(("b",), alphabet)
        b = sfa.letter("b")
        a = sfa.letter("a")
        expected = {
            "D3": sfa.union(a, sfa.concat(b, a_star, b, a_star, b)),
            "D1": sfa.concat(b, a_star),
            "D0": sfa.concat(b, a_star, b, a_star),
        }
        escapes = sfa.escapes(sfa.WEIS_L2_DIAGONAL_GRAPH, "D2")
        for target, want in expected.items():
            with self.subTest(target=target):
                self.assertEqual(escapes[target].star_height(), 0)
                self.assertTrue(_language_equal(escapes[target], want, alphabet))

    def test_letter_labelled_minimal_dfa_has_rank_two(self) -> None:
        machine = sfa.from_dfa(sfa.weis_l2_minimal_dfa())
        self.assertEqual(len(machine.states), 6)
        self.assertEqual(machine.loop_complexity(), 2)
        self.assertLessEqual(machine.to_expression().star_height(), 2)


if __name__ == "__main__":
    unittest.main()
