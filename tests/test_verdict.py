"""Acceptance tests for `tools/verdict.py`.

The module's job is to make a `COMPUTED` label unwritable unless a program
earned it.  So every test here is a *negative* control on the module itself:
each one exhibits a way of not having tested the claim, and asserts that the
ceiling comes out below `COMPUTED`.  A verdict library whose own tests only
check the happy path would be the same mistake one level up.
"""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from tools.verdict import (
    Check,
    Control,
    Observable,
    Run,
    VerdictError,
    decide_linear_identity,
    exhaustive,
    load,
    sampled,
)


# --------------------------------------------------------------------------
# The identity that motivated the module: THOMAS-D2-02.
#
#   #ab == |w|_a + 2|w|_b - 2*#tok - [word ends mid-token]
#
# over the prefix code {b, aa, ab}, written as a form that must vanish.  The
# version in the repository on 2026-07-25 was certified by a machine whose state
# was `(parse, d)` with `d` defined to be -1 exactly when `parse == 1`, and
# whose acceptance test asked whether `d == -1` when `parse == 1`.  It traversed
# a finite object exhaustively.  The object had nothing to do with the identity.
# --------------------------------------------------------------------------


def parse_step(parse: int, letter: str) -> int:
    """0 = between tokens; 1 = an `a` was read and the token is incomplete."""
    return 1 if (parse == 0 and letter == "a") else 0


THOMAS_OBSERVABLES = [
    Observable("n_ab", lambda p, x, q: 1 if (p == 1 and x == "b") else 0),
    Observable("len_a", lambda p, x, q: 1 if x == "a" else 0),
    Observable("len_b", lambda p, x, q: 1 if x == "b" else 0),
    Observable("n_tok", lambda p, x, q: 0 if (p == 0 and x == "a") else 1),
    Observable("tail", lambda p, x, q: 0, terminal=lambda p: 1 if p == 1 else 0),
]
THOMAS_COEFFICIENTS = {"n_ab": 1, "len_a": -1, "len_b": -2, "n_tok": 2, "tail": 1}


def thomas(**overrides: int) -> Check:
    coefficients = dict(THOMAS_COEFFICIENTS, **overrides)
    return decide_linear_identity(
        "thomas",
        "THOMAS-D2-02",
        alphabet="ab",
        control_start=0,
        control_step=parse_step,
        observables=THOMAS_OBSERVABLES,
        coefficients=coefficients,
        detail="token-counting identity over {b, aa, ab}",
        covers="claim",
    )


class LinearIdentityTests(unittest.TestCase):
    def test_the_true_identity_is_decided(self) -> None:
        check = thomas()
        self.assertTrue(check.passed)
        self.assertEqual(check.ceiling, "COMPUTED")
        self.assertEqual(check.scope, "exhaustive")

    def test_every_coefficient_perturbation_is_rejected(self) -> None:
        """The property the 2026-07-25 certification did not have.

        Its single control perturbed the acceptance constant, so it fired
        without testing any coefficient of the identity.  Here the controls are
        generated from the coefficients themselves and there is no way to
        supply a machine that ignores them.
        """
        check = thomas()
        self.assertEqual(len(check.controls), 10)
        unnoticed = [c.name for c in check.controls if not c.rejected]
        self.assertEqual(unnoticed, [])

    def test_a_false_identity_fails(self) -> None:
        self.assertFalse(thomas(len_b=-1).passed)

    def test_a_quantity_the_traversal_cannot_see_fails(self) -> None:
        """The shape of the machine this module was written to make impossible.

        An observable that never moves makes the form vanish for every word, so
        the check would "pass" — and so would every perturbation of it, which is
        precisely the evidence that nothing was tested.
        """
        check = decide_linear_identity(
            "degenerate",
            "X-01",
            alphabet="ab",
            control_start=0,
            control_step=parse_step,
            observables=[Observable("invisible", lambda p, x, q: 0)],
            coefficients={"invisible": 1},
            detail="a quantity the traversal cannot see",
        )
        self.assertFalse(check.passed)
        self.assertEqual(check.ceiling, "UNREVIEWED")
        self.assertIn("not noticed", check.detail)

    def test_the_universe_is_the_number_of_states_actually_visited(self) -> None:
        self.assertEqual(thomas().universe, 2)

    def test_a_modular_identity_is_supported(self) -> None:
        """`LAAB-04-01`: binom(w,aab) = M1 + 2*M2 (mod 4), over {a,b}.

        Control state carries `(#a mod 8, binom(#a,2) mod 4)`; every quantity in
        the identity is an observable, so the coefficients stay perturbable.
        """
        check = decide_linear_identity(
            "laab",
            "LAAB-04-01",
            alphabet="ab",
            control_start=(0, 0),
            control_step=lambda s, x: ((s[0] + 1) % 8, (s[1] + s[0]) % 4) if x == "a" else s,
            observables=[
                Observable("binom_aab", lambda s, x, t: s[1] if x == "b" else 0),
                Observable("m1", lambda s, x, t: 1 if (x == "b" and s[0] % 4 in (2, 3)) else 0),
                Observable(
                    "m2", lambda s, x, t: 1 if (x == "b" and s[0] % 8 in (3, 4, 5, 6)) else 0
                ),
            ],
            coefficients={"binom_aab": 1, "m1": -1, "m2": -2},
            modulus=4,
            detail="binom(w,aab) = M1 + 2*M2 (mod 4)",
        )
        self.assertTrue(check.passed, check.detail)
        self.assertEqual(check.ceiling, "COMPUTED")
        self.assertTrue(all(c.rejected for c in check.controls))

    def test_a_coefficient_naming_an_unknown_observable_is_refused(self) -> None:
        with self.assertRaises(VerdictError):
            decide_linear_identity(
                "typo",
                "X-01",
                alphabet="ab",
                control_start=0,
                control_step=parse_step,
                observables=[Observable("a", lambda p, x, q: 1)],
                coefficients={"typoed_name": 1},
                detail="",
            )


class CeilingTests(unittest.TestCase):
    def test_a_sampled_check_can_never_reach_computed(self) -> None:
        check = sampled("bounded", "X-01", passed=True, sample="length <= 16", detail="")
        self.assertEqual(check.ceiling, "EMPIRICAL")

    def test_an_exhaustive_check_with_no_control_is_not_computed(self) -> None:
        """"All N passed" and "the judge always says pass" are the same output."""
        check = exhaustive("swept", "X-01", passed=True, universe=99, detail="")
        self.assertEqual(check.ceiling, "UNREVIEWED")

    def test_an_exhaustive_check_with_a_control_that_fired_is_computed(self) -> None:
        check = exhaustive(
            "swept",
            "X-01",
            passed=True,
            universe=99,
            detail="",
            controls=[Control("shifted residue", "the residue h -> h+1", rejected=True)],
        )
        self.assertEqual(check.ceiling, "COMPUTED")

    def test_a_control_that_did_not_fire_does_not_count(self) -> None:
        check = exhaustive(
            "swept",
            "X-01",
            passed=True,
            universe=99,
            detail="",
            controls=[Control("shifted residue", "the residue h -> h+1", rejected=False)],
        )
        self.assertEqual(check.ceiling, "UNREVIEWED")

    def test_a_failed_check_supports_nothing(self) -> None:
        check = exhaustive(
            "swept",
            "X-01",
            passed=False,
            universe=99,
            detail="",
            controls=[Control("c", "m", rejected=True)],
        )
        self.assertEqual(check.ceiling, "UNREVIEWED")

    def test_an_exhaustive_check_must_have_visited_something(self) -> None:
        with self.assertRaises(VerdictError):
            exhaustive("empty", "X-01", passed=True, universe=0, detail="")

    def test_a_claim_with_no_check_is_unreviewed(self) -> None:
        """Silence is not evidence: the default has to be the weak one."""
        self.assertEqual(Run("s").ceiling("NEVER-MENTIONED-01"), "UNREVIEWED")

    def test_the_weakest_load_bearing_check_sets_the_ceiling(self) -> None:
        run = Run("s")
        run.add(
            exhaustive(
                "a", "X-01", passed=True, universe=9, detail="",
                controls=[Control("c", "m", rejected=True)], covers="claim",
            )
        )
        run.add(sampled("b", "X-01", passed=True, sample="length <= 8", detail=""))
        self.assertEqual(run.ceiling("X-01"), "EMPIRICAL")

    def test_a_sampled_check_marked_not_load_bearing_is_ignored(self) -> None:
        """A sanity-check run alongside a decision procedure must stay writable.

        Deleting the honest mention of a bounded run is what the previous gate
        pushed authors towards; the escape here is structural rather than a
        magic phrase, so it names the check it applies to.
        """
        run = Run("s")
        run.add(
            exhaustive(
                "a", "X-01", passed=True, universe=9, detail="",
                controls=[Control("c", "m", rejected=True)], covers="claim",
            )
        )
        run.add(
            sampled(
                "b", "X-01", passed=True, sample="length <= 8", detail="",
                load_bearing=False,
            )
        )
        self.assertEqual(run.ceiling("X-01"), "COMPUTED")


class RunTests(unittest.TestCase):
    def test_a_run_round_trips_through_its_verdict_file(self) -> None:
        run = Run("scripts/demo.py")
        run.add(thomas())
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "demo.json"
            run.write(path)
            data = load(path)
        self.assertEqual(data["ceilings"], {"THOMAS-D2-02": "COMPUTED"})
        self.assertEqual(data["script"], "scripts/demo.py")

    def test_a_document_that_is_not_a_verdict_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "other.json"
            path.write_text(json.dumps({"schema": "something-else"}), encoding="utf-8")
            with self.assertRaises(VerdictError):
                load(path)

    def test_finish_reports_failure_through_the_exit_status(self) -> None:
        run = Run("scripts/demo.py")
        run.add(thomas(len_b=-1))
        with tempfile.TemporaryDirectory() as directory:
            self.assertEqual(run.finish(Path(directory) / "demo.json"), 1)


if __name__ == "__main__":
    unittest.main()
