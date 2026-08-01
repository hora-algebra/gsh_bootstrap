#!/usr/bin/env python3
"""Finite checks supporting the F_20 phase-rigidity argument.

The general statement ``F20-PHASE-RIGID-01`` is proved by the Maschke
argument in ``notes/f20_alphabetic_reduction.md``.  This script does not claim
to decide that theorem by finite sampling.  It checks the concrete action and
its phase-only negative control, and it decides the separate finite claim
``F20-GENPAIR-AUDIT-01`` exactly.
"""

from __future__ import annotations

import itertools
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.research import f20_full_alphabet as base  # noqa: E402
from tools.verdict import Control, Run, exhaustive  # noqa: E402


RUN = Run("scripts/ci/f20_phase_rigidity.py")
ELEMENTS = base.SIGMA
IDENTITY = base.IDENTITY
STANDARD_A = (1, 1)  # phase 0, translation 1, order 5
STANDARD_B = (2, 0)  # phase 1, translation 0, order 4


def power(x, exponent: int):
    out = IDENTITY
    for _ in range(exponent):
        out = base.compose(out, x)
    return out


def inverse(x):
    return next(
        y
        for y in ELEMENTS
        if base.compose(x, y) == IDENTITY and base.compose(y, x) == IDENTITY
    )


def order(x) -> int:
    return next(n for n in range(1, 21) if power(x, n) == IDENTITY)


def generated_subgroup(generators) -> frozenset:
    generators = tuple(generators)
    reached = {IDENTITY}
    frontier = [IDENTITY]
    while frontier:
        x = frontier.pop()
        for y in generators:
            z = base.compose(x, y)
            if z not in reached:
                reached.add(z)
                frontier.append(z)
    return frozenset(reached)


def check_conjugation_action() -> tuple[bool, int, str]:
    """Check the C_4-character on N=C_5 in the repository convention."""

    checked = 0
    failures = []
    translations = tuple(g for g in ELEMENTS if base.EPSILON[g] == 0)
    for h in ELEMENTS:
        scale = pow(2, -base.EPSILON[h], 5)
        for u in translations:
            checked += 1
            actual = base.compose(base.compose(h, u), inverse(h))
            expected = (1, scale * u[1] % 5)
            if actual != expected:
                failures.append((h, u, actual, expected))
    return (
        not failures,
        checked,
        "conjugation is u -> 2^(-phase)u on all F_20 x C_5 pairs"
        if not failures
        else f"first failure: {failures[0]}",
    )


def check_phase_only_binary_control(*, coefficient: int = 2) -> tuple[bool, int, str]:
    """The quotient C_4 alone can be recovered from two binary-image maps."""

    q = lambda x, y: (x + coefficient * y) % 4
    hom = all(
        q((x + xp) % 4, (y + yp) % 4)
        == (q(x, y) + q(xp, yp)) % 4
        for x, y, xp, yp in itertools.product(range(4), repeat=4)
    )
    recovered = all(q(e % 2, e // 2) == e for e in range(4))
    return (
        hom and recovered,
        4**4 + 4,
        "q(x,y)=x+2y recovers all four phases from two binary images"
        if hom and recovered
        else "the proposed phase-only recovery fails",
    )


def generating_pair_audit() -> dict:
    """Exhaust all two-element subsets and all possible generator images."""

    two_subsets = tuple(itertools.combinations(ELEMENTS, 2))
    generating = tuple(
        frozenset(pair)
        for pair in two_subsets
        if len(generated_subgroup(pair)) == len(ELEMENTS)
    )

    profiles: dict[tuple[int, int], int] = {}
    for pair in generating:
        profile = tuple(sorted(order(x) for x in pair))
        profiles[profile] = profiles.get(profile, 0) + 1

    order_five = tuple(x for x in ELEMENTS if order(x) == 5)
    order_four = tuple(x for x in ELEMENTS if order(x) == 4)
    candidate_image_pairs = tuple(itertools.product(order_five, order_four))
    automorphisms = []
    for image_a, image_b in candidate_image_pairs:
        mapping = {
            g: base.compose(
                power(image_b, base.EPSILON[g]), power(image_a, g[1])
            )
            for g in ELEMENTS
        }
        is_hom = all(
            mapping[base.compose(x, y)]
            == base.compose(mapping[x], mapping[y])
            for x in ELEMENTS
            for y in ELEMENTS
        )
        if is_hom and len(set(mapping.values())) == len(ELEMENTS):
            automorphisms.append(mapping)

    standard_orbit = {
        frozenset((mapping[STANDARD_A], mapping[STANDARD_B]))
        for mapping in automorphisms
    }
    return {
        "two_subsets": len(two_subsets),
        "generating": len(generating),
        "profiles": profiles,
        "candidate_image_pairs": len(candidate_image_pairs),
        "automorphisms": len(automorphisms),
        "standard_orbit": len(standard_orbit),
        "uncovered": len(set(generating) - standard_orbit),
    }


def main() -> int:
    action_ok, action_pairs, action_detail = check_conjugation_action()
    phase_ok, phase_cases, phase_detail = check_phase_only_binary_control()
    mutated_phase_ok, _, _ = check_phase_only_binary_control(coefficient=1)
    if not action_ok or not phase_ok or mutated_phase_ok:
        print(action_detail)
        print(phase_detail)
        return 1

    audit = generating_pair_audit()
    expected_profiles = {(4, 5): 40, (4, 4): 40, (2, 4): 40}
    passed = (
        audit["two_subsets"] == 190
        and audit["generating"] == 120
        and audit["profiles"] == expected_profiles
        and audit["candidate_image_pairs"] == 40
        and audit["automorphisms"] == 20
        and audit["standard_orbit"] == 20
        and audit["uncovered"] == 100
    )
    RUN.add(
        exhaustive(
            "F_20 generating-pair and standard-orbit audit",
            "F20-GENPAIR-AUDIT-01",
            passed=passed,
            universe=audit["two_subsets"] + audit["candidate_image_pairs"],
            detail=(
                "190 two-subsets give 120 generating pairs with profiles "
                "(4,5)/(4,4)/(2,4) = 40/40/40; all 40 possible images of "
                "the standard generators give exactly 20 automorphisms and a "
                "20-pair orbit, leaving 100 generating pairs outside it"
            ),
            covers="claim",
            rationale=(
                "the claim consists exactly of the complete two-subset generation "
                "classification and the complete standard-generator image audit"
            ),
            controls=[
                Control(
                    "drop generation test",
                    "treat all two-element subsets as generating",
                    rejected=audit["two_subsets"] != audit["generating"],
                ),
                Control(
                    "drop homomorphism test",
                    "treat every order-compatible generator image pair as an automorphism",
                    rejected=audit["candidate_image_pairs"] != audit["automorphisms"],
                ),
                Control(
                    "inflate standard orbit",
                    "identify the standard orbit with all (4,5)-profile generating pairs",
                    rejected=audit["standard_orbit"] != expected_profiles[(4, 5)],
                ),
            ],
        )
    )
    print(f"support check: {action_detail} ({action_pairs} pairs)")
    print(f"negative control: {phase_detail} ({phase_cases} cases)")
    return RUN.finish()


if __name__ == "__main__":
    raise SystemExit(main())
