#!/usr/bin/env python3
"""Exact finite support for the sharp five-letter reduction of F_20.

The universal word factorization is proved algebraically in
``notes/f20_alphabetic_reduction.md`` section 13.  This script checks the
finite data of the construction: the sixteen letter maps, their images, the
section identity, the four erased alphabets, and load-bearing mutations.  It
does not infer a theorem from bounded word samples.
"""

from __future__ import annotations

import itertools
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.ci.f20_phase_rigidity import (  # noqa: E402
    ELEMENTS,
    IDENTITY,
    base,
    generated_subgroup,
)


PHASES = range(4)
THRESHOLDS = range(1, 5)


def phase_element(epsilon: int, beta: int) -> tuple[int, int]:
    return (base.POWERS_OF_TWO[epsilon], beta % 5)


def threshold(beta: int, level: int) -> int:
    """The ordinary representative beta in {0,...,4} crosses level or not."""

    return int(beta >= level)


def coordinate_map(
    distinguished_phase: int, level: int, g: tuple[int, int]
) -> tuple[int, int]:
    epsilon = base.EPSILON[g]
    beta = g[1]
    digit = threshold(beta, level) if epsilon == distinguished_phase else 0
    return phase_element(epsilon, digit)


def coordinate_alphabet(distinguished_phase: int) -> frozenset[tuple[int, int]]:
    return frozenset(
        phase_element(epsilon, 0) for epsilon in PHASES
    ) | {phase_element(distinguished_phase, 1)}


def letter_section(g: tuple[int, int]) -> tuple[tuple[int, int], ...]:
    return tuple(
        coordinate_map(r, level, g)
        for r in PHASES
        for level in THRESHOLDS
    )


def rho_equal_phase(vector: tuple[tuple[int, int], ...]) -> tuple[int, int]:
    phases = {base.EPSILON[x] for x in vector}
    if len(phases) != 1:
        raise ValueError("rho is defined here only on the equal-phase subgroup")
    epsilon = next(iter(phases))
    return phase_element(epsilon, sum(x[1] for x in vector) % 5)


def construction_audit() -> dict[str, object]:
    image_checks = []
    for r in PHASES:
        expected = coordinate_alphabet(r)
        for level in THRESHOLDS:
            actual = frozenset(coordinate_map(r, level, g) for g in ELEMENTS)
            image_checks.append(actual == expected and len(actual) == 5)

    section_checks = tuple(rho_equal_phase(letter_section(g)) == g for g in ELEMENTS)
    return {
        "coordinates": len(image_checks),
        "distinct_alphabets": len({coordinate_alphabet(r) for r in PHASES}),
        "all_images_exactly_five": all(image_checks),
        "letters_checked": len(section_checks),
        "section_on_all_letters": all(section_checks),
    }


def homomorphism_formula_audit() -> dict[str, object]:
    """Check the 400 scalar summaries of the arbitrary-vector rho calculation."""

    cases = tuple(itertools.product(PHASES, range(5), PHASES, range(5)))
    checks = []
    for epsilon, sum_u, epsilon_prime, sum_v in cases:
        lhs = phase_element(
            (epsilon + epsilon_prime) % 4,
            base.POWERS_OF_TWO[epsilon_prime] * sum_u + sum_v,
        )
        rhs = base.compose(
            phase_element(epsilon, sum_u), phase_element(epsilon_prime, sum_v)
        )
        checks.append(lhs == rhs)
    return {"scalar_summaries": len(cases), "all_hold": all(checks)}


def erased_alphabet_audit() -> dict[str, object]:
    erased = tuple(coordinate_alphabet(r) - {IDENTITY} for r in PHASES)
    generated_orders = tuple(len(generated_subgroup(alphabet)) for alphabet in erased)
    return {
        "alphabets": len(erased),
        "sizes": tuple(len(alphabet) for alphabet in erased),
        "generated_orders": generated_orders,
        "all_generate_f20": all(order == 20 for order in generated_orders),
    }


def control_audit() -> dict[str, bool]:
    # The last threshold is essential for beta=4 in every distinguished phase.
    missing_last = tuple(
        coordinate_map(r, level, phase_element(r, 4))
        for r in PHASES
        for level in range(1, 4)
    )
    missing_last_sum = {
        r: sum(x[1] for x in missing_last[3 * r : 3 * r + 3]) % 5
        for r in PHASES
    }

    # The old, nonlocalized threshold coordinate has two values in every phase,
    # hence eight images rather than the desired five.
    unlocalized_images = {
        phase_element(base.EPSILON[g], threshold(g[1], 1)) for g in ELEMENTS
    }

    # Mutating one coordinate value breaks the section on a concrete letter.
    witness = phase_element(0, 1)
    mutated = list(letter_section(witness))
    mutated[0] = phase_element(0, 0)

    return {
        "dropping_level_four_breaks_beta_four": all(
            missing_last_sum[r] != 4 for r in PHASES
        ),
        "unlocalized_threshold_has_eight_images": len(unlocalized_images) == 8,
        "one_value_mutation_breaks_section": rho_equal_phase(tuple(mutated)) != witness,
    }


def audit() -> dict[str, object]:
    return {
        "construction": construction_audit(),
        "homomorphism": homomorphism_formula_audit(),
        "erasure": erased_alphabet_audit(),
        "controls": control_audit(),
    }


def main() -> int:
    result = audit()
    expected = {
        "construction": {
            "coordinates": 16,
            "distinct_alphabets": 4,
            "all_images_exactly_five": True,
            "letters_checked": 20,
            "section_on_all_letters": True,
        },
        "homomorphism": {"scalar_summaries": 400, "all_hold": True},
        "erasure": {
            "alphabets": 4,
            "sizes": (4, 4, 4, 4),
            "generated_orders": (20, 20, 20, 20),
            "all_generate_f20": True,
        },
        "controls": {
            "dropping_level_four_breaks_beta_four": True,
            "unlocalized_threshold_has_eight_images": True,
            "one_value_mutation_breaks_section": True,
        },
    }
    if result != expected:
        print("F20 five-letter reduction support: FAIL")
        print(result)
        return 1
    print(
        "F20 five-letter reduction support: PASS; "
        "16 coordinates, 4 distinct five-letter alphabets, 20-letter section, "
        "400 homomorphism summaries"
    )
    print(
        "erasure: four generating four-letter obligations; "
        "all three load-bearing controls rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
