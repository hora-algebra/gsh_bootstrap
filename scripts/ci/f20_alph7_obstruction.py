#!/usr/bin/env python3
"""Exact audit of the old F_20 cut mechanism on its seven-letter reduction.

``F20-ALPH8-01`` reduces the full-alphabet obligation to

    Delta7 = {(epsilon, beta) : epsilon in Z/4, beta in {0,1}} - {(0,0)}.

The reduction note left open whether deleting the identity letter also deletes
the length-four obstruction to the pattern-conditioned cuts of
``F20-FULL-OBS-01``.  This script decides that finite, mechanism-scoped claim.
It does not decide ``HeightOneForGroup F_20`` and is not a height lower bound.
"""

from __future__ import annotations

import itertools
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.research import f20_subalphabet_obstruction as sub  # noqa: E402
from tools.verdict import Control, Run, conjunction, exhaustive  # noqa: E402

base = sub.base

DELTA8 = tuple(g for g in sub.FULL_SIGMA if g[1] in (0, 1))
DELTA7 = tuple(g for g in DELTA8 if g != base.IDENTITY)
TWO_GENERATOR = sub.TWO_GEN

K = (1, 1)       # epsilon=0, beta=1; replaces the erased identity endpoint
U0 = (2, 0)      # epsilon=1, beta=0
U1 = (2, 1)      # epsilon=1, beta=1
W0 = (K, U0, U1, K)
W1 = (K, U1, U0, K)

RUN = Run("scripts/ci/f20_alph7_obstruction.py")


def check_pattern_universe(sigma=DELTA7) -> tuple[bool, int, str]:
    """Decide every signature used by the base/single/pair cut family."""

    table = sub.certification_table(tuple(sigma))
    certified = [key for key, verdict in table.items() if verdict["aperiodic"]]
    ok = not certified
    detail = (
        f"all {len(table)} pattern signatures have a nontrivial period"
        if ok
        else f"{len(certified)} signature(s) are aperiodic: {certified[:3]}"
    )
    return ok, len(table), detail


def _feature_vector(word, *, include_letter_counts: bool = True) -> tuple[int, ...]:
    """The complete certified old-mechanism vector in both directions."""

    with sub.alphabet(DELTA7) as (sigma, nonmovers, _):
        table = sub.certification_table(sigma)
        pairs = sub.certified_pairs(sigma, table)

        def one_direction(current) -> tuple[int, ...]:
            data = base.certified_features(current)
            vector = [data.total_phase]
            vector.extend(data.base_cuts)
            vector.extend(
                data.nonmover_count(letter, q)
                for letter in nonmovers
                for q in range(base.PHASES)
            )
            vector.extend(
                data.pair_count(left, right, q)
                for left, right in pairs
                for q in range(base.PHASES)
            )
            if include_letter_counts:
                vector.extend(data.letter_counts.get(letter, 0) for letter in sigma)
            vector.append(sigma.index(data.first) if data.first is not None else -1)
            vector.append(sigma.index(data.last) if data.last is not None else -1)
            return tuple(vector)

        return one_direction(word) + one_direction(tuple(reversed(word)))


def check_collision_witness(*, force_same_word: bool = False) -> tuple[bool, int, str]:
    """Verify the explicit length-four feature collision and image separation."""

    right = W0 if force_same_word else W1
    left_features = _feature_vector(W0)
    right_features = _feature_vector(right)
    left_image = base.evaluate(W0)
    right_image = base.evaluate(right)
    left_coordinates = (base.EPSILON[left_image], left_image[1])
    right_coordinates = (base.EPSILON[right_image], right_image[1])
    ok = left_features == right_features and left_image != right_image
    detail = (
        f"{sub.show(W0)} and {sub.show(right)} agree in all "
        f"{len(left_features)} feature fields but map to epsilon/beta coordinates "
        f"{left_coordinates} and {right_coordinates}"
    )
    return ok, len(left_features), detail


def check_shortest_collision(
    *, include_letter_counts: bool = True
) -> tuple[bool, int, str]:
    """Exhaust every Delta7 word of length at most three.

    Together with ``check_collision_witness`` this proves that the displayed
    collision has minimum length four for the stated feature family.
    """

    seen = {}
    visited = 0
    first_collision = None
    for length in range(4):
        for word in itertools.product(DELTA7, repeat=length):
            visited += 1
            key = _feature_vector(word, include_letter_counts=include_letter_counts)
            image = base.evaluate(word)
            if key in seen and seen[key][1] != image:
                first_collision = (seen[key][0], word)
                break
            seen.setdefault(key, (word, image))
        if first_collision is not None:
            break
    ok = first_collision is None
    detail = (
        "no two words of length at most three with the full certified feature "
        "vector have different F_20 images"
        if ok
        else f"an earlier collision exists: {first_collision}"
    )
    return ok, visited, detail


def main() -> int:
    pattern_ok, signatures, pattern_detail = check_pattern_universe()
    control_pattern_ok, _, _ = check_pattern_universe(TWO_GENERATOR)
    patterns = RUN.add(
        exhaustive(
            "F_20 Delta7 cut-pattern aperiodicity audit",
            "F20-ALPH7-OBS-01",
            passed=pattern_ok,
            universe=signatures,
            detail=pattern_detail,
            controls=[
                Control(
                    "Delta7 -> two-generator alphabet",
                    "replace the seven-letter alphabet by the known positive "
                    "two-generator alphabet",
                    rejected=not control_pattern_ok,
                )
            ],
        )
    )

    witness_ok, fields, witness_detail = check_collision_witness()
    same_ok, _, _ = check_collision_witness(force_same_word=True)
    witness = RUN.add(
        exhaustive(
            "F_20 Delta7 explicit feature collision",
            "F20-ALPH7-OBS-01",
            passed=witness_ok,
            universe=fields,
            detail=witness_detail,
            controls=[
                Control(
                    "second witness word -> first witness word",
                    "replace the second word by the first, destroying image separation",
                    rejected=not same_ok,
                )
            ],
        )
    )

    shortest_ok, words, shortest_detail = check_shortest_collision()
    shortened_ok, _, _ = check_shortest_collision(include_letter_counts=False)
    shortest = RUN.add(
        exhaustive(
            "F_20 Delta7 shortest-collision audit",
            "F20-ALPH7-OBS-01",
            passed=shortest_ok,
            universe=words,
            detail=shortest_detail,
            controls=[
                Control(
                    "delete letter-count coordinates",
                    "remove the per-letter mod-5 counts from the certified feature family",
                    rejected=not shortened_ok,
                )
            ],
        )
    )

    RUN.add(
        conjunction(
            "F_20 seven-letter old-cut obstruction",
            "F20-ALPH7-OBS-01",
            parts=[patterns, witness, shortest],
            detail=(
                "identity erasure does not repair the old pattern-conditioned-cut "
                "mechanism on the seven-letter F_20 reduction"
            ),
            rationale=(
                "the claim consists exactly of the complete pattern-signature "
                "aperiodicity table, the explicit all-feature image collision, "
                "and its asserted minimum length"
            ),
        )
    )
    return RUN.finish()


if __name__ == "__main__":
    raise SystemExit(main())
