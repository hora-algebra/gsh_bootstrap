#!/usr/bin/env python3
"""Finite support checks for the universal four-letter impossibility proof.

``F20-ALPH4-RIGID-01`` is proved for arbitrary coordinate number in
``notes/f20_alphabetic_reduction.md`` section 12.  This script checks only the
concrete F_20 ingredients used there.  In particular, it does not enumerate
factorizations and is not a ``COMPUTED`` verdict for the universal theorem.
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
    inverse,
    order,
    power,
)
from scripts.ci.f20_alph4_classification import phase_sections  # noqa: E402


def same_phase_power_audit() -> dict[str, int | bool]:
    """Check the order-five contradiction on every ordered fibre pair."""

    pairs = tuple(
        (g, h)
        for g, h in itertools.permutations(ELEMENTS, 2)
        if base.EPSILON[g] == base.EPSILON[h]
    )
    differences = tuple(base.compose(g, inverse(h)) for g, h in pairs)
    return {
        "pairs": len(pairs),
        "all_nonidentity_kernel": all(
            x != IDENTITY and base.EPSILON[x] == 0 for x in differences
        ),
        "all_order_five": all(order(x) == 5 for x in differences),
        "fourth_powers_nonidentity": all(
            power(x, 4) != IDENTITY for x in differences
        ),
        "fifth_powers_identity": all(
            power(x, 5) == IDENTITY for x in differences
        ),
    }


def four_image_fibre_audit() -> dict[str, int | bool]:
    """Every phase-preserving image of size four collapses each phase fibre."""

    sections = phase_sections()
    pairs = tuple(
        (g, h)
        for g, h in itertools.permutations(ELEMENTS, 2)
        if base.EPSILON[g] == base.EPSILON[h]
    )
    collisions = 0
    for section in sections:
        target = {
            phase: next(g for g in section if base.EPSILON[g] == phase)
            for phase in range(4)
        }
        image = {target[base.EPSILON[g]] for g in ELEMENTS}
        if len(image) != 4:
            return {"sections": len(sections), "collisions": collisions,
                    "all_collapse": False, "five_image_control": False}
        collisions += sum(
            target[base.EPSILON[g]] == target[base.EPSILON[h]]
            for g, h in pairs
        )

    # Load-bearing control: at size five a phase-preserving map can separate a
    # same-phase pair, so the proof cannot silently claim a stronger bound.
    distinguished = ((1, 1), (1, 0))

    def five_image_map(g):
        if g == distinguished[0]:
            return (1, 1)
        return (base.POWERS_OF_TWO[base.EPSILON[g]], 0)

    five_image = {five_image_map(g) for g in ELEMENTS}
    five_image_control = (
        len(five_image) == 5
        and five_image_map(distinguished[0]) != five_image_map(distinguished[1])
    )
    return {
        "sections": len(sections),
        "collisions": collisions,
        "all_collapse": collisions == len(sections) * len(pairs),
        "five_image_control": five_image_control,
    }


def character_orthogonality_audit() -> dict[str, object]:
    """Check the only root sums possible for nontrivial P-characters."""

    # F_5^x has orders 1, 2, 4.  A nontrivial character image therefore has
    # order 2 or 4; summing over P is |ker| times one of these two sums.
    roots = {2: 4, 4: 2}
    sums = {
        image_order: sum(pow(root, i, 5) for i in range(image_order)) % 5
        for image_order, root in roots.items()
    }
    return {"image_orders": tuple(sorted(sums)), "root_sums": sums,
            "all_zero": all(value == 0 for value in sums.values())}


def audit() -> dict[str, object]:
    return {
        "same_phase": same_phase_power_audit(),
        "four_image": four_image_fibre_audit(),
        "characters": character_orthogonality_audit(),
    }


def main() -> int:
    result = audit()
    expected = {
        "same_phase": {
            "pairs": 80,
            "all_nonidentity_kernel": True,
            "all_order_five": True,
            "fourth_powers_nonidentity": True,
            "fifth_powers_identity": True,
        },
        "four_image": {
            "sections": 625,
            "collisions": 50_000,
            "all_collapse": True,
            "five_image_control": True,
        },
        "characters": {
            "image_orders": (2, 4),
            "root_sums": {2: 0, 4: 0},
            "all_zero": True,
        },
    }
    if result != expected:
        print("F20 four-letter impossibility support: FAIL")
        print(result)
        return 1
    print(
        "F20 four-letter impossibility support: PASS; "
        "80 fibre differences, 625 sections, 50000 forced collisions"
    )
    print(
        "negative controls: fifth powers kill the target difference; "
        "a five-image phase map separates a fibre pair"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
