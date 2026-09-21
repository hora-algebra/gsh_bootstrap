#!/usr/bin/env python3
"""Exact support for equivalences among the four F_20 Gamma_r alphabets.

The structural theorem is proved in ``notes/f20_alphabetic_reduction.md``
section 14.  This script decides the finite language comparisons by complete
reachability in products of the two 20-state group automata.  It never uses a
word-length cutoff.
"""

from __future__ import annotations

from collections import deque
import itertools
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.ci.f20_alph5_reduction import phase_element  # noqa: E402
from scripts.ci.f20_phase_rigidity import (  # noqa: E402
    ELEMENTS,
    IDENTITY,
    base,
    inverse,
)


PHASES = range(4)
COMPLEMENT_TRANSLATIONS = (0, 1, 3, 2)


def gamma(r: int) -> tuple[tuple[int, int], ...]:
    letters = {phase_element(epsilon, 0) for epsilon in range(1, 4)}
    letters.add(phase_element(r, 1))
    return tuple(sorted(letters, key=lambda g: (base.EPSILON[g], g[1])))


def all_letter_maps(r: int, s: int):
    source = gamma(r)
    target = gamma(s)
    for images in itertools.product(target, repeat=len(source)):
        yield dict(zip(source, images, strict=True))


def kernel_equivalent(
    r: int,
    s: int,
    mapping: dict[tuple[int, int], tuple[int, int]],
    *,
    reverse_target: bool = False,
) -> tuple[bool, tuple[tuple[int, int], ...] | None, int]:
    """Decide identity-kernel equality on every word by product reachability."""

    start = (IDENTITY, IDENTITY)
    queue = deque([start])
    seen = {start}
    witness: dict[
        tuple[tuple[int, int], tuple[int, int]], tuple[tuple[int, int], ...]
    ] = {start: ()}
    first_mismatch = None
    while queue:
        left, right = queue.popleft()
        word = witness[(left, right)]
        if first_mismatch is None and (left == IDENTITY) != (right == IDENTITY):
            first_mismatch = word
        for letter in gamma(r):
            next_left = base.compose(left, letter)
            if reverse_target:
                next_right = base.compose(mapping[letter], right)
            else:
                next_right = base.compose(right, mapping[letter])
            state = (next_left, next_right)
            if state not in seen:
                seen.add(state)
                witness[state] = word + (letter,)
                queue.append(state)
    return first_mismatch is None, first_mismatch, len(seen)


def automorphism(scale: int, shift: int, g: tuple[int, int]) -> tuple[int, int]:
    epsilon = base.EPSILON[g]
    beta = (scale * g[1] + shift * COMPLEMENT_TRANSLATIONS[epsilon]) % 5
    return phase_element(epsilon, beta)


def anti_automorphism(
    scale: int, shift: int, g: tuple[int, int]
) -> tuple[int, int]:
    return automorphism(scale, shift, inverse(g))


def structural_signatures() -> dict[str, tuple[tuple[object, ...], ...]]:
    auto_signatures = set()
    anti_signatures = set()
    for r, s in itertools.product(PHASES, repeat=2):
        target = set(gamma(s))
        for scale, shift in itertools.product(range(1, 5), range(5)):
            auto_images = tuple(automorphism(scale, shift, g) for g in gamma(r))
            anti_images = tuple(
                anti_automorphism(scale, shift, g) for g in gamma(r)
            )
            if set(auto_images) == target:
                auto_signatures.add((r, s, auto_images))
            if set(anti_images) == target:
                anti_signatures.add((r, s, anti_images))
    return {
        "automorphism": tuple(sorted(auto_signatures)),
        "anti_automorphism": tuple(sorted(anti_signatures)),
    }


def structural_image_matrices() -> dict[str, object]:
    auto = [[0 for _ in PHASES] for _ in PHASES]
    anti = [[0 for _ in PHASES] for _ in PHASES]
    for r, s in itertools.product(PHASES, repeat=2):
        target = set(gamma(s))
        for scale, shift in itertools.product(range(1, 5), range(5)):
            if {automorphism(scale, shift, g) for g in gamma(r)} == target:
                auto[r][s] += 1
            if {anti_automorphism(scale, shift, g) for g in gamma(r)} == target:
                anti[r][s] += 1

    auto_maps = tuple(
        tuple(automorphism(scale, shift, g) for g in ELEMENTS)
        for scale, shift in itertools.product(range(1, 5), range(5))
    )
    anti_maps = tuple(
        tuple(anti_automorphism(scale, shift, g) for g in ELEMENTS)
        for scale, shift in itertools.product(range(1, 5), range(5))
    )
    auto_laws = all(
        automorphism(scale, shift, base.compose(x, y))
        == base.compose(
            automorphism(scale, shift, x), automorphism(scale, shift, y)
        )
        for scale, shift in itertools.product(range(1, 5), range(5))
        for x, y in itertools.product(ELEMENTS, repeat=2)
    )
    anti_laws = all(
        anti_automorphism(scale, shift, base.compose(x, y))
        == base.compose(
            anti_automorphism(scale, shift, y),
            anti_automorphism(scale, shift, x),
        )
        for scale, shift in itertools.product(range(1, 5), range(5))
        for x, y in itertools.product(ELEMENTS, repeat=2)
    )
    return {
        "automorphism": tuple(tuple(row) for row in auto),
        "anti_automorphism": tuple(tuple(row) for row in anti),
        "automorphisms": len(auto_maps),
        "anti_automorphisms": len(anti_maps),
        "all_distinct": len(set(auto_maps)) == 20 and len(set(anti_maps)) == 20,
        "all_bijective": all(len(set(mapping)) == 20 for mapping in auto_maps + anti_maps),
        "hom_and_anti_laws": auto_laws and anti_laws,
    }


def exact_language_matrices() -> dict[str, object]:
    direct = [[0 for _ in PHASES] for _ in PHASES]
    reversed_matrix = [[0 for _ in PHASES] for _ in PHASES]
    maps_checked = 0
    largest_reachable = 0
    direct_states = 0
    reversed_states = 0
    direct_witness_lengths: dict[int, int] = {}
    reversed_witness_lengths: dict[int, int] = {}
    accepted_direct = set()
    accepted_reversed = set()
    for r, s in itertools.product(PHASES, repeat=2):
        for mapping in all_letter_maps(r, s):
            maps_checked += 1
            ok, witness, states = kernel_equivalent(r, s, mapping)
            largest_reachable = max(largest_reachable, states)
            direct_states += states
            direct[r][s] += int(ok)
            signature = (r, s, tuple(mapping[g] for g in gamma(r)))
            if ok:
                accepted_direct.add(signature)
            else:
                length = len(witness or ())
                direct_witness_lengths[length] = direct_witness_lengths.get(length, 0) + 1

            ok_rev, witness_rev, states_rev = kernel_equivalent(
                r, s, mapping, reverse_target=True
            )
            largest_reachable = max(largest_reachable, states_rev)
            reversed_states += states_rev
            reversed_matrix[r][s] += int(ok_rev)
            if ok_rev:
                accepted_reversed.add(signature)
            else:
                length = len(witness_rev or ())
                reversed_witness_lengths[length] = (
                    reversed_witness_lengths.get(length, 0) + 1
                )

    structural = structural_signatures()

    return {
        "maps_checked_each_mode": maps_checked,
        "direct": tuple(tuple(row) for row in direct),
        "reversed": tuple(tuple(row) for row in reversed_matrix),
        "largest_reachable_product": largest_reachable,
        "reachable_states_each_mode": (direct_states, reversed_states),
        "transitions_each_mode": (4 * direct_states, 4 * reversed_states),
        "direct_witness_lengths": direct_witness_lengths,
        "reversed_witness_lengths": reversed_witness_lengths,
        "accepted_maps_match_structure": (
            tuple(sorted(accepted_direct)) == structural["automorphism"]
            and tuple(sorted(accepted_reversed)) == structural["anti_automorphism"]
        ),
    }


def length_six_control_audit() -> dict[str, object]:
    word = tuple(
        phase_element(epsilon, beta)
        for epsilon, beta in ((1, 0), (2, 1), (3, 0), (2, 1), (2, 0), (2, 1))
    )
    anti_map = {g: anti_automorphism(1, 0, g) for g in gamma(2)}
    identity_map = {g: g for g in gamma(2)}

    source = IDENTITY
    direct_target = IDENTITY
    reversed_target = IDENTITY
    for letter in word:
        source = base.compose(source, letter)
        direct_target = base.compose(direct_target, anti_map[letter])
        reversed_target = base.compose(identity_map[letter], reversed_target)

    direct_ok, direct_witness, _ = kernel_equivalent(2, 2, anti_map)
    reversed_ok, reversed_witness, _ = kernel_equivalent(
        2, 2, identity_map, reverse_target=True
    )
    return {
        "length": len(word),
        "source_nonidentity": source != IDENTITY,
        "direct_target_identity": direct_target == IDENTITY,
        "reversed_target_identity": reversed_target == IDENTITY,
        "direct_shortest_length": len(direct_witness or ()),
        "reversed_shortest_length": len(reversed_witness or ()),
        "both_mutations_rejected": not direct_ok and not reversed_ok,
    }


def fixed_context_audit() -> dict[str, object]:
    contexts = 0
    empty_rejected = 0
    identity_contexts = 0
    all_identity_contexts_are_conjugation = True
    for prefix, suffix in itertools.product(ELEMENTS, repeat=2):
        contexts += 1
        if base.compose(prefix, suffix) != IDENTITY:
            empty_rejected += 1
            continue
        identity_contexts += 1
        for x in ELEMENTS:
            accepts = base.compose(base.compose(prefix, x), suffix) == IDENTITY
            if accepts != (x == IDENTITY):
                all_identity_contexts_are_conjugation = False
    return {
        "contexts": contexts,
        "empty_rejected": empty_rejected,
        "identity_contexts": identity_contexts,
        "all_identity_contexts_are_conjugation": (
            all_identity_contexts_are_conjugation
        ),
    }


def audit() -> dict[str, object]:
    return {
        "structural": structural_image_matrices(),
        "languages": exact_language_matrices(),
        "length_six_control": length_six_control_audit(),
        "contexts": fixed_context_audit(),
    }


def main() -> int:
    result = audit()
    expected = {
        "structural": {
            "automorphism": (
                (1, 0, 0, 0),
                (0, 1, 0, 0),
                (0, 0, 1, 0),
                (0, 0, 0, 1),
            ),
            "anti_automorphism": (
                (1, 0, 0, 0),
                (0, 0, 0, 1),
                (0, 0, 1, 0),
                (0, 1, 0, 0),
            ),
            "automorphisms": 20,
            "anti_automorphisms": 20,
            "all_distinct": True,
            "all_bijective": True,
            "hom_and_anti_laws": True,
        },
        "languages": {
            "maps_checked_each_mode": 4096,
            "direct": (
                (1, 0, 0, 0),
                (0, 1, 0, 0),
                (0, 0, 1, 0),
                (0, 0, 0, 1),
            ),
            "reversed": (
                (1, 0, 0, 0),
                (0, 0, 0, 1),
                (0, 0, 1, 0),
                (0, 1, 0, 0),
            ),
            "largest_reachable_product": 400,
            "reachable_states_each_mode": (1_152_000, 1_152_000),
            "transitions_each_mode": (4_608_000, 4_608_000),
            "direct_witness_lengths": {2: 4074, 3: 2, 4: 12, 5: 3, 6: 1},
            "reversed_witness_lengths": {2: 4074, 3: 2, 4: 12, 5: 3, 6: 1},
            "accepted_maps_match_structure": True,
        },
        "length_six_control": {
            "length": 6,
            "source_nonidentity": True,
            "direct_target_identity": True,
            "reversed_target_identity": True,
            "direct_shortest_length": 6,
            "reversed_shortest_length": 6,
            "both_mutations_rejected": True,
        },
        "contexts": {
            "contexts": 400,
            "empty_rejected": 380,
            "identity_contexts": 20,
            "all_identity_contexts_are_conjugation": True,
        },
    }
    if result != expected:
        print("F20 Gamma4 equivalence support: FAIL")
        print(result)
        return 1
    print(
        "F20 Gamma4 equivalence support: PASS; 4096 maps per mode, "
        "direct classes 0/1/2/3, reversal classes {0}/{1,3}/{2}"
    )
    print(
        "fixed contexts: 380 reject the empty word; "
        "20 inverse pairs preserve exactly the identity"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
