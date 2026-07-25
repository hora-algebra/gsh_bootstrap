#!/usr/bin/env python3
"""Exact reconstruction identity for the full 21-letter C_7:C_3 alphabet.

`C7C3-FULL-01` (RESULTS.md 5.14) established, by exhaustive checking up to
length 4 and a fixed-seed sweep, that the identity fibre of the full alphabet
of `C_7:C_3` is reconstructible from certified (star-free-token) cut counts.
That was `COMPUTED`.  This script replaces the sampling by a proof.

Two things change relative to `scripts/c7c3_full_alphabet.py`.

1. **A smaller certified family.**  The old scheme recovered, for a mover
   letter `g`, the count of occurrences of `g` not immediately preceded by `g`
   as a sum of 20 pair-conditioned cuts `("pair", h, g)`, `h != g`.  The single
   pattern

       ("anti", g):  at an arrival at phase q, skip the cut iff the letter is
                     g and the previous letter is not g

   computes that count directly, and section 1 certifies by exact transition-
   monoid enumeration that all 14 of them are aperiodic.  Likewise the six
   nonmover letters with `beta != 0` are handled by three *bit-set* patterns
   `("set", S)` instead of six single patterns, because
   `sum_g beta_g N_g = sum_k 2^k N_{S_k}` with `S_k` the letters whose k-th
   binary digit is set.  The family drops from 741 conditioned cuts to 63.

2. **A closed-form solution, hence a proof.**  Writing `x_p` for the number of
   occurrences of a mover `g` at *prefix* phase p and `n_a` for those at
   arrival phase a immediately preceded by `g`, the forward and backward rows
   of `RESULTS.md` 5.5 are `x_p - n_{p+eps}` and `x_p - n_{p+2 eps}`.  Solving
   `sum_p 2^p x_p = sum_p (cF_p F_p + cB_p B_p)` over GF(7) forces

       cF_p + cB_p = 2^p        and        cF_{p+eps} = cF_p - 2^p,

   a one-parameter family (section 2 checks it reproduces the particular
   solution that `scripts/c7c3_full_alphabet.py` obtained by elimination).
   The second relation telescopes:

       cF_p - cF_{p + m eps} = sum_{j<m} 2^{p + j eps},

   so for a maximal run of `g` of length L starting at prefix phase p,

       cF_p + cB_{p + (L-1) eps} = sum_{j<L} 2^{p + j eps},                (*)

   which is exactly that run's contribution to `beta`.  Summing (*) over all
   maximal runs of all letters proves the reconstruction identity for **every**
   word, with no length bound.  Note that both coefficients in (*) are indexed
   by *prefix* phases, so the total phase of the word does not appear.

Sections 3-5 verify the proof mechanically: the run-decomposition identity by
complete BFS over `(phase, previous letter, accumulator)`, its expression in
terms of the actual `CutPattern` counts by replay, and finally the statement

    mu(u) = e   <==>   phase(u) = 0  and  sum_j lambda_j c_j(u) = 0 mod 7

by complete BFS over `(group element, previous letter, accumulator)`.  Every
check is exhaustive over the reachable state space, not over sampled words.

This script does **not** yet build the height-one regular expression; that is
the remaining step of `N-C7C3-001`.  What it does establish is that the
arithmetic half of the argument is a theorem rather than an observation.

`scripts/c7c3_full_alphabet.py` is imported for the group, the DFA
minimizer and the transition-monoid enumerator, but its `CutPattern` only
knows the `single`/`pair` kinds, so the extended pattern semantics is
re-implemented here; section 1 checks the two agree on the old family.

Python standard library only.  Exit code 0 iff every check passes.
"""

from __future__ import annotations

import argparse
import itertools
import time
from collections import deque

import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from scripts.c7c3_full_alphabet import (  # noqa: E402
    EPSILON,
    IDENTITY,
    MODULUS,
    MOVERS,
    NONMOVERS,
    PHASES,
    POWERS_OF_TWO,
    SIGMA,
    CutPattern,
    all_words,
    candidate_patterns,
    compose,
    evaluate,
    letter_name,
    minimize_dfa,
    compose_transformation,
    objective_combination,
)

CONTRIBUTING_MOVERS = tuple(g for g in MOVERS if g[1] != 0)
CONTRIBUTING_NONMOVERS = tuple(g for g in NONMOVERS if g[1] != 0)
BITS = tuple(range((MODULUS - 1).bit_length()))  # 0, 1, 2: beta ranges over 1..6


def bit_set(bit):
    """Nonmover letters whose beta has the given binary digit set."""

    return frozenset(g for g in NONMOVERS if (g[1] >> bit) & 1)


BIT_SETS = tuple(bit_set(bit) for bit in BITS)
PHASE_OF_ALPHA = {alpha: phase for phase, alpha in enumerate(POWERS_OF_TWO)}


# ---------------- extended cut patterns ----------------


class Cut:
    """A q-entry cut with an extended skip condition.

    ``pattern`` is one of

      * ``None``                  -- never skip (the plain base cut);
      * ``("single", g)``         -- skip iff the letter is g;
      * ``("pair", h, g)``        -- skip iff the previous letter is h and the
                                     letter is g;
      * ``("anti", g)``           -- skip iff the letter is g and the previous
                                     letter is not g;
      * ``("set", S)``            -- skip iff the letter lies in S;
      * ``("antiset", S)``        -- skip iff the letter lies in S and the
                                     previous letter differs from it.

    The first three reproduce ``scripts/c7c3_full_alphabet.CutPattern``; the
    last three are new.  ``antiset`` is retained only as a negative control:
    section 1 shows it is *not* aperiodic.
    """

    def __init__(self, q, pattern):
        self.q = q
        self.pattern = pattern

    def matches(self, previous, letter) -> bool:
        pattern = self.pattern
        if pattern is None:
            return False
        kind = pattern[0]
        if kind == "single":
            return letter == pattern[1]
        if kind == "anti":
            return letter == pattern[1] and previous != letter
        if kind == "set":
            return letter in pattern[1]
        if kind == "antiset":
            return letter in pattern[1] and previous != letter
        return previous == pattern[1] and letter == pattern[2]

    def run(self, word) -> int:
        residue = 0
        phase = 0
        previous = None
        for letter in word:
            phase = (phase + EPSILON[letter]) % PHASES
            if phase == self.q:
                if self.matches(previous, letter):
                    previous = letter
                else:
                    residue = (residue + 1) % MODULUS
                    previous = None
            else:
                previous = letter
        return residue


def token_dfa(pattern):
    """Token language of the cut: post-cut state to the next cut, at q = 0."""

    accept = ("accept",)
    dead = ("dead",)
    start = (0, None)
    transitions = {}
    seen = {start, accept, dead}
    queue = deque([start])
    cut = Cut(0, pattern)
    for state in (accept, dead):
        for letter in SIGMA:
            transitions[state, letter] = dead
    while queue:
        phase, previous = queue.popleft()
        for letter in SIGMA:
            next_phase = (phase + EPSILON[letter]) % PHASES
            if next_phase == 0:
                next_state = (
                    (next_phase, letter) if cut.matches(previous, letter) else accept
                )
            else:
                next_state = (next_phase, letter)
            transitions[(phase, previous), letter] = next_state
            if next_state not in seen:
                seen.add(next_state)
                queue.append(next_state)
    return tuple(sorted(seen, key=repr)), transitions, start, {accept}


def aperiodicity(pattern):
    """Exact: minimize, enumerate the transition monoid, test every element."""

    states, transitions, start, accepting = token_dfa(pattern)
    states, transitions, _, _ = minimize_dfa(states, transitions, start, accepting)
    generators = {}
    for letter in SIGMA:
        transformation = tuple(transitions[state, letter] for state in states)
        generators.setdefault(transformation, letter_name(letter))
    identity = tuple(states)
    representatives = {identity: "epsilon"}
    queue = deque([identity])
    generator_items = tuple(generators.items())
    while queue:
        current = queue.popleft()
        current_word = representatives[current]
        for generator, name in generator_items:
            product = compose_transformation(current, generator)
            if product not in representatives:
                representatives[product] = (
                    name if current_word == "epsilon" else f"{current_word} {name}"
                )
                queue.append(product)
    for transformation, word in representatives.items():
        seen = {}
        power = transformation
        exponent = 1
        while power not in seen:
            seen[power] = exponent
            power = compose_transformation(power, transformation)
            exponent += 1
        period = exponent - seen[power]
        if period != 1:
            return {
                "aperiodic": False,
                "states": len(states),
                "monoid": len(representatives),
                "period": period,
                "witness": word,
            }
    return {
        "aperiodic": True,
        "states": len(states),
        "monoid": len(representatives),
        "period": 1,
        "witness": None,
    }


def signature(pattern):
    """Patterns with the same signature have isomorphic token automata."""

    if pattern is None:
        return ("base",)
    kind = pattern[0]
    if kind in ("single", "anti"):
        return (kind, EPSILON[pattern[1]])
    if kind in ("set", "antiset"):
        return (kind, tuple(sorted(EPSILON[g] for g in pattern[1])))
    return ("pair", EPSILON[pattern[1]], EPSILON[pattern[2]], pattern[1] == pattern[2])


# ---------------- the closed-form coefficients ----------------


def coefficients(epsilon, free=0):
    """``(cF, cB)`` with ``sum_p 2^p x_p = sum_p cF_p F_p + cB_p B_p``.

    Derived, not solved: ``cF_p + cB_p = 2^p`` kills the ``x_p`` columns and
    ``cF_p + cB_{p-eps} = 0`` kills the ``n_a`` columns; eliminating cB gives
    ``cF_{p+eps} = cF_p - 2^p``.  ``free`` is the one degree of freedom, the
    value of ``cF_0``.
    """

    if epsilon % PHASES == 0:
        raise ValueError("coefficients are for mover letters only")
    forward = [None] * PHASES
    forward[0] = free % MODULUS
    phase = 0
    for _ in range(PHASES - 1):
        nxt = (phase + epsilon) % PHASES
        forward[nxt] = (forward[phase] - POWERS_OF_TWO[phase]) % MODULUS
        phase = nxt
    # closing the cycle must return the free parameter: 2^0+2^1+2^2 = 7 = 0
    closing = (forward[phase] - POWERS_OF_TWO[phase]) % MODULUS
    if closing != forward[0]:
        raise AssertionError(f"the cF recursion does not close: {closing} != {free}")
    backward = [
        (POWERS_OF_TWO[phase] - forward[phase]) % MODULUS for phase in range(PHASES)
    ]
    return tuple(forward), tuple(backward)


def run_contribution(epsilon, start_phase, length):
    """Left-hand side of (*): what the certified rows award a maximal run."""

    forward, backward = COEFFICIENTS[epsilon]
    end_phase = (start_phase + (length - 1) * epsilon) % PHASES
    return (forward[start_phase] + backward[end_phase]) % MODULUS


def run_truth(epsilon, start_phase, length):
    """Right-hand side of (*): the run's actual contribution to beta."""

    return sum(
        POWERS_OF_TWO[(start_phase + j * epsilon) % PHASES] for j in range(length)
    ) % MODULUS


COEFFICIENTS = {epsilon: coefficients(epsilon) for epsilon in (1, 2)}


# ---------------- the local weight delta ----------------
#
# For a position i of u, write p_i for its prefix phase.  The reconstruction
# awards it
#
#   nonmover g              : beta_g * 2^{p_i}                (exact already)
#   mover g, beta_g != 0    : beta_g * ( cF_{p_i} [u_{i-1} != g] +
#                                        cB_{p_i} [u_{i+1} != g] )
#
# with the conventions [u_0 != g] = [u_{n+1} != g] = 1.  Summing over a maximal
# run of g of length L starting at prefix phase p leaves cF_p + cB_{p+(L-1)eps},
# which is (*): the run's true contribution to beta.  ``delta_step`` below
# emits the part of this that is knowable on reading the letter, and
# ``delta_correction`` repays the cB term when the next letter turns out to
# repeat, which is what makes a single left-to-right pass exact.


def gamma_step(phase, letter):
    """The true contribution of a letter read at prefix phase ``phase``."""

    return letter[1] * POWERS_OF_TWO[phase] % MODULUS


def delta_step(phase, previous, letter):
    """Reconstruction weight of the letter, assuming it is not repeated next."""

    beta = letter[1]
    if beta == 0:
        return 0
    epsilon = EPSILON[letter]
    if epsilon == 0:
        return beta * POWERS_OF_TWO[phase] % MODULUS
    forward, backward = COEFFICIENTS[epsilon]
    weight = backward[phase]
    if previous != letter:
        weight += forward[phase]
    return beta * weight % MODULUS


def delta_correction(phase, previous, letter):
    """Repayment when the letter repeats the previous one.

    ``phase`` is the prefix phase of the *current* letter, so the previous
    occurrence sat at ``phase - eps``.
    """

    if previous != letter or letter[1] == 0:
        return 0
    epsilon = EPSILON[letter]
    if epsilon == 0:
        return 0
    _, backward = COEFFICIENTS[epsilon]
    return letter[1] * backward[(phase - epsilon) % PHASES] % MODULUS


def delta_total(word):
    """Sum of the local weights over a word (one left-to-right pass)."""

    total = 0
    phase = 0
    previous = None
    for letter in word:
        total = (
            total + delta_step(phase, previous, letter)
            - delta_correction(phase, previous, letter)
        ) % MODULUS
        phase = (phase + EPSILON[letter]) % PHASES
        previous = letter
    return total


def beta_prefix(word):
    """``sum_i beta_i 2^{p_i}``, the prefix-frame coordinate."""

    total = 0
    phase = 0
    for letter in word:
        total = (total + letter[1] * POWERS_OF_TWO[phase]) % MODULUS
        phase = (phase + EPSILON[letter]) % PHASES
    return total


def total_phase(word):
    return sum(EPSILON[letter] for letter in word) % PHASES


# ---------------- complete state-space proofs ----------------


def prove_local_identity():
    """``beta_prefix(u) = delta_total(u)`` for EVERY word, by complete BFS.

    The state is ``(prefix phase, previous letter, gamma - delta so far)``.
    Every reachable state is an end-of-word state, so the identity holds for
    all words iff the accumulator is zero in every reachable state.  This is a
    finite exhaustive proof, not a sample: 3 * 22 * 7 states.
    """

    start = (0, None, 0)
    seen = {start: ""}
    queue = deque([start])
    while queue:
        phase, previous, accumulator = state = queue.popleft()
        if accumulator != 0:
            return {"proved": False, "state": state, "witness": seen[state]}
        for letter in SIGMA:
            step = (
                gamma_step(phase, letter)
                - delta_step(phase, previous, letter)
                + delta_correction(phase, previous, letter)
            ) % MODULUS
            successor = (
                (phase + EPSILON[letter]) % PHASES,
                letter,
                (accumulator + step) % MODULUS,
            )
            if successor not in seen:
                seen[successor] = seen[state] + letter_name(letter) + " "
                queue.append(successor)
    return {"proved": True, "states": len(seen)}


def prove_fibre():
    """``nu(u) = e  <==>  phase(u) = 0 and delta_total(u) = 0``, by BFS.

    ``nu(u) = mu(reverse(u))`` is the product of the letters taken right to
    left, so that ``nu``'s C_7 coordinate is the *prefix*-frame ``beta_prefix``
    that sections 3 and 4 reconstruct.  Reversal is a bijection of Sigma* that
    preserves generalized star-height, and ``nu`` is the morphism into the
    opposite group, which is isomorphic to ``C_7:C_3``; so a height-one bound
    for the ``nu``-fibre is a height-one bound for the ``mu``-fibre.

    The state is ``(group element, previous letter, delta so far)``; the phase
    is a function of the group element, so it is not tracked separately.  As
    above every reachable state is an end-of-word state.  21 * 22 * 7 states.
    """

    start = (IDENTITY, None, 0)
    seen = {start: ""}
    queue = deque([start])
    while queue:
        element, previous, accumulator = state = queue.popleft()
        phase = PHASE_OF_ALPHA[element[0]]
        if (element == IDENTITY) != (phase == 0 and accumulator == 0):
            return {"proved": False, "state": state, "witness": seen[state]}
        for letter in SIGMA:
            step = (
                delta_step(phase, previous, letter)
                - delta_correction(phase, previous, letter)
            ) % MODULUS
            successor = (
                compose(letter, element),  # right-to-left product: nu, not mu
                letter,
                (accumulator + step) % MODULUS,
            )
            if successor not in seen:
                seen[successor] = seen[state] + letter_name(letter) + " "
                queue.append(successor)
    return {"proved": True, "states": len(seen)}


def prove_cut_count(pattern, q, target):
    """``base_cut[q] - cut(pattern, q) = sum_i target(phase_i, prev_i, u_i)``.

    Proved by complete BFS over ``(prefix phase, true previous letter, the
    base cut's own previous, the conditioned cut's own previous, difference)``.
    Carrying both cut machines' private ``previous`` values means the proof
    does not assume that a cut's reset of ``previous`` is harmless; it
    establishes it.
    """

    base = Cut(q, None)
    conditioned = Cut(q, pattern)
    start = (0, None, None, None, 0)
    seen = {start}
    queue = deque([start])
    while queue:
        phase, previous, base_previous, cut_previous, accumulator = state = (
            queue.popleft()
        )
        if accumulator != 0:
            return {"proved": False, "state": state}
        for letter in SIGMA:
            next_phase = (phase + EPSILON[letter]) % PHASES
            if next_phase == q:
                if base.matches(base_previous, letter):
                    base_step, next_base = 0, letter
                else:
                    base_step, next_base = 1, None
                if conditioned.matches(cut_previous, letter):
                    cut_step, next_cut = 0, letter
                else:
                    cut_step, next_cut = 1, None
            else:
                base_step, next_base = 0, letter
                cut_step, next_cut = 0, letter
            step = (base_step - cut_step - target(phase, previous, letter)) % MODULUS
            successor = (
                next_phase,
                letter,
                next_base,
                next_cut,
                (accumulator + step) % MODULUS,
            )
            if successor not in seen:
                seen.add(successor)
                queue.append(successor)
    return {"proved": True, "states": len(seen)}


def anti_target(letter_g, q):
    """Occurrences of ``letter_g`` at arrival phase q not preceded by itself."""

    def target(phase, previous, letter):
        if letter != letter_g:
            return 0
        if (phase + EPSILON[letter]) % PHASES != q:
            return 0
        return 0 if previous == letter_g else 1

    return target


def set_target(letters, q):
    """Occurrences of a letter of ``letters`` at arrival phase q."""

    def target(phase, previous, letter):
        if letter not in letters:
            return 0
        return 1 if (phase + EPSILON[letter]) % PHASES == q else 0

    return target


# ---------------- the atom family and the assembled combination ----------------
#
# Every atom below is a *cut count*: the number of cuts of one certified
# pattern, taken modulo 7.  Section 1 certifies each pattern's token language
# aperiodic, which is what makes the corresponding residue language have
# generalized star-height at most one.  The combination is written for words of
# total phase 0 only -- the only ones the identity fibre contains -- because
# that is what lets the backward atoms be indexed by ``-p`` instead of by
# ``P - p``.


def atom_family():
    """``(atoms, terms)``: the distinct cut counts and the GF(7) combination.

    An atom is ``(direction, q, pattern)`` with ``direction`` in
    ``{"forward", "backward"}``; a term is ``(coefficient, atom)``.
    """

    terms = []
    for phase in range(PHASES):
        for bit in BITS:
            weight = POWERS_OF_TWO[phase] * (1 << bit) % MODULUS
            if weight == 0:
                continue
            terms.append((weight, ("forward", phase, None)))
            terms.append((-weight % MODULUS, ("forward", phase, ("set", BIT_SETS[bit]))))
    for letter in CONTRIBUTING_MOVERS:
        epsilon = EPSILON[letter]
        forward, backward = COEFFICIENTS[epsilon]
        for phase in range(PHASES):
            weight = letter[1] * forward[phase] % MODULUS
            if weight:
                arrival = (phase + epsilon) % PHASES
                terms.append((weight, ("forward", arrival, None)))
                terms.append(
                    (-weight % MODULUS, ("forward", arrival, ("anti", letter)))
                )
            weight = letter[1] * backward[phase] % MODULUS
            if weight:
                arrival = (-phase) % PHASES
                terms.append((weight, ("backward", arrival, None)))
                terms.append(
                    (-weight % MODULUS, ("backward", arrival, ("anti", letter)))
                )
    collected = {}
    for coefficient, atom in terms:
        collected[atom] = (collected.get(atom, 0) + coefficient) % MODULUS
    reduced = tuple(
        sorted(
            ((coefficient, atom) for atom, coefficient in collected.items() if coefficient),
            key=lambda item: repr(item[1]),
        )
    )
    atoms = tuple(atom for _, atom in reduced)
    return atoms, reduced


ATOMS, TERMS = atom_family()


def atom_value(atom, word, reversed_word):
    direction, q, pattern = atom
    return Cut(q, pattern).run(word if direction == "forward" else reversed_word)


def combination_value(word):
    """The assembled GF(7) combination, from the actual cut counts."""

    reversed_word = tuple(reversed(word))
    return sum(
        coefficient * atom_value(atom, word, reversed_word)
        for coefficient, atom in TERMS
    ) % MODULUS


def fail(section, message):
    print(f"[{section}] FAIL: {message}")
    raise SystemExit(1)


# ---------------- sections ----------------


def section1(seed_words):
    """Certify the extended patterns, with the controls that must fail."""

    print("=== 1. aperiodicity of the extended cut patterns ===")

    for pattern in candidate_patterns():
        for q in range(PHASES):
            for word in seed_words:
                if Cut(q, pattern).run(word) != CutPattern(q, pattern).run(word):
                    fail(1, f"Cut disagrees with CutPattern on {pattern} q={q}")
    print(
        f"  the re-implemented Cut agrees with c7c3_full_alphabet.CutPattern on all "
        f"{len(candidate_patterns())} old patterns, all {PHASES} entries, "
        f"{len(seed_words)} words."
    )

    families = [
        ("anti(g), g a mover", [("anti", g) for g in MOVERS], True),
        ("set(S), S a nonmover bit set", [("set", S) for S in BIT_SETS], True),
        ("single(g), g a mover [control]", [("single", g) for g in MOVERS], False),
        (
            "antiset(S), S movers of one eps [control]",
            [
                ("antiset", frozenset(g for g in MOVERS
                                      if EPSILON[g] == epsilon and (g[1] >> bit) & 1))
                for epsilon in (1, 2)
                for bit in BITS
            ],
            False,
        ),
    ]
    cache = {}
    for label, patterns, expected in families:
        good = bad = 0
        example = None
        for pattern in patterns:
            key = signature(pattern)
            if key not in cache:
                cache[key] = aperiodicity(pattern)
            result = cache[key]
            if result["aperiodic"]:
                good += 1
            else:
                bad += 1
                if example is None:
                    example = result
        if expected and bad:
            fail(1, f"{label}: {bad} of {good + bad} are not aperiodic")
        if not expected and good:
            fail(1, f"{label}: {good} of {good + bad} are aperiodic, expected none")
        note = ""
        if example is not None:
            note = f" (period={example['period']}, witness={example['witness']})"
        print(f"  {label:44s} aperiodic {good}/{good + bad}{note}")
    print(
        "  the two control families are the reason the family had to be enlarged "
        "this way; the judge answers no when it should."
    )


def section2():
    """The closed-form coefficients and the run identity (*)."""

    print("=== 2. closed-form coefficients and the run identity ===")
    for epsilon in (1, 2):
        forward, backward = COEFFICIENTS[epsilon]
        for phase in range(PHASES):
            if (forward[phase] + backward[phase]) % MODULUS != POWERS_OF_TWO[phase]:
                fail(2, f"cF+cB != 2^p at eps={epsilon}, p={phase}")
            nxt = (phase + epsilon) % PHASES
            if (forward[nxt] - forward[phase] + POWERS_OF_TWO[phase]) % MODULUS:
                fail(2, f"the cF recursion fails at eps={epsilon}, p={phase}")
        for start in range(PHASES):
            for length in range(1, 3 * PHASES * 2 + 1):
                if run_contribution(epsilon, start, length) != run_truth(
                    epsilon, start, length
                ):
                    fail(
                        2,
                        f"(*) fails at eps={epsilon}, start={start}, length={length}",
                    )
        print(
            f"  eps={epsilon}: cF={forward}, cB={backward}; "
            f"(*) holds for all start phases and all run lengths 1..{3 * PHASES * 2}."
        )

    for epsilon in (1, 2):
        _, labels, solved = objective_combination(epsilon)
        if solved is None:
            fail(2, f"the reference elimination found no solution for eps={epsilon}")
        if solved[2 * PHASES] % MODULUS:
            fail(2, f"the reference solution uses the total-count row: {solved}")
        forward, backward = coefficients(epsilon, free=solved[0])
        if tuple(value % MODULUS for value in solved[:PHASES]) != forward or tuple(
            value % MODULUS for value in solved[PHASES : 2 * PHASES]
        ) != backward:
            fail(
                2,
                f"the closed form misses the reference solution for eps={epsilon}: "
                f"{solved} vs {forward}+{backward}",
            )
        printed = " + ".join(
            f"{value}*{name}"
            for value, name in zip(solved, labels)
            if value % MODULUS
        )
        print(
            f"  eps={epsilon}: the elimination of scripts/c7c3_full_alphabet.py "
            f"({printed}) is the member of the family with cF_0={solved[0]}."
        )


def section3():
    """Complete proof that the local weights reconstruct beta."""

    print("=== 3. the reconstruction identity, proved for every word ===")
    result = prove_local_identity()
    if not result["proved"]:
        fail(3, f"beta != delta at state {result['state']}, witness {result['witness']}")
    print(
        f"  PASS: beta_prefix(u) = delta_total(u) for EVERY word in Sigma*; "
        f"complete BFS over {result['states']} reachable "
        f"(phase, previous letter, accumulator) states."
    )


def section4():
    """Complete proof that each atom is the count it is used as."""

    print("=== 4. each certified cut equals the count it stands for ===")
    checked = 0
    for phase in range(PHASES):
        for bit in BITS:
            pattern = ("set", BIT_SETS[bit])
            result = prove_cut_count(pattern, phase, set_target(BIT_SETS[bit], phase))
            if not result["proved"]:
                fail(4, f"set atom bit={bit} q={phase} at state {result['state']}")
            checked += 1
    for letter in CONTRIBUTING_MOVERS:
        for phase in range(PHASES):
            pattern = ("anti", letter)
            result = prove_cut_count(pattern, phase, anti_target(letter, phase))
            if not result["proved"]:
                fail(
                    4,
                    f"anti atom {letter_name(letter)} q={phase} at "
                    f"state {result['state']}",
                )
            checked += 1
    print(
        f"  PASS: {checked} statements of the form "
        f"'base_cut[q] - conditioned_cut[q] = the intended count', each proved by "
        f"complete BFS carrying both cut machines' private previous-letter state."
    )
    print(
        "  applying the same statements to the reversed word gives the backward "
        "atoms, since a backward atom is by definition a forward cut of the reversal."
    )


def section5():
    """Complete proof of the fibre characterization."""

    print("=== 5. the identity fibre, proved for every word ===")
    result = prove_fibre()
    if not result["proved"]:
        fail(5, f"characterization fails at {result['state']}: {result['witness']}")
    print(
        f"  PASS: mu(u) = e  <==>  phase(u) = 0 and delta_total(u) = 0, for EVERY "
        f"word; complete BFS over {result['states']} reachable "
        f"(group element, previous letter, accumulator) states."
    )


def section6(exhaustive_length, sweep_words):
    """Tie the proved identity to the actual cut counts, numerically."""

    print("=== 6. end-to-end cross-check against the actual cut counts ===")
    print(f"  the family has {len(ATOMS)} distinct atoms and {len(TERMS)} terms.")
    checked = zero_phase = members = 0
    for word in all_words(exhaustive_length):
        checked += 1
        if total_phase(word) != 0:
            continue
        zero_phase += 1
        beta = beta_prefix(word)
        if delta_total(word) != beta:
            fail(6, f"delta_total != beta_prefix on {word}")
        if combination_value(word) != beta:
            fail(6, f"the assembled combination != beta_prefix on {word}")
        predicted = beta == 0
        actual = evaluate(tuple(reversed(word))) == IDENTITY
        if predicted != actual:
            fail(6, f"membership mismatch on {word}")
        members += int(actual)
    for word in sweep_words:
        if total_phase(word) != 0:
            continue
        if combination_value(word) != beta_prefix(word):
            fail(6, f"the assembled combination != beta_prefix on sweep word {word}")
    print(
        f"  PASS: on all {checked} words of length <= {exhaustive_length} "
        f"({zero_phase} of total phase 0, {members} in the fibre) the actual cut "
        f"counts reproduce beta, and on {len(sweep_words)} longer sweep words."
    )


def section7(exhaustive_length):
    """Negative controls.  Without these, sections 3-6 are unfalsifiable.

    A proof procedure that always answers yes produces exactly the output of
    sections 3-6.  Each control below perturbs one ingredient and demands that
    the same procedure then answers no.
    """

    print("=== 7. negative controls ===")

    global COEFFICIENTS
    original = COEFFICIENTS
    survivors = []
    mutations = 0
    try:
        for epsilon in (1, 2):
            forward, backward = original[epsilon]
            for index in range(PHASES):
                for which in ("cF", "cB"):
                    for delta in range(1, MODULUS):
                        mutated_f, mutated_b = list(forward), list(backward)
                        if which == "cF":
                            mutated_f[index] = (mutated_f[index] + delta) % MODULUS
                        else:
                            mutated_b[index] = (mutated_b[index] + delta) % MODULUS
                        COEFFICIENTS = dict(original)
                        COEFFICIENTS[epsilon] = (tuple(mutated_f), tuple(mutated_b))
                        mutations += 1
                        if prove_local_identity()["proved"]:
                            survivors.append((epsilon, which, index, delta))
    finally:
        COEFFICIENTS = original
    if survivors:
        fail(7, f"{len(survivors)} coefficient mutations still 'proved': {survivors[:4]}")
    print(
        f"  (a) all {mutations} single-coefficient perturbations of cF and cB make "
        f"the section-3 proof fail; 0 survive."
    )

    broken = 0
    for word in all_words(exhaustive_length):
        if total_phase(word) != 0:
            continue
        naive = 0
        phase = 0
        previous = None
        for letter in word:
            naive = (naive + delta_step(phase, previous, letter)) % MODULUS
            phase = (phase + EPSILON[letter]) % PHASES
            previous = letter
        if naive != beta_prefix(word):
            broken += 1
    if broken == 0:
        fail(
            7,
            "dropping the repeat correction never changes the answer, so the "
            "run-length bookkeeping of (*) would be untested",
        )
    print(
        f"  (b) dropping the repeat correction (pretending no letter is ever "
        f"followed by itself) breaks the reconstruction on {broken} words of "
        f"length <= {exhaustive_length}; the run bookkeeping is load-bearing."
    )

    perturbed = 0
    survived = 0
    for index in range(len(TERMS)):
        coefficient, atom = TERMS[index]
        mutated = list(TERMS)
        mutated[index] = ((coefficient + 1) % MODULUS, atom)
        perturbed += 1
        agrees = True
        for word in all_words(2):
            if total_phase(word) != 0:
                continue
            reversed_word = tuple(reversed(word))
            value = sum(
                factor * atom_value(item, word, reversed_word)
                for factor, item in mutated
            ) % MODULUS
            if value != beta_prefix(word):
                agrees = False
                break
        if agrees:
            survived += 1
    if survived:
        fail(7, f"{survived} of {perturbed} term perturbations still reproduce beta")
    print(
        f"  (c) all {perturbed} single-term perturbations of the assembled "
        f"combination break it already on words of length <= 2; 0 survive."
    )

    total = fibre = 0
    for word in all_words(exhaustive_length):
        total += 1
        fibre += int(evaluate(tuple(reversed(word))) == IDENTITY)
    print(
        f"  (d) membership base rate {fibre}/{total} = {fibre / total:.4f} "
        f"(theoretical 1/{len(SIGMA)} = {1 / len(SIGMA):.4f}); a constant-False "
        f"predictor would score {1 - fibre / total:.1%}, so section 6 needs this "
        f"number to be informative."
    )


def sweep(count, max_length, seed=20260725):
    """Fixed-seed pseudorandom words; no dependence on the random module."""

    state = seed
    words = []
    for _ in range(count):
        state = (1103515245 * state + 12345) % (1 << 31)
        length = 5 + state % (max_length - 4)
        letters = []
        for _ in range(length):
            state = (1103515245 * state + 12345) % (1 << 31)
            letters.append(SIGMA[state % len(SIGMA)])
        words.append(tuple(letters))
    return words


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--exhaustive-length", type=int, default=3)
    parser.add_argument("--sweep", type=int, default=4000)
    parser.add_argument("--max-length", type=int, default=200)
    args = parser.parse_args()

    started = time.time()
    seed_words = [word for word in all_words(2)]
    seed_words.extend(sweep(200, 40, seed=101))
    sweep_words = sweep(args.sweep, args.max_length)

    section1(seed_words)
    section2()
    section3()
    section4()
    section5()
    section6(args.exhaustive_length, sweep_words)
    section7(min(args.exhaustive_length, 3))

    print(
        f"[done] every check PASS ({time.time() - started:.1f}s).  Sections 3-5 are "
        f"exhaustive over their state spaces, so the reconstruction of the "
        f"C_7:C_3 identity fibre from certified cut counts is now a theorem about "
        f"all words, not an observation up to length 4."
    )
    print(
        "[open] N-C7C3-001 remains OPEN: no height-one regular expression has been "
        "built or compiled yet.  What sections 1-5 supply is the arithmetic half."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
