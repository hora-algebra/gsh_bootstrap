#!/usr/bin/env python3
"""Full-alphabet stage-2 computation for the metacyclic family F_{p,q} = C_p : C_q.

This is `scripts/research/c7c3_full_alphabet.py` parameterized by `(p, q)`.  No
step of the mechanism has been changed; the three hard-coded constants of that
script have been replaced by their general forms, which are:

    MODULUS = 7               ->  p            (p prime)
    PHASES  = 3               ->  q            (q | p - 1, q > 1)
    POWERS_OF_TWO = (1, 2, 4) ->  POWERS = (r^0, r^1, ..., r^(q-1)) mod p
    IDENTITY = (1, 0)         ->  unchanged

where `r` is a generator of the unique subgroup of order `q` in `(Z/p)^*`.  The
script picks the *smallest* element of exact order `q`, and checks the order is
exactly `q` (a power `r^d = 1` for a proper divisor `d | q` is rejected).  That
choice reproduces the recorded `r` for every target in `TARGETS` below, and each
named target additionally asserts its recorded `r` against the derived one.

`F_{p,q}` is realized as the subgroup of `AGL(1,p)` whose linear part ranges over
`<r> <= (Z/p)^*`:

    (a, b) . (a', b') = (a a', a' b + b')      # apply the left factor first

with `a` in `<r>` and `b` in `Z/p`.  For `(p, q) = (7, 3)` this is the unique
non-abelian group of order 21, `<x, y | x^7 = y^3 = 1, y x y^-1 = x^2>`; in
general section 1 verifies `<x, y | x^p = y^q = 1, y x y^-1 = x^r>` on the nose.

Why this family, and why now.  `FAMILY-A-PRED-01` conjectures that the
multi-mover mechanism of `RESULTS.md` §5.5 closes every split extension of an
abelian group by a cyclic group of *prime* order, and lists `C_13 : C_3`,
`C_11 : C_5` and `C_19 : C_3` among the instances that have never been run.
`F20-FULL-OBS-01` showed the mechanism fails on the full 20-letter alphabet of
`F_20 = C_5 : C_4` and localized the failure to the phase group `Z/4` being
*composite*: the `eps = 2` letters have phase orbit `{0, 2}`, a proper subgroup,
so they bounce `1 <-> 3` forever without meeting the cut phase.  `C7C3-FULL-01`
then passed on `Z/3`.  This script runs the same code path on all of them, so
that the positive and the negative instances are decided by one implementation
rather than by two scripts that could differ silently.

The script certifies the pattern-conditioned token languages exactly, builds the
forward/backward GF(p) system, solves for the `beta` functional, and checks the
reconstruction of the identity fibre end to end.  The output is deterministic.

Section 7 removes the sample that used to cap these rows.  Sections 5 and 6
compare the reconstruction with the direct product on every word of length <= 3
and then on a fixed-seed sweep, which can refute and cannot establish; section 7
BFSes the product of the certified-feature machine with the group element and
checks the agreement at every reachable state, so the agreement holds on every
word with no length bound.  That is the repair `PROOF_OBLIGATIONS.md` `L-A4-001`
names, in the style of `prove_function` in `scripts/research/weis_l2_family.py`,
and it reports through `tools/verdict.py` so the status is computed from what
ran.  Two residues, both recorded rather than absorbed: section 7 decides a
machine, and that the machine is section 5's own function is compared on a
bounded set of words in 7(c), which is a sample and is filed as one under its
own step id.  And nothing here is a formal proof of `HeightOneForGroup
(C_p : C_q)` for any `(p, q)`: certifying the cuts and solving the linear system
is not a language equivalence, and no regular expression of height one is built
or compiled here.

Controls.  Sections 2 and 6 exist because the positive path of this computation
had never been executed for any group before the `C_7 : C_3` script: an
"everything passed" report and a judge that cannot say no are indistinguishable
outputs.  Section 2 runs the same-letter pure-power patterns, which must FAIL,
before trusting the ones that pass; that control is printed *before* the
candidate-failure exit, so it is reported even on a group where the candidates
themselves fail.  Section 6 mutates every solved coefficient and requires the
reconstruction of section 5 to break, reports the membership base rate so that
section 5 cannot be passing on a near-constant predicate, and exhibits a pair of
words that letter counts alone cannot separate.  Section 7 re-runs the same
mutation test as a decision rather than a replay: each perturbed coefficient
gets its own BFS, and every one of them must make that BFS fail.  A perturbation
the traversal cannot notice would mean the traversal is not testing the claim,
so a single survivor fails the check instead of passing quietly.

The whole-script control is `--target F_20`, which must FAIL in section 2 with
0 certified patterns out of 291, reproducing `F20-FULL-OBS-01`.  If this script
ever certifies `F_20`, that is an implementation bug, not a breakthrough.
"""

from __future__ import annotations

import argparse
import itertools
import math
import random
import sys
import time
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.verdict import (  # noqa: E402
    Control,
    Run,
    VerdictError,
    exhaustive,
    load as load_verdict,
    sampled,
)


# name -> (p, q, recorded r).  The recorded r is asserted against the derived one.
TARGETS = {
    "C_7:C_3": (7, 3, 2),
    "C_13:C_3": (13, 3, 3),
    "C_11:C_5": (11, 5, 3),
    "C_19:C_3": (19, 3, 7),
    "F_20": (5, 4, 2),
}
# The ledger row each named target reports against.  Section 7 names the *step*
# id `ROW/reconstruction`, never the row itself: the row also claims the
# aperiodicity table, the rank, and a group identification, and a check that
# named the row would let it inherit a ceiling from one component.  That is the
# `A4-STD-01` sub-step loophole, which `tools/verdict.py` exists to close.
LEDGER_ROWS = {
    "C_7:C_3": "C7C3-FULL-01",
    "C_13:C_3": "C13C3-FULL-01",
    "C_11:C_5": "C11C5-FULL-01",
    "C_19:C_3": "C19C3-FULL-01",
}
TARGET_ALIASES = {
    "c7c3": "C_7:C_3",
    "c13c3": "C_13:C_3",
    "c11c5": "C_11:C_5",
    "c19c3": "C_19:C_3",
    "f20": "F_20",
    "c_5:c_4": "F_20",
}


# ---------------- parameters (set once by ``configure``) ----------------

MODULUS = 0      # p
PHASES = 0       # q
ROOT = 0         # r, a generator of the order-q subgroup of (Z/p)^*
POWERS = ()      # (r^0, ..., r^(q-1)) mod p
IDENTITY = (1, 0)
GROUP_NAME = ""

SIGMA = ()
EPSILON = {}
NONMOVERS = ()
MOVERS = ()
CONTRIBUTING = ()


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def multiplicative_order(a: int, p: int) -> int:
    """Order of ``a`` in ``(Z/p)^*``.  Refuses ``a`` that is not a unit.

    The guard is not a nicety.  A non-unit has no order, and this loop never
    reaches 1 on one -- ``0 * 0 % p`` is 0 forever -- so without the check
    ``--r 0`` hangs instead of being refused, and hanging is the one failure a
    caller cannot tell from a long computation.
    """
    value = a % p
    if math.gcd(value, p) != 1:
        raise SystemExit(
            f"r = {a} is {value} mod {p}, which is not invertible, so it has "
            f"no multiplicative order and cannot generate anything"
        )
    order = 1
    while value != 1:
        value = value * a % p
        order += 1
    return order


def derive_root(p: int, q: int) -> int:
    """Smallest element of ``(Z/p)^*`` of order exactly ``q``."""
    for candidate in range(2, p):
        if pow(candidate, q, p) != 1:
            continue
        if multiplicative_order(candidate, p) != q:
            continue
        return candidate
    raise SystemExit(f"no element of order exactly {q} in (Z/{p})^*")


def configure(p: int, q: int, root: int | None, name: str) -> int:
    global MODULUS, PHASES, ROOT, POWERS, GROUP_NAME
    global SIGMA, EPSILON, NONMOVERS, MOVERS, CONTRIBUTING
    if not is_prime(p):
        raise SystemExit(f"p = {p} is not prime")
    if q < 2 or (p - 1) % q:
        raise SystemExit(f"q = {q} does not divide p - 1 = {p - 1}, or is < 2")
    derived = derive_root(p, q)
    if root is None:
        root = derived
    elif multiplicative_order(root, p) != q:
        raise SystemExit(
            f"r = {root} has order {multiplicative_order(root, p)} mod {p}, not {q}"
        )
    MODULUS = p
    PHASES = q
    ROOT = root
    POWERS = tuple(pow(root, k, p) for k in range(q))
    GROUP_NAME = name
    if len(set(POWERS)) != q:
        raise SystemExit(f"<{root}> does not have {q} distinct powers mod {p}")
    SIGMA = tuple(
        (POWERS[epsilon], beta)
        for epsilon in range(PHASES)
        for beta in range(MODULUS)
    )
    EPSILON = {g: POWERS.index(g[0]) for g in SIGMA}
    NONMOVERS = tuple(g for g in SIGMA if EPSILON[g] == 0)
    MOVERS = tuple(g for g in SIGMA if EPSILON[g] != 0)
    CONTRIBUTING = tuple(g for g in SIGMA if g[1] != 0)
    return derived


def compose(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    """Apply ``left`` first and ``right`` second."""
    alpha, beta = left
    alpha_prime, beta_prime = right
    return (
        alpha * alpha_prime % MODULUS,
        (alpha_prime * beta + beta_prime) % MODULUS,
    )


def letter_name(g: tuple[int, int]) -> str:
    return f"g(e={EPSILON[g]},b={g[1]})"


def evaluate(word: tuple[tuple[int, int], ...]) -> tuple[int, int]:
    product = IDENTITY
    for letter in word:
        product = compose(product, letter)
    return product


def coordinate_formula(word: tuple[tuple[int, int], ...]) -> tuple[int, int]:
    total_phase = sum(EPSILON[g] for g in word) % PHASES
    suffix_phase = 0
    beta = 0
    for letter in reversed(word):
        beta = (beta + letter[1] * POWERS[suffix_phase]) % MODULUS
        suffix_phase = (suffix_phase + EPSILON[letter]) % PHASES
    return POWERS[total_phase], beta


def prefix_coordinates(word: tuple[tuple[int, int], ...]) -> tuple[int, int]:
    phase = 0
    beta = 0
    for letter in word:
        beta = (beta + letter[1] * POWERS[phase]) % MODULUS
        phase = (phase + EPSILON[letter]) % PHASES
    return POWERS[phase], beta


def all_words(max_length: int):
    for length in range(max_length + 1):
        yield from itertools.product(SIGMA, repeat=length)


# ---------------- pattern-conditioned cuts ----------------


class CutPattern:
    """A q-entry cut, optionally continued by a one- or two-letter suffix."""

    def __init__(self, q: int, pattern):
        self.q = q
        self.pattern = pattern

    def matches(self, previous, letter) -> bool:
        if self.pattern is None:
            return False
        if self.pattern[0] == "single":
            return letter == self.pattern[1]
        return previous == self.pattern[1] and letter == self.pattern[2]

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
    accept = ("accept",)
    dead = ("dead",)
    start = (0, None)
    transitions = {}
    seen = {start, accept, dead}
    queue = deque([start])
    cut = CutPattern(0, pattern)
    for state in (accept, dead):
        for letter in SIGMA:
            transitions[state, letter] = dead
    while queue:
        phase, previous = queue.popleft()
        for letter in SIGMA:
            next_phase = (phase + EPSILON[letter]) % PHASES
            if next_phase == 0:
                next_state = (
                    (next_phase, letter)
                    if cut.matches(previous, letter)
                    else accept
                )
            else:
                next_state = (next_phase, letter)
            transitions[(phase, previous), letter] = next_state
            if next_state not in seen:
                seen.add(next_state)
                queue.append(next_state)
    return tuple(sorted(seen, key=repr)), transitions, start, {accept}


def minimize_dfa(states, transitions, start, accepting):
    accepting = frozenset(accepting)
    rejecting = frozenset(set(states) - set(accepting))
    partitions = [block for block in (accepting, rejecting) if block]
    while True:
        block_of = {
            state: index
            for index, block in enumerate(partitions)
            for state in block
        }
        refined = []
        for block in partitions:
            groups = defaultdict(set)
            for state in block:
                signature = tuple(
                    block_of[transitions[state, letter]] for letter in SIGMA
                )
                groups[signature].add(state)
            refined.extend(frozenset(group) for group in groups.values())
        if len(refined) == len(partitions):
            break
        partitions = refined
    block_of = {
        state: index
        for index, block in enumerate(partitions)
        for state in block
    }
    minimized = {
        (index, letter): block_of[transitions[next(iter(block)), letter]]
        for index, block in enumerate(partitions)
        for letter in SIGMA
    }
    minimized_accepting = {block_of[state] for state in accepting}
    return tuple(range(len(partitions))), minimized, block_of[start], minimized_accepting


def compose_transformation(left, right):
    return tuple(right[left[index]] for index in range(len(left)))


def aperiodicity_certificate(pattern):
    """Exact: minimize, enumerate the transition monoid, test every element.

    A star-free (equivalently: aperiodic) token language is what licenses the
    height-one construction.  The monoid is enumerated by BFS over the letter
    transformations, so ``monoid`` below is its exact order, not a bound.
    """
    states, transitions, start, accepting = token_dfa(pattern)
    states, transitions, _, _ = minimize_dfa(
        states, transitions, start, accepting
    )
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


def pattern_signature(pattern):
    if pattern is None:
        return ("base",)
    if pattern[0] == "single":
        return ("single", EPSILON[pattern[1]])
    left, right = pattern[1], pattern[2]
    return ("pair", EPSILON[left], EPSILON[right], left == right)


def candidate_patterns():
    patterns = [None]
    patterns.extend(("single", h) for h in NONMOVERS)
    patterns.extend(
        ("pair", h, g) for g in MOVERS for h in SIGMA if h != g
    )
    return tuple(patterns)


def certify_patterns(patterns=None):
    if patterns is None:
        patterns = candidate_patterns()
    cache = {}
    results = {}
    for pattern in patterns:
        signature = pattern_signature(pattern)
        if signature not in cache:
            cache[signature] = aperiodicity_certificate(pattern)
        results[pattern] = cache[signature]
    return patterns, results, cache


# ---------------- certified features ----------------


@dataclass(frozen=True)
class FeatureData:
    """Values of the certified cuts, plus the sparse event counts they encode.

    ``base_cuts[q]`` is the value of the plain q-cut.  ``nonmover_events`` and
    ``pair_events`` are the *differences* ``base_cut - conditioned_cut``, stored
    sparsely because the dense tables are almost all zero; section 3 checks that
    the reconstructed conditioned cuts agree with ``CutPattern.run`` exactly.
    """

    total_phase: int
    first: tuple[int, int] | None
    last: tuple[int, int] | None
    letter_counts: dict
    base_cuts: tuple[int, ...]
    nonmover_events: dict
    pair_events: dict
    # Purely an index over ``pair_events``: ``pair_totals[(right, phase)]`` is
    # ``sum_left pair_events[(left, right, phase)]``.  ``pair_events`` never has
    # an entry with ``left == right`` (``certified_features`` skips those), so
    # this is exactly the sum that ``mover_rhs`` needs, and no information is
    # added.  Its only purpose is to turn the per-letter |Sigma|-fold sum into a
    # lookup; ``section3b`` checks the two agree.
    pair_totals: dict

    def single_cut(self, letter, phase):
        return (
            self.base_cuts[phase] - self.nonmover_events.get((letter, phase), 0)
        ) % MODULUS

    def pair_cut(self, left, right, phase):
        return (
            self.base_cuts[phase] - self.pair_events.get((left, right, phase), 0)
        ) % MODULUS

    def nonmover_count(self, letter, phase):
        return self.nonmover_events.get((letter, phase), 0) % MODULUS

    def pair_count(self, left, right, arrival_phase):
        return self.pair_events.get((left, right, arrival_phase), 0) % MODULUS

    def pair_total(self, right, arrival_phase):
        return self.pair_totals.get((right, arrival_phase), 0) % MODULUS


def certified_features(word) -> FeatureData:
    phase = 0
    previous = None
    arrivals = [0] * PHASES
    nonmover_events = defaultdict(int)
    pair_events = defaultdict(int)
    letter_counts = defaultdict(int)
    for letter in word:
        letter_counts[letter] = (letter_counts[letter] + 1) % MODULUS
        phase = (phase + EPSILON[letter]) % PHASES
        arrivals[phase] = (arrivals[phase] + 1) % MODULUS
        if EPSILON[letter] == 0:
            nonmover_events[letter, phase] = (
                nonmover_events[letter, phase] + 1
            ) % MODULUS
        if previous is not None and EPSILON[letter] != 0 and previous != letter:
            pair_events[previous, letter, phase] = (
                pair_events[previous, letter, phase] + 1
            ) % MODULUS
        previous = letter
    pair_totals = defaultdict(int)
    for (_left, right, arrival), count in pair_events.items():
        pair_totals[right, arrival] += count
    return FeatureData(
        total_phase=phase,
        first=word[0] if word else None,
        last=word[-1] if word else None,
        letter_counts=dict(letter_counts),
        base_cuts=tuple(arrivals),
        nonmover_events=dict(nonmover_events),
        pair_events=dict(pair_events),
        pair_totals=dict(pair_totals),
    )


# ---------------- GF(p) linear algebra ----------------


def rank_modp(rows, columns):
    matrix = [[entry % MODULUS for entry in row[:columns]] for row in rows]
    rank = 0
    pivot_columns = []
    for column in range(columns):
        pivot = None
        for index in range(rank, len(matrix)):
            if matrix[index][column] % MODULUS:
                pivot = index
                break
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inverse = pow(matrix[rank][column], -1, MODULUS)
        matrix[rank] = [inverse * value % MODULUS for value in matrix[rank]]
        for index in range(len(matrix)):
            if index == rank or matrix[index][column] % MODULUS == 0:
                continue
            factor = matrix[index][column] % MODULUS
            matrix[index] = [
                (left - factor * right) % MODULUS
                for left, right in zip(matrix[index], matrix[rank])
            ]
        pivot_columns.append(column)
        rank += 1
    return rank, tuple(pivot_columns), matrix


def solve_modp(coefficients, rhs):
    """Solve ``coefficients @ x = rhs`` over GF(MODULUS); None if inconsistent."""
    columns = len(coefficients[0]) if coefficients else 0
    augmented = [
        list(row) + [rhs[index] % MODULUS]
        for index, row in enumerate(coefficients)
    ]
    rank = 0
    pivots = []
    for column in range(columns):
        pivot = None
        for index in range(rank, len(augmented)):
            if augmented[index][column] % MODULUS:
                pivot = index
                break
        if pivot is None:
            continue
        augmented[rank], augmented[pivot] = augmented[pivot], augmented[rank]
        inverse = pow(augmented[rank][column] % MODULUS, -1, MODULUS)
        augmented[rank] = [
            inverse * value % MODULUS for value in augmented[rank]
        ]
        for index in range(len(augmented)):
            if index == rank or augmented[index][column] % MODULUS == 0:
                continue
            factor = augmented[index][column] % MODULUS
            augmented[index] = [
                (left - factor * right) % MODULUS
                for left, right in zip(augmented[index], augmented[rank])
            ]
        pivots.append(column)
        rank += 1
    for row in augmented:
        if all(value == 0 for value in row[:columns]) and row[columns] != 0:
            return None
    solution = [0] * columns
    for row_index, column in enumerate(pivots):
        solution[column] = augmented[row_index][columns]
    return solution


def mover_matrix(epsilon):
    """Rows of the system for one mover letter g with phase shift ``epsilon``.

    Unknowns are ``x_p`` (occurrences of g at prefix phase p) followed by
    ``n_a`` (occurrences of g at arrival phase a immediately preceded by g
    itself -- the one count the pure-power patterns fail to certify).

    Forward reading gives ``x_p - n_{p+eps} = known``; reading the word backwards
    sends prefix phase p to ``P - eps - p`` and gives ``x_p - n_{p+2eps} = known``.
    These two families are independent exactly when ``eps != 2*eps`` in the phase
    group Z/q, i.e. when ``eps != 0`` and q has no element of order dividing 2 --
    automatic for a prime q > 2, and the point where the ``Z/4`` case of `F_20`
    degenerates.  The last row is the total count of g.
    """
    rows = []
    labels = []
    for phase in range(PHASES):
        row = [0] * (2 * PHASES)
        row[phase] = 1
        row[PHASES + (phase + epsilon) % PHASES] = -1
        rows.append(tuple(value % MODULUS for value in row))
        labels.append(f"F{phase}")
    for phase in range(PHASES):
        row = [0] * (2 * PHASES)
        row[phase] = 1
        row[PHASES + (phase + 2 * epsilon) % PHASES] = -1
        rows.append(tuple(value % MODULUS for value in row))
        labels.append(f"B{phase}")
    rows.append(tuple([1] * PHASES + [0] * PHASES))
    labels.append("C")
    return tuple(rows), tuple(labels)


def objective_combination(epsilon):
    """Express ``sum_p r^p x_p`` as a GF(p) combination of the available rows."""
    rows, labels = mover_matrix(epsilon)
    target = POWERS + (0,) * PHASES
    transpose = tuple(
        tuple(row[column] for row in rows) for column in range(2 * PHASES)
    )
    coefficients = solve_modp(transpose, target)
    return rows, labels, coefficients


def mover_rhs_explicit(forward, backward, letter):
    """Reference form: the known-pair term summed letter by letter over Sigma.

    This is the shape the ``C_7 : C_3`` script uses.  It is kept verbatim as the
    reference against which the indexed ``mover_rhs`` is checked in section 3b,
    because the indexed form is the only place where this parameterization does
    something the original did not.
    """
    epsilon = EPSILON[letter]
    rhs = []
    for phase in range(PHASES):
        arrival = (phase + epsilon) % PHASES
        known_pairs = sum(
            forward.pair_count(left, letter, arrival)
            for left in SIGMA
            if left != letter
        )
        start_term = int(forward.first == letter and phase == 0)
        rhs.append((known_pairs + start_term) % MODULUS)
    for phase in range(PHASES):
        reverse_phase = (forward.total_phase - epsilon - phase) % PHASES
        arrival = (reverse_phase + epsilon) % PHASES
        known_pairs = sum(
            backward.pair_count(left, letter, arrival)
            for left in SIGMA
            if left != letter
        )
        end_term = int(backward.first == letter and reverse_phase == 0)
        rhs.append((known_pairs + end_term) % MODULUS)
    rhs.append(forward.letter_counts.get(letter, 0))
    return tuple(rhs)


def mover_rhs(forward, backward, letter):
    """Same values as ``mover_rhs_explicit``, with the Sigma-fold sum indexed.

    The alphabet has ``p*q`` letters, so the reference form costs
    ``|MOVERS| * 2q * |Sigma|`` dictionary probes per word; at ``p = 19`` that is
    13k probes for every single word, which puts the section 6 mutation test out
    of reach.  ``pair_totals`` holds the identical sum.
    """
    epsilon = EPSILON[letter]
    total_phase = forward.total_phase
    forward_totals = forward.pair_totals
    backward_totals = backward.pair_totals
    forward_first = forward.first
    backward_first = backward.first
    rhs = []
    for phase in range(PHASES):
        arrival = (phase + epsilon) % PHASES
        known_pairs = forward_totals.get((letter, arrival), 0)
        start_term = int(forward_first == letter and phase == 0)
        rhs.append((known_pairs + start_term) % MODULUS)
    for phase in range(PHASES):
        reverse_phase = (total_phase - epsilon - phase) % PHASES
        arrival = (reverse_phase + epsilon) % PHASES
        known_pairs = backward_totals.get((letter, arrival), 0)
        end_term = int(backward_first == letter and reverse_phase == 0)
        rhs.append((known_pairs + end_term) % MODULUS)
    rhs.append(forward.letter_counts.get(letter, 0))
    return tuple(rhs)


def prefix_beta_from_certified_features(word, combinations):
    forward = certified_features(word)
    backward = certified_features(tuple(reversed(word)))
    if backward.total_phase != forward.total_phase:
        raise AssertionError("reversal changed the total phase")
    beta = 0
    for letter in NONMOVERS:
        if letter[1] == 0:
            continue
        weighted = sum(
            POWERS[phase] * forward.nonmover_count(letter, phase)
            for phase in range(PHASES)
        )
        beta = (beta + letter[1] * weighted) % MODULUS
    for letter in MOVERS:
        if letter[1] == 0:
            continue
        rhs = mover_rhs(forward, backward, letter)
        combination = combinations[EPSILON[letter]]
        weighted = sum(c * value for c, value in zip(combination, rhs))
        beta = (beta + letter[1] * weighted) % MODULUS
    return forward.total_phase, beta


def identity_from_certified_features(word, combinations):
    phase, beta = prefix_beta_from_certified_features(
        tuple(reversed(word)), combinations
    )
    return phase == 0 and beta == 0


def direct_identity(word):
    return evaluate(word) == IDENTITY


def pattern_text(pattern):
    if pattern is None:
        return "base"
    if pattern[0] == "single":
        return f"single {letter_name(pattern[1])}"
    return f"pair {letter_name(pattern[1])} -> {letter_name(pattern[2])}"


def count_signature(word):
    counts = [0] * len(SIGMA)
    indices = {letter: index for index, letter in enumerate(SIGMA)}
    for letter in word:
        index = indices[letter]
        counts[index] = (counts[index] + 1) % MODULUS
    return (
        sum(EPSILON[letter] for letter in word) % PHASES,
        word[0] if word else None,
        word[-1] if word else None,
        tuple(counts),
    )


def minimal_count_witness(max_length=4):
    for length in range(max_length + 1):
        seen = {}
        for word in itertools.product(SIGMA, repeat=length):
            signature = count_signature(word)
            membership = direct_identity(word)
            previous = seen.get(signature)
            if previous is not None and previous[1] != membership:
                return previous[0], word
            seen[signature] = (word, membership)
    return None


def fail(section, message):
    print(f"[{section}] FAIL: {message}", flush=True)
    raise SystemExit(1)


# ---------------- sections ----------------


def section1(derived_root) -> None:
    print("=== 1. group and coordinate checks ===", flush=True)
    order = MODULUS * PHASES
    if (
        len(SIGMA) != order
        or len(NONMOVERS) != MODULUS
        or len(MOVERS) != MODULUS * (PHASES - 1)
    ):
        fail(1, "incorrect alphabet partition")
    if ROOT != derived_root:
        print(
            f"  NOTE: r = {ROOT} was supplied; the smallest element of order "
            f"{PHASES} is {derived_root}. Both generate the same subgroup, but "
            "the letter labelling differs from the recorded one.",
            flush=True,
        )
    if sorted(POWERS) != sorted(set(POWERS)) or pow(ROOT, PHASES, MODULUS) != 1:
        fail(1, f"the linear part is not <{ROOT}> of order {PHASES} mod {MODULUS}")
    for divisor in range(1, PHASES):
        if PHASES % divisor == 0 and pow(ROOT, divisor, MODULUS) == 1:
            fail(1, f"r = {ROOT} has order {divisor}, a proper divisor of {PHASES}")

    # closure, associativity, identity, inverses on the full p*q elements
    elements = SIGMA
    element_set = set(elements)
    for left in elements:
        if compose(left, IDENTITY) != left or compose(IDENTITY, left) != left:
            fail(1, "identity law")
        if not any(compose(left, right) == IDENTITY for right in elements):
            fail(1, f"no inverse for {left}")
        for right in elements:
            if compose(left, right) not in element_set:
                fail(1, "not closed")
    for left in elements:
        for middle in elements:
            for right in elements:
                if compose(compose(left, middle), right) != compose(
                    left, compose(middle, right)
                ):
                    fail(1, "associativity")
    if all(
        compose(left, right) == compose(right, left)
        for left in elements
        for right in elements
    ):
        fail(1, "the group came out abelian")

    # presentation <x, y | x^p, y^q, y x y^-1 = x^r>
    x = (1, 1)
    y = (ROOT, 0)
    def power_of(g, k):
        result = IDENTITY
        for _ in range(k):
            result = compose(result, g)
        return result
    if power_of(x, MODULUS) != IDENTITY or x == IDENTITY:
        fail(1, f"x does not have order {MODULUS}")
    if power_of(y, PHASES) != IDENTITY or y == IDENTITY:
        fail(1, f"y does not have order {PHASES}")
    for divisor in range(1, PHASES):
        if PHASES % divisor == 0 and power_of(y, divisor) == IDENTITY:
            fail(1, f"y has order {divisor}, a proper divisor of {PHASES}")
    y_inverse = next(g for g in elements if compose(y, g) == IDENTITY)
    conjugate = compose(compose(y_inverse, x), y)  # left factor applied first
    nontrivial_powers = {power_of(x, s) for s in POWERS if s != 1}
    if conjugate not in nontrivial_powers:
        fail(1, f"conjugation relation is not x^s for s in <{ROOT}>: {conjugate}")
    generated = {IDENTITY}
    frontier = [IDENTITY]
    while frontier:
        current = frontier.pop()
        for generator in (x, y):
            product = compose(current, generator)
            if product not in generated:
                generated.add(product)
                frontier.append(product)
    if len(generated) != order:
        fail(1, f"x and y generate only {len(generated)} elements")

    checked = 0
    for word in all_words(3):
        checked += 1
        if evaluate(word) != coordinate_formula(word):
            fail(1, f"coordinate mismatch on {word}")
    random_words = random.Random(20260725)
    longer_checked = 0
    for length in range(4, 9):
        for _ in range(4000):
            word = tuple(random_words.choice(SIGMA) for _ in range(length))
            longer_checked += 1
            if evaluate(word) != coordinate_formula(word):
                fail(1, f"coordinate mismatch at length {length}")
    print(
        f"  PASS: {order} elements, non-abelian, associative, "
        f"<x,y | x^{MODULUS}, y^{PHASES}, y x y^-1 = x^{ROOT}> with <x,y> = the "
        f"whole group; {order} letters, non-movers={len(NONMOVERS)}, "
        f"movers={len(MOVERS)}; coordinate formula exhaustive "
        f"for length <= 3 ({checked} words) and on {longer_checked} fixed-seed "
        "words of lengths 4..8.",
        flush=True,
    )


def section2():
    print("\n=== 2. exact aperiodicity table (q=0; all q isomorphic) ===", flush=True)
    atom_started = time.time()
    patterns, pattern_results, signature_results = certify_patterns()
    grouped = defaultdict(lambda: {"count": 0, "result": None})
    for pattern in patterns:
        signature = pattern_signature(pattern)
        grouped[signature]["count"] += 1
        grouped[signature]["result"] = pattern_results[pattern]
    for signature in sorted(grouped, key=repr):
        entry = grouped[signature]
        result = entry["result"]
        status = "OK" if result["aperiodic"] else "FAIL"
        extra = ""
        if not result["aperiodic"]:
            extra = f" period={result['period']} witness={result['witness']}"
        print(
            f"  {signature}: count={entry['count']} {status}; "
            f"minimal_states={result['states']} monoid={result['monoid']}{extra}",
            flush=True,
        )
    failures = [
        pattern for pattern in patterns if not pattern_results[pattern]["aperiodic"]
    ]
    print(
        f"  exact total={len(patterns)}; certified={len(patterns)-len(failures)}; "
        f"failed={len(failures)}; distinct DFA types={len(signature_results)}; "
        f"time={time.time()-atom_started:.1f}s.",
        flush=True,
    )

    # POSITIVE CONTROL on the judge.  The same-letter pure-power patterns are
    # excluded from the candidate list precisely because RESULTS.md 5.5 records
    # that they break aperiodicity for A_4.  If they certified here too, the
    # judge would be answering "aperiodic" unconditionally and the OK rows
    # above would carry no information.  This runs BEFORE the candidate-failure
    # exit so that it is reported for the F_20 negative control too.
    pure = tuple(("pair", g, g) for g in MOVERS)
    _, pure_results, _ = certify_patterns(pure)
    pure_failures = [p for p in pure if not pure_results[p]["aperiodic"]]
    example = pure_results[pure[0]]
    print(
        f"  positive control: of the {len(pure)} excluded same-letter patterns "
        f"(g -> g), {len(pure_failures)} are NOT aperiodic "
        f"(e.g. period={example['period']}, witness={example['witness']}); "
        "the judge can and does answer no.",
        flush=True,
    )
    if len(pure_failures) != len(pure):
        fail(2, "the same-letter positive control did not fail as expected")

    if failures:
        fail(2, f"{len(failures)} candidate patterns are not aperiodic")
    return patterns, pattern_results


def section3(patterns, pattern_results) -> None:
    print("\n=== 3. certified feature identities ===", flush=True)
    feature_rng = random.Random(72103)
    feature_checks = 0
    usable = [
        pattern
        for pattern in patterns
        if pattern_results[pattern]["aperiodic"]
        and not (
            pattern is not None
            and pattern[0] == "pair"
            and pattern[1] == pattern[2]
        )
    ]

    def expected_value(data, pattern, q):
        if pattern is None:
            return data.base_cuts[q]
        if pattern[0] == "single":
            return data.single_cut(pattern[1], q)
        return data.pair_cut(pattern[1], pattern[2], q)

    for word in all_words(2):
        data = certified_features(word)
        for q in range(PHASES):
            for pattern in usable:
                actual = CutPattern(q, pattern).run(word)
                feature_checks += 1
                if actual != expected_value(data, pattern, q):
                    fail(3, f"feature identity mismatch: q={q}, {pattern_text(pattern)}")
    for _ in range(4000):
        length = feature_rng.randint(0, 200)
        word = tuple(feature_rng.choice(SIGMA) for _ in range(length))
        data = certified_features(word)
        q = feature_rng.randrange(PHASES)
        pattern = feature_rng.choice(usable)
        actual = CutPattern(q, pattern).run(word)
        feature_checks += 1
        if actual != expected_value(data, pattern, q):
            fail(3, f"long feature identity mismatch: q={q}, {pattern_text(pattern)}")
    print(f"  PASS: {feature_checks} exact/sweep comparisons.", flush=True)


def section3b() -> None:
    """Control on the one optimization this parameterization adds.

    ``mover_rhs`` reads an index instead of re-summing over Sigma.  If the index
    were wrong, section 5 would be reconstructing the fibre from the wrong right
    hand side and every downstream number would be silently off, so the two
    forms are compared on every word of length <= 2 and on a fixed-seed sweep of
    long words, for every mover letter.
    """
    compared = 0
    for word in all_words(2):
        forward = certified_features(word)
        backward = certified_features(tuple(reversed(word)))
        for letter in MOVERS:
            compared += 1
            if mover_rhs(forward, backward, letter) != mover_rhs_explicit(
                forward, backward, letter
            ):
                fail(3, f"indexed mover_rhs disagrees with the reference on {word}")
    rhs_rng = random.Random(72105)
    for _ in range(300):
        length = rhs_rng.randint(3, 120)
        word = tuple(rhs_rng.choice(SIGMA) for _ in range(length))
        forward = certified_features(word)
        backward = certified_features(tuple(reversed(word)))
        for letter in MOVERS:
            compared += 1
            if mover_rhs(forward, backward, letter) != mover_rhs_explicit(
                forward, backward, letter
            ):
                fail(3, f"indexed mover_rhs disagrees with the reference at {length}")
    print(
        f"  PASS (3b): the indexed mover_rhs agrees with the explicit "
        f"per-letter sum on {compared} (word, mover) pairs.",
        flush=True,
    )


def section4():
    print(f"\n=== 4. GF({MODULUS}) rank and solved beta combination ===", flush=True)
    combinations = {}
    algebra_rng = random.Random(72104)
    for epsilon in range(1, PHASES):
        rows, labels, combination = objective_combination(epsilon)
        rank, _, _ = rank_modp(rows, 2 * PHASES)
        if combination is None:
            fail(4, f"eps={epsilon}: beta functional unsolved (rank {rank})")
        combinations[epsilon] = tuple(combination)
        terms = [
            f"{coefficient}*{label}"
            for coefficient, label in zip(combination, labels)
            if coefficient
        ]
        # Independent check: the identity must hold for *every* (x, n) vector,
        # not merely for the ones the elimination happened to visit.
        mismatches = 0
        for _ in range(5000):
            vector = [algebra_rng.randrange(MODULUS) for _ in range(2 * PHASES)]
            left = sum(
                coefficient * sum(a * b for a, b in zip(row, vector))
                for coefficient, row in zip(combination, rows)
            ) % MODULUS
            right = sum(
                POWERS[phase] * vector[phase] for phase in range(PHASES)
            ) % MODULUS
            mismatches += left != right
        if mismatches:
            fail(4, f"eps={epsilon}: solved combination fails on random vectors")
        print(
            f"  eps={epsilon}: rank={rank}/{2*PHASES}; "
            f"sum_p {ROOT}^p*x_p = {' + '.join(terms) if terms else '0'} "
            f"mod {MODULUS} (verified on 5000 random (x,n) vectors)",
            flush=True,
        )
    if len(combinations) != PHASES - 1:
        fail(4, "beta is not determined by the certified feature system")
    return combinations


def section5(combinations, exhaustive_length, sweep_count, max_length):
    print("\n=== 5. end-to-end reconstruction ===", flush=True)
    exhaustive_count = 0
    members = 0
    for word in all_words(exhaustive_length):
        exhaustive_count += 1
        predicted = identity_from_certified_features(word, combinations)
        actual = direct_identity(word)
        members += actual
        if predicted != actual:
            fail(5, f"reconstruction mismatch on {word}: {predicted} != {actual}")
    sweep_rng = random.Random(2026072503)
    sweep_members = 0
    for _ in range(sweep_count):
        length = sweep_rng.randint(exhaustive_length + 1, max_length)
        word = tuple(sweep_rng.choice(SIGMA) for _ in range(length))
        predicted = identity_from_certified_features(word, combinations)
        actual = direct_identity(word)
        sweep_members += actual
        if predicted != actual:
            fail(5, f"long reconstruction mismatch at length {length}")
    print(
        f"  PASS: all {exhaustive_count} words of length <= {exhaustive_length}; "
        f"{sweep_count} fixed-seed words of length {exhaustive_length+1}..{max_length}.",
        flush=True,
    )
    print(
        f"  membership base rate: {members}/{exhaustive_count} exhaustive "
        f"({members/exhaustive_count:.4f}) and {sweep_members}/{sweep_count} "
        f"sweep ({sweep_members/sweep_count:.4f}); the target predicate is not "
        "near-constant, so agreement is informative.",
        flush=True,
    )
    return exhaustive_count


def section6(combinations, mutation_length, witness_length) -> None:
    print("\n=== 6. negative controls ===", flush=True)

    # (a) mutation test: perturb each solved coefficient and require breakage.
    words = list(all_words(mutation_length))
    survivors = []
    mutations = 0
    for epsilon, combination in sorted(combinations.items()):
        for index in range(len(combination)):
            for delta in range(1, MODULUS):
                mutated = list(combination)
                mutated[index] = (mutated[index] + delta) % MODULUS
                perturbed = dict(combinations)
                perturbed[epsilon] = tuple(mutated)
                mutations += 1
                broke = False
                for word in words:
                    if identity_from_certified_features(
                        word, perturbed
                    ) != direct_identity(word):
                        broke = True
                        break
                if not broke:
                    survivors.append((epsilon, index, delta))
    print(
        f"  (a) mutation test: {mutations} single-coefficient perturbations of "
        f"the solved combinations, each replayed on {len(words)} words; "
        f"{mutations - len(survivors)} broke the reconstruction, "
        f"{len(survivors)} survived.",
        flush=True,
    )
    if survivors:
        # A survivor means section 5 would accept a wrong coefficient, which is
        # the one thing this control exists to catch -- unless the replay was
        # too short to distinguish them at all, in which case the failure is an
        # artifact of the cap and not a fact about the group.  Saying which is
        # the point: a false FAIL that reads like a real one is the same defect
        # as a false PASS.
        hint = ""
        if mutation_length < 3:
            hint = (
                f" NOTE: mutation-length is {mutation_length}. Coefficient "
                "perturbations are not separable on words this short, so this "
                "is very likely an artifact of the cap rather than a real "
                "insensitivity -- re-run at mutation-length 3 before reading "
                "anything into it."
            )
        fail(
            6,
            "some perturbed combinations still reproduce the fibre: "
            f"{survivors[:5]} -- section 5 is not sensitive to the coefficients"
            + hint,
        )

    # (b) the certified pair/single features are doing real work: letter counts
    #     plus phase plus endpoints do NOT separate the fibre.
    witness = minimal_count_witness(witness_length)
    if witness is None:
        fail(6, f"no count-only witness found through length {witness_length}")
    left, right = witness
    print(
        "  (b) counts alone are insufficient -- same phase, endpoints and "
        f"letter counts mod {MODULUS}, different membership "
        f"(length {len(left)}):",
        flush=True,
    )
    print(
        "        w0 = [" + ", ".join(letter_name(g) for g in left) + "]"
        f"  mu={evaluate(left)} in T={direct_identity(left)}",
        flush=True,
    )
    print(
        "        w1 = [" + ", ".join(letter_name(g) for g in right) + "]"
        f"  mu={evaluate(right)} in T={direct_identity(right)}",
        flush=True,
    )


# ---------------- section 7: the reconstruction, decided ----------------
#
# Sections 5 and 6 compare `identity_from_certified_features` with
# `direct_identity` on every word of length <= 3 and then on a fixed-seed
# sample.  A sample can refute and cannot establish, so the row is capped at
# EMPIRICAL no matter how exhaustive sections 1-4 are.  `PROOF_OBLIGATIONS.md`
# `L-A4-001` names the repair: a product BFS in the style of `prove_function` in
# `scripts/research/weis_l2_family.py`, deciding that the group element is a
# function of the certified features on *every* word.
#
# THE MACHINE.  `prefix_beta_from_certified_features(v)` reads two records,
# `forward = certified_features(v)` and `backward = certified_features(v^R)`,
# and returns `(total phase, beta)`; `identity_from_certified_features(word)`
# calls it on `v = word^R`.  `certified_features` is already a left fold, so the
# `forward` half is a machine as written.  The `backward` half is not: reading
# `v` left to right builds `v^R` right to left.  That is the one place where an
# incremental form has to be *derived* rather than transcribed, and the whole of
# the derivation is the single reindexing
#
#     (w-prefix phase through a letter) + (v-prefix phase before it) = total,
#
# which holds because `w = v^R` splits the total phase at each position.  It is
# what turns the `B` rows -- indexed by `total_phase - arrival`, a quantity not
# known until the word ends -- into a term payable at the moment the letter
# stops being the last one.  Everything else below is the fold, term by term:
#
#   (1) the nonmover sum `h[1] * POWERS[phase] * nonmover_count(h, phase)`
#       becomes `x[1] * POWERS[phase after x]` charged at each nonmover x;
#   (2) `comb[ph] * forward.pair_totals[(g, (ph + eps) % q)]` becomes
#       `x[1] * comb[phase before x]` charged when x is a mover whose predecessor
#       differs from it -- exactly the guard in `certified_features`;
#       the `forward.first == g and ph == 0` start term is charged once, at the
#       first letter of v;
#   (3) `comb[2q] * forward.letter_counts[g]` becomes `x[1] * comb[2q]` at each
#       mover occurrence;
#   (4) `comb[q + ph] * backward.pair_totals[(g, (total - ph) % q)]` becomes
#       `prev[1] * comb[q + (phase before prev)]` charged when a letter arrives
#       after a mover `prev != x`, by the reindexing above; the
#       `backward.first == g and reverse_phase == 0` end term is the same
#       expression at the current last letter, and is charged at read-out
#       because that letter can still be extended.
#
# The four running totals are added into one accumulator because only their sum
# is ever read.  The state is therefore
#
#     (mu(v^R), last letter of v, total phase of v, accumulator in GF(p))
#
# and `mu` is stepped by `compose(x, mu)` -- prepending to `v^R` -- so it is
# `direct_identity`'s own product, not a second model of it.
#
# WHAT THIS DOES NOT DECIDE.  That this machine *is*
# `prefix_beta_from_certified_features`.  Nothing in the BFS compares them;
# section 7(b) does, on a bounded set of words, and carries five perturbations
# of the transcription that must all break that comparison.  7(b) is a sample
# and is recorded as one, under its own step id, so the gap is visible rather
# than absorbed.  This is the same residue the `A4-FULL-01` step [4] repair in
# `scripts/ci/completeness_upgrade.py` carries.


MACHINE_START = (IDENTITY, None, 0, 0)


def machine_step(state, letter, combinations, variant=None):
    """One letter appended to ``v``; see the block comment for each term.

    ``variant`` names a deliberate corruption of the transcription, used only by
    section 7(b) as a control on that comparison.  It is never used by the BFS.
    """
    mu, previous, phase, accumulator = state
    epsilon = EPSILON[letter]
    next_phase = (phase + epsilon) % PHASES
    if epsilon == 0:
        if letter[1]:
            # (1) nonmover: certified_features records it at the phase *after*.
            index = next_phase
            if variant == "nonmover-phase":
                index = (index + 1) % PHASES
            accumulator += letter[1] * POWERS[index]
    else:
        combination = combinations[epsilon]
        if letter[1]:
            accumulator += letter[1] * combination[2 * PHASES]  # (3) the C row
            if previous is None:
                # (2) forward.first == letter and ph == 0
                if variant != "drop-start":
                    accumulator += letter[1] * combination[0]
            elif previous != letter or variant == "forward-pair-guard":
                # (2) a forward pair event: right letter a mover, left different.
                index = phase
                if variant == "forward-pair-phase":
                    index = (index + 1) % PHASES
                accumulator += letter[1] * combination[index]
    if previous is not None and EPSILON[previous] != 0 and previous[1]:
        if letter != previous or variant == "backward-pair-guard":
            # (4) `previous` has just stopped being the last letter of v, so it
            # now carries a pair event of v^R; its `B` row index is the phase of
            # v before `previous`.
            combination = combinations[EPSILON[previous]]
            index = (phase - EPSILON[previous]) % PHASES
            if variant == "backward-pair-phase":
                index = (index + 1) % PHASES
            accumulator += previous[1] * combination[PHASES + index]
    # `v` is the reverse of the word section 5 is about, so a letter appended to
    # `v` is prepended to that word: `compose(letter, mu)`, left factor first.
    product = compose(mu, letter) if variant == "mu-order" else compose(letter, mu)
    return (product, letter, next_phase, accumulator % MODULUS)


def machine_value(state, combinations, variant=None):
    """``(total phase, beta)`` for the word that reached ``state``."""
    _mu, previous, phase, accumulator = state
    if previous is not None and EPSILON[previous] != 0 and previous[1]:
        if variant != "drop-end":
            # (4) end term: backward.first == previous with reverse_phase == 0.
            combination = combinations[EPSILON[previous]]
            index = (phase - EPSILON[previous]) % PHASES
            accumulator += previous[1] * combination[PHASES + index]
    return phase, accumulator % MODULUS


def machine_run(word, combinations, variant=None):
    state = MACHINE_START
    for letter in word:
        state = machine_step(state, letter, combinations, variant)
    return state, machine_value(state, combinations, variant)


def decide_reconstruction(combinations, cap):
    """BFS the product of the feature machine with the group element itself.

    Every word drives the machine into exactly one reachable state, so checking
    the agreement at every reachable state checks it for every word.  Returns
    ``(verdict, visited, exact_beta, detail)``; ``verdict`` is ``None`` when the
    cap was hit, which is a BLOCKED result and never a pass.

    ``machine_value`` never reads the group element: the read-out is a function
    of the feature part of the state alone.  So checking it against ``mu`` at
    every reachable state is strictly stronger than the cell constancy of
    ``prove_function`` in ``scripts/research/weis_l2_family.py`` -- two words
    sharing a feature cell get the same read-out and therefore the same ``mu``,
    which is what "the group element is constant on each certified-feature cell"
    says, and this pins down *which* element as well.
    """
    seen = {MACHINE_START}
    frontier = deque([MACHINE_START])
    visited = 0
    exact_beta = True
    while frontier:
        state = frontier.popleft()
        visited += 1
        mu = state[0]
        phase, beta = machine_value(state, combinations)
        if (phase == 0 and beta == 0) != (mu == IDENTITY):
            return (
                False,
                visited,
                False,
                f"disagreement at a reachable state: predicted "
                f"{(phase == 0 and beta == 0)}, mu = {mu}",
            )
        # Strictly stronger than the fibre membership section 5 tests, and
        # reported separately because a failure here would not be a failure of
        # the claim: the reconstruction is only asked for the fibre.
        if (POWERS[phase], beta) != mu:
            exact_beta = False
        for letter in SIGMA:
            following = machine_step(state, letter, combinations)
            if following not in seen:
                if len(seen) >= cap:
                    return None, visited, False, f"state cap {cap} reached"
                seen.add(following)
                frontier.append(following)
    cells = len({state[1:] for state in seen})
    return (
        True,
        visited,
        exact_beta,
        f"membership agrees with the direct product at all {visited} reachable "
        f"product states, hence on every word; those states fall into {cells} "
        f"certified-feature cells (last letter, total phase, GF({MODULUS}) "
        "read-out), so the group element is a function of the cell",
    )


def section7(combinations, row, transcription_length, sweep, cap):
    """Decide section 5's claim, and report through ``tools.verdict``.

    Returns ``(checks, decided)``: the checks to record, and whether the BFS
    decided the claim.
    """
    print("\n=== 7. the reconstruction, decided by product BFS ===", flush=True)
    print(
        f"  limits: state cap={cap}, transcription exhaustive to length "
        f"{transcription_length}, transcription sweep={sweep}",
        flush=True,
    )
    started = time.time()

    # (a) the decision itself.
    verdict, visited, exact_beta, detail = decide_reconstruction(combinations, cap)
    if verdict is None:
        print(
            f"  (a) BLOCKED: {detail} after {visited} states; nothing is decided.",
            flush=True,
        )
        return [], False
    print(
        f"  (a) {'PASS' if verdict else 'FAIL'}: {detail} "
        f"({time.time()-started:.1f}s).",
        flush=True,
    )
    if verdict:
        print(
            "      stronger, and not required by the row: the reconstructed "
            f"(phase, beta) equals mu on every word: {exact_beta}.",
            flush=True,
        )

    # (b) brittleness of the claim: every solved coefficient, every value.
    _rows, labels = mover_matrix(1)
    controls = []
    mutation_started = time.time()
    for epsilon, combination in sorted(combinations.items()):
        for index, value in enumerate(combination):
            for delta in range(1, MODULUS):
                mutated = list(combination)
                mutated[index] = (value + delta) % MODULUS
                perturbed = dict(combinations)
                perturbed[epsilon] = tuple(mutated)
                broke = decide_reconstruction(perturbed, cap)[0] is not True
                controls.append(
                    Control(
                        name=f"eps={epsilon} {labels[index]}: {value} -> {mutated[index]}",
                        mutation=(
                            f"the coefficient of row {labels[index]} in the solved "
                            f"GF({MODULUS}) combination for sum_p {ROOT}^p x_p at "
                            f"eps={epsilon}"
                        ),
                        rejected=broke,
                    )
                )
    fired = sum(1 for control in controls if control.rejected)
    print(
        f"  (b) brittleness: {len(controls)} single-coefficient mutations of the "
        f"solved combinations, each re-decided by its own BFS; {fired} rejected, "
        f"{len(controls)-fired} survived ({time.time()-mutation_started:.1f}s).",
        flush=True,
    )

    # (c) transcription: the machine of (a) against the function of section 5.
    #     This is a sample, and is recorded as one.
    comparison = list(all_words(transcription_length))
    exhaustive_words = len(comparison)
    sweep_rng = random.Random(2026072801)
    comparison += [
        tuple(sweep_rng.choice(SIGMA) for _ in range(sweep_rng.randint(transcription_length + 1, 200)))
        for _ in range(sweep)
    ]

    def disagreements(variant):
        """The first word where the machine and section 5's own code differ.

        Both halves of the product are compared, not just the reconstruction:
        the state's group element must be the product `direct_identity` takes,
        or the BFS would be checking a correct reconstruction against the wrong
        target and would pass for the wrong reason.
        """
        for word in comparison:
            state, value = machine_run(word, combinations, variant)
            if value != prefix_beta_from_certified_features(word, combinations):
                return word
            if state[0] != evaluate(tuple(reversed(word))):
                return word
        return None

    faithful = disagreements(None) is None
    variants = (
        ("nonmover-phase", "the phase at which a nonmover occurrence is counted"),
        ("forward-pair-phase", "the phase at which a forward pair event is counted"),
        ("backward-pair-phase", "the phase at which a backward pair event is counted"),
        ("forward-pair-guard", "the rule that a pair event needs two distinct letters"),
        ("backward-pair-guard", "the same rule on the reversed word"),
        ("drop-start", "the first-letter term of the forward rows"),
        ("drop-end", "the last-letter term of the backward rows"),
        ("mu-order", "the order in which the group element multiplies letters"),
    )
    caught = [name for name, _ in variants if disagreements(name) is not None]
    print(
        f"  (c) transcription: the machine of (a) agrees with "
        f"prefix_beta_from_certified_features AND with evaluate() on all "
        f"{exhaustive_words} "
        f"words of length <= {transcription_length} and {sweep} fixed-seed words: "
        f"{faithful}. Of {len(variants)} deliberate corruptions of the "
        f"transcription, {len(caught)} are caught by that comparison"
        + (f"; MISSED: {[n for n, _ in variants if n not in caught]}" if len(caught) != len(variants) else "")
        + ".",
        flush=True,
    )
    print(
        "      This step is a SAMPLE. It is what stands between (a) and the "
        "claim that section 5's own function is decided, and it is recorded "
        "under its own step id so that the gap stays visible.",
        flush=True,
    )

    checks = [
        exhaustive(
            f"{GROUP_NAME} identity fibre from certified features",
            f"{row}/reconstruction",
            passed=bool(verdict),
            universe=visited,
            detail=detail
            + f"; the reconstructed (phase, beta) equals mu exactly: {exact_beta}",
            controls=controls,
            covers="claim",
            rationale=(
                "The id names one step: that the reconstruction of the identity "
                "fibre from the certified features agrees with the direct "
                "product on EVERY word, which is the step that capped this row "
                "at EMPIRICAL. A word enters that statement only through the "
                "state its letters drive the machine into; every word reaches "
                "exactly one reachable state; the BFS visits every reachable "
                "state and checks the agreement there. So no word is outside "
                "the traversal, and there is no length bound and no sample. "
                "What this does NOT cover, and what a reviewer should attack: "
                "(i) that the machine computes the same function as "
                "prefix_beta_from_certified_features -- compared on a bounded "
                "set of words by step 7(c), recorded separately as "
                f"{row}/streaming-transcription, which stays EMPIRICAL; "
                "(ii) the rest of the row -- aperiodicity, rank, group "
                "identification -- decided by sections 1, 2 and 4; (iii) the "
                "row's CAUTION, that no height-one expression is built or "
                "compiled here, which nothing in this script addresses."
            ),
        ),
        sampled(
            f"{GROUP_NAME} streaming machine equals the section 5 function",
            f"{row}/streaming-transcription",
            passed=faithful and len(caught) == len(variants),
            sample=(
                f"all words of length <= {transcription_length} and {sweep} "
                "fixed-seed words of length up to 200"
            ),
            detail=(
                f"agreement of both halves -- the reconstruction against "
                f"prefix_beta_from_certified_features and the state's group "
                f"element against evaluate(): {faithful}; "
                f"{len(caught)}/{len(variants)} deliberate "
                "corruptions of the transcription are caught by the same "
                "comparison, so the sample is not passing on insensitivity. A "
                "sample can refute and cannot establish; this step is the "
                "residue of the 7(a) decision and is why the id above is a step "
                "id and not the row"
            ),
            covers="claim",
            rationale=(
                "This id claims exactly one thing -- that the machine section "
                "7(a) decides computes the same function as "
                "prefix_beta_from_certified_features -- and 7(c) is the whole of "
                "the evidence for it. It is marked `claim` so that the ceiling "
                "this file records for it reads EMPIRICAL rather than "
                "UNREVIEWED: a sample that ran is weaker than a decision and "
                "stronger than silence, and writing it down as EMPIRICAL is what "
                "makes the residue of 7(a) legible instead of absent."
            ),
        ),
    ]
    return checks, bool(verdict)


def record_verdict(checks, row, path):
    """Write the verdict, keeping the checks other targets left in the file.

    One script, one verdict file, four targets: a run of `--target C13C3` must
    not silently delete what `--target C7C3` earned. Checks whose ids belong to
    THIS row are replaced, never merged, so a stale result cannot survive a
    re-run of its own target.
    """
    run = Run("scripts/research/metacyclic_full_alphabet.py")
    if path.is_file():
        try:
            previous = load_verdict(path)
        except VerdictError as error:
            print(f"  NOTE: discarding the previous verdict file ({error})", flush=True)
        else:
            for check in previous.checks:
                if not any(cid.startswith(f"{row}/") for cid in check.claim_ids):
                    run.checks.append(check)
    for check in checks:
        run.add(check)
    status = run.finish(path)
    print(f"  verdict covers: {', '.join(run.claim_ids)}", flush=True)
    return status


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--target",
        help="named group from the recorded table: " + ", ".join(sorted(TARGETS))
        + ". With no arguments at all this defaults to C7C3, so that the run "
        "scripts/ci/run_research.py makes is the positive control: this "
        "generalization must keep reproducing c7c3_full_alphabet.py exactly. "
        "Giving --p/--q selects an arbitrary member of the family instead, "
        "which is what this program exists for -- do NOT make this an argparse "
        "default, or --p/--q become unreachable and read as contradicting a "
        "target the caller never asked for.",
    )
    parser.add_argument("--p", type=int, help="the prime p")
    parser.add_argument("--q", type=int, help="the phase group order q, q | p-1")
    parser.add_argument(
        "--r",
        type=int,
        help="override the generator of the order-q subgroup of (Z/p)^*; "
        "its order is checked to be exactly q",
    )
    parser.add_argument(
        "--exhaustive-length",
        type=int,
        default=3,
        help="exhaustive reconstruction up to this word length (default 3; for "
        "(7,3) that is 9724 words, and 4 is 204205 words and takes minutes)",
    )
    parser.add_argument("--sweep", type=int, default=20000)
    parser.add_argument("--max-length", type=int, default=400)
    parser.add_argument(
        "--mutation-length",
        type=int,
        default=None,
        help="word length for the section 6(a) mutation control; defaults to "
        "min(exhaustive-length, 3), which is what the C_7 : C_3 script uses. "
        "Set it explicitly when --exhaustive-length is lowered: on the larger "
        "alphabets a mutated coefficient is not detectable by words of length "
        "<= 2 at all, so letting this follow a lowered --exhaustive-length "
        "reports survivors and fails section 6 for a reason that has nothing "
        "to do with the group.",
    )
    parser.add_argument(
        "--witness-length",
        type=int,
        default=4,
        help="section 6(b) searches for a count-only witness up to this length",
    )
    parser.add_argument(
        "--skip-section7",
        action="store_true",
        help="do not decide the reconstruction and do not write a verdict; the "
        "run then reports EMPIRICAL, as it did before section 7 existed",
    )
    parser.add_argument(
        "--section7-cap",
        type=int,
        default=20_000_000,
        help="refuse to keep exploring past this many product states. Hitting "
        "it is reported as BLOCKED and never as a pass",
    )
    parser.add_argument(
        "--section7-transcription-length",
        type=int,
        default=None,
        help="section 7(c) compares the machine with the section 5 function on "
        "every word up to this length; defaults to 3 when the alphabet is small "
        "enough for that to stay cheap and 2 otherwise",
    )
    parser.add_argument("--section7-sweep", type=int, default=3000)
    parser.add_argument(
        "--write-verdict",
        action="store_true",
        help="write the machine-readable verdict to disk. Off by default: a "
        "verdict file backs a COMPUTED row, and no row here can be COMPUTED "
        "while 7(c) is a sample, so a committed file would be the orphan "
        "lint_claims.py refuses. Turn it on when 7(c) closes, and register the "
        "producer there and in scripts/check.sh at the same time.",
    )
    parser.add_argument(
        "--verdict-path",
        default=None,
        help="where --write-verdict puts the verdict; defaults to "
        "data/verdicts/metacyclic_full_alphabet.json",
    )
    args = parser.parse_args()

    recorded_root = None
    if args.target is None and args.p is None and args.q is None:
        args.target = "C7C3"

    if args.target is not None:
        key = TARGET_ALIASES.get(args.target.lower(), args.target)
        if key not in TARGETS:
            raise SystemExit(
                f"unknown target {args.target!r}; known: {', '.join(sorted(TARGETS))}"
            )
        p, q, recorded_root = TARGETS[key]
        if args.p is not None and args.p != p:
            raise SystemExit(f"--p {args.p} contradicts --target {key} (p = {p})")
        if args.q is not None and args.q != q:
            raise SystemExit(f"--q {args.q} contradicts --target {key} (q = {q})")
        name = key
    else:
        if args.p is None or args.q is None:
            raise SystemExit("give --target NAME, or both --p P and --q Q")
        p, q = args.p, args.q
        name = f"C_{p}:C_{q}"

    derived = configure(p, q, args.r, name)
    if recorded_root is not None and ROOT != recorded_root:
        raise SystemExit(
            f"derived r = {ROOT} contradicts the recorded r = {recorded_root} "
            f"for target {name}"
        )

    print(
        f"target {GROUP_NAME}: p={MODULUS}, q={PHASES}, r={ROOT}, "
        f"<r>={POWERS} (as r^0..r^{PHASES-1}), |G|={MODULUS*PHASES}, "
        f"alphabet={len(SIGMA)} letters"
        + (" [recorded r confirmed]" if recorded_root is not None else ""),
        flush=True,
    )
    mutation_length = args.mutation_length
    if mutation_length is None:
        mutation_length = min(args.exhaustive_length, 3)
    print(
        f"limits: exhaustive-length={args.exhaustive_length}, sweep={args.sweep}, "
        f"max-length={args.max_length}, mutation-length={mutation_length}, "
        f"witness-length={args.witness_length}",
        flush=True,
    )

    started = time.time()
    section1(derived)
    patterns, pattern_results = section2()
    section3(patterns, pattern_results)
    section3b()
    combinations = section4()
    section5(combinations, args.exhaustive_length, args.sweep, args.max_length)
    section6(combinations, mutation_length, args.witness_length)

    row = LEDGER_ROWS.get(GROUP_NAME)
    decided = False
    verdict_status = 0
    if not args.skip_section7:
        transcription_length = args.section7_transcription_length
        if transcription_length is None:
            transcription_length = 3 if len(SIGMA) ** 3 <= 30000 else 2
        checks, decided = section7(
            combinations,
            row or f"UNREGISTERED-{GROUP_NAME}",
            transcription_length,
            args.section7_sweep,
            args.section7_cap,
        )
        if not checks:
            pass
        elif row is None:
            print(
                "  NOTE: no ledger row is registered for this target, so no "
                "verdict is written; a verdict naming an id the ledger does not "
                "carry is an orphan.",
                flush=True,
            )
        else:
            # Opt-in on purpose.  A verdict file is evidence for a COMPUTED
            # row, and no row here can be COMPUTED while 7(c) is a sample: the
            # chain from section 5's own function to the fibre still has a
            # sampled link.  Committing one anyway produces exactly the orphan
            # `lint_claims.py` refuses -- a real-looking file that nothing in
            # scripts/ci/ regenerates, since the four targets together take
            # about half an hour and cannot run in check.sh.  The checks are
            # still computed and printed; only the file is withheld.
            if args.write_verdict:
                path = Path(args.verdict_path) if args.verdict_path else (
                    Path(__file__).resolve().parents[2]
                    / "data"
                    / "verdicts"
                    / "metacyclic_full_alphabet.json"
                )
                verdict_status = record_verdict(checks, row, path)
            else:
                print(
                    "  verdict: computed but not written (pass --write-verdict). "
                    "The reconstruction step reaches COMPUTED; the row does not, "
                    "because 7(c) is sampled.",
                    flush=True,
                )

    if decided:
        print(
            f"\nCONCLUSION (the reconstruction is DECIDED; the row is still "
            f"EMPIRICAL, and the gap is named at the end of this paragraph). "
            f"The aperiodicity of every "
            f"pattern-conditioned cut over the full {len(SIGMA)}-letter alphabet "
            f"of {GROUP_NAME} is COMPUTED -- each candidate's transition monoid "
            "is enumerated completely. The reconstruction of the identity fibre "
            "is no longer checked on a sample: section 7 BFSes the product of "
            "the certified-feature machine with the group element itself and "
            "checks the agreement at every reachable state, so it holds on every "
            "word, with no length bound. Two things this still does NOT do. It "
            "is not a proof of HeightOneForGroup "
            f"({GROUP_NAME}): no height-one regular expression is built or "
            "compiled here, as it was for the two-generator cases, and no "
            "language equivalence is decided. And section 7 decides a machine, "
            "not the text of section 5's function: that the two agree is section "
            "7(c), which is a bounded comparison and is recorded as one.",
            flush=True,
        )
        print(f"runtime: {time.time()-started:.1f}s", flush=True)
        return verdict_status

    print(
        f"\nCONCLUSION (EMPIRICAL, and the two halves differ): the aperiodicity "
        f"of every pattern-conditioned cut over the full {len(SIGMA)}-letter "
        f"alphabet of {GROUP_NAME} is COMPUTED -- the transition monoid of each "
        "candidate is enumerated completely, with no sampling and no length "
        "bound. The reconstruction of the identity fibre is not: it is checked "
        "exhaustively only up to the exhaustive-length above and then on a "
        "sample, so it can refute and cannot establish, and it caps this run at "
        "EMPIRICAL. That cap is the whole content of the 2026-07-25 retraction "
        "of A4-FULL-01, which said COMPUTED while its last step was agreement "
        "on short and random words. Together with FULL-ALPH-RED-01 this is "
        f"evidence for HeightOneForGroup ({GROUP_NAME}) and NOT a proof: no "
        "height-one regular expression is built or compiled here, as it was for "
        "the two-generator cases, and no language equivalence is decided.",
        flush=True,
    )
    print(f"runtime: {time.time()-started:.1f}s", flush=True)
    # A section 7 that ran and did not decide is a failure of this script, not a
    # quieter kind of success: it means either the BFS found a word where the
    # reconstruction is wrong, or it hit its cap. `--skip-section7` is the only
    # way to reach the EMPIRICAL conclusion above with status 0.
    return 0 if args.skip_section7 else max(1, verdict_status)


if __name__ == "__main__":
    raise SystemExit(main())
