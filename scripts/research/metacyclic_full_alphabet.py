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
reconstruction of the identity fibre end to end.  The output is deterministic
and the evidence level is EMPIRICAL: section 2 is exhaustive, but the
reconstruction in section 5 is checked on bounded and sampled words, and a
row is capped by its weakest step.  Nothing here is a formal proof of
`HeightOneForGroup (C_p : C_q)` for any `(p, q)`: certifying the cuts and
solving the linear system is not a language equivalence, and no regular
expression of height one is built or compiled here.

Controls.  Sections 2 and 6 exist because the positive path of this computation
had never been executed for any group before the `C_7 : C_3` script: an
"everything passed" report and a judge that cannot say no are indistinguishable
outputs.  Section 2 runs the same-letter pure-power patterns, which must FAIL,
before trusting the ones that pass; that control is printed *before* the
candidate-failure exit, so it is reported even on a group where the candidates
themselves fail.  Section 6 mutates every solved coefficient and requires the
reconstruction of section 5 to break, reports the membership base rate so that
section 5 cannot be passing on a near-constant predicate, and exhibits a pair of
words that letter counts alone cannot separate.

The whole-script control is `--target F_20`, which must FAIL in section 2 with
0 certified patterns out of 291, reproducing `F20-FULL-OBS-01`.  If this script
ever certifies `F_20`, that is an implementation bug, not a breakthrough.
"""

from __future__ import annotations

import argparse
import itertools
import random
import time
from collections import defaultdict, deque
from dataclasses import dataclass


# name -> (p, q, recorded r).  The recorded r is asserted against the derived one.
TARGETS = {
    "C_7:C_3": (7, 3, 2),
    "C_13:C_3": (13, 3, 3),
    "C_11:C_5": (11, 5, 3),
    "C_19:C_3": (19, 3, 7),
    "F_20": (5, 4, 2),
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
    order = 1
    value = a % p
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
        fail(
            6,
            "some perturbed combinations still reproduce the fibre: "
            f"{survivors[:5]} -- section 5 is not sensitive to the coefficients",
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
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
