#!/usr/bin/env python3
"""Full-alphabet stage-2 computation for C_7 : C_3, the order-21 group.

`C_7 : C_3` is realized as the subgroup of `AGL(1,7)` on which the linear part
ranges over the cube roots of unity `{1, 2, 4} = <2> <= (Z/7)^*`:

    (a, b) . (a', b') = (a a', a' b + b')      # apply the left factor first

with `a` in `{1,2,4}` and `b` in `Z/7`.  This is the unique non-abelian group of
order 21, `<x, y | x^7 = y^3 = 1, y x y^-1 = x^2>`, verified in section 1.

Why this group, and why now.  `FRONTIER-ORD20-01` lists six non-abelian groups
of order at most 31 outside the class covered by the audited literature;
`C_7 : C_3` is the third of them and the smallest of odd order.  `F20-FULL-OBS-01`
showed that the multi-mover mechanism of `RESULTS.md` §5.5 fails on the full
20-letter alphabet of `F_20`, and localized the failure to the phase group being
`Z/4`, which is *composite*: the `eps = 2` letters have phase orbit `{0, 2}`, a
proper subgroup, so they bounce `1 <-> 3` forever without meeting the cut phase.
Here the phase group is `Z/3`, which is *prime*, so every non-zero `eps`
generates it and that failure mode cannot arise.  The order-21 group is larger
than `F_20` yet is predicted to be easier, and this script tests exactly that
prediction.

The script certifies the pattern-conditioned token languages exactly, builds the
forward/backward GF(7) system, solves for the `beta` functional, and checks the
reconstruction of the identity fibre end to end.  The output is deterministic
and the evidence level is COMPUTED.  Nothing here is a formal proof of
`HeightOneForGroup (C_7 : C_3)`.

Controls.  Sections 2 and 6 exist because the positive path of this computation
had never been executed for any group before this script: an "everything passed"
report and a judge that cannot say no are indistinguishable outputs.  Section 2
runs the same-letter pure-power patterns, which must FAIL, before trusting the
288 that pass.  Section 6 mutates every solved coefficient and requires the
reconstruction of section 5 to break, reports the membership base rate so that
section 5 cannot be passing on a near-constant predicate, and exhibits a pair of
words that letter counts alone cannot separate.
"""

from __future__ import annotations

import argparse
import itertools
import random
import time
from collections import defaultdict, deque
from dataclasses import dataclass


MODULUS = 7
PHASES = 3
POWERS_OF_TWO = (1, 2, 4)
IDENTITY = (1, 0)


def compose(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    """Apply ``left`` first and ``right`` second."""
    alpha, beta = left
    alpha_prime, beta_prime = right
    return (
        alpha * alpha_prime % MODULUS,
        (alpha_prime * beta + beta_prime) % MODULUS,
    )


SIGMA = tuple(
    (POWERS_OF_TWO[epsilon], beta)
    for epsilon in range(PHASES)
    for beta in range(MODULUS)
)
EPSILON = {g: POWERS_OF_TWO.index(g[0]) for g in SIGMA}
NONMOVERS = tuple(g for g in SIGMA if EPSILON[g] == 0)
MOVERS = tuple(g for g in SIGMA if EPSILON[g] != 0)
CONTRIBUTING = tuple(g for g in SIGMA if g[1] != 0)


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
        beta = (beta + letter[1] * POWERS_OF_TWO[suffix_phase]) % MODULUS
        suffix_phase = (suffix_phase + EPSILON[letter]) % PHASES
    return POWERS_OF_TWO[total_phase], beta


def prefix_coordinates(word: tuple[tuple[int, int], ...]) -> tuple[int, int]:
    phase = 0
    beta = 0
    for letter in word:
        beta = (beta + letter[1] * POWERS_OF_TWO[phase]) % MODULUS
        phase = (phase + EPSILON[letter]) % PHASES
    return POWERS_OF_TWO[phase], beta


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
    return FeatureData(
        total_phase=phase,
        first=word[0] if word else None,
        last=word[-1] if word else None,
        letter_counts=dict(letter_counts),
        base_cuts=tuple(arrivals),
        nonmover_events=dict(nonmover_events),
        pair_events=dict(pair_events),
    )


# ---------------- GF(7) linear algebra ----------------


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
    group, i.e. when ``eps != 0`` and the phase group has no element of order
    dividing 2 -- automatic for the prime group Z/3, and the point where the
    ``Z/4`` case of `F_20` degenerates.  The last row is the total count of g.
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
    """Express ``sum_p 2^p x_p`` as a GF(7) combination of the available rows."""
    rows, labels = mover_matrix(epsilon)
    target = POWERS_OF_TWO + (0,) * PHASES
    transpose = tuple(
        tuple(row[column] for row in rows) for column in range(2 * PHASES)
    )
    coefficients = solve_modp(transpose, target)
    return rows, labels, coefficients


def mover_rhs(forward, backward, letter):
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
            POWERS_OF_TWO[phase] * forward.nonmover_count(letter, phase)
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


def section1() -> None:
    print("=== 1. group and coordinate checks ===", flush=True)
    if len(SIGMA) != 21 or len(NONMOVERS) != 7 or len(MOVERS) != 14:
        fail(1, "incorrect alphabet partition")
    if sorted(POWERS_OF_TWO) != [1, 2, 4] or pow(2, 3, MODULUS) != 1:
        fail(1, "the linear part is not the cube roots of unity mod 7")

    # closure, associativity, identity, inverses on the full 21 elements
    elements = SIGMA
    for left in elements:
        if compose(left, IDENTITY) != left or compose(IDENTITY, left) != left:
            fail(1, "identity law")
        if not any(compose(left, right) == IDENTITY for right in elements):
            fail(1, f"no inverse for {left}")
        for right in elements:
            if compose(left, right) not in elements:
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

    # presentation <x, y | x^7, y^3, y x y^-1 = x^2>
    x = (1, 1)
    y = (2, 0)
    def power_of(g, k):
        result = IDENTITY
        for _ in range(k):
            result = compose(result, g)
        return result
    if power_of(x, 7) != IDENTITY or power_of(x, 3) == IDENTITY:
        fail(1, "x does not have order 7")
    if power_of(y, 3) != IDENTITY or y == IDENTITY:
        fail(1, "y does not have order 3")
    y_inverse = next(g for g in elements if compose(y, g) == IDENTITY)
    conjugate = compose(compose(y_inverse, x), y)  # left factor applied first
    if conjugate != power_of(x, 2) and conjugate != power_of(x, 4):
        fail(1, f"conjugation relation is neither x^2 nor x^4: {conjugate}")
    generated = {IDENTITY}
    frontier = [IDENTITY]
    while frontier:
        current = frontier.pop()
        for generator in (x, y):
            product = compose(current, generator)
            if product not in generated:
                generated.add(product)
                frontier.append(product)
    if len(generated) != 21:
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
        "  PASS: 21 elements, non-abelian, associative, "
        "<x,y | x^7, y^3, y x y^-1 = x^2> with <x,y> = the whole group; "
        f"21 letters, non-movers=7, movers=14; coordinate formula exhaustive "
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
    if failures:
        fail(2, f"{len(failures)} candidate patterns are not aperiodic")

    # POSITIVE CONTROL on the judge.  The same-letter pure-power patterns are
    # excluded from the candidate list precisely because RESULTS.md 5.5 records
    # that they break aperiodicity for A_4.  If they certified here too, the
    # judge would be answering "aperiodic" unconditionally and the 288 OK rows
    # above would carry no information.
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


def section4():
    print("\n=== 4. GF(7) rank and solved beta combination ===", flush=True)
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
                POWERS_OF_TWO[phase] * vector[phase] for phase in range(PHASES)
            ) % MODULUS
            mismatches += left != right
        if mismatches:
            fail(4, f"eps={epsilon}: solved combination fails on random vectors")
        print(
            f"  eps={epsilon}: rank={rank}/{2*PHASES}; "
            f"sum_p 2^p*x_p = {' + '.join(terms) if terms else '0'} mod 7 "
            "(verified on 5000 random (x,n) vectors)",
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


def section6(combinations, exhaustive_length) -> None:
    print("\n=== 6. negative controls ===", flush=True)

    # (a) mutation test: perturb each solved coefficient and require breakage.
    words = list(all_words(min(exhaustive_length, 3)))
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
    witness = minimal_count_witness(4)
    if witness is None:
        fail(6, "no count-only witness found through length 4")
    left, right = witness
    print(
        "  (b) counts alone are insufficient -- same phase, endpoints and "
        f"letter counts mod 7, different membership (length {len(left)}):",
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
        "--exhaustive-length",
        type=int,
        default=3,
        help="exhaustive reconstruction up to this word length (default 3 = "
        "9261 words; 4 is 194481 words and takes minutes)",
    )
    parser.add_argument("--sweep", type=int, default=20000)
    parser.add_argument("--max-length", type=int, default=400)
    args = parser.parse_args()

    started = time.time()
    section1()
    patterns, pattern_results = section2()
    section3(patterns, pattern_results)
    combinations = section4()
    section5(combinations, args.exhaustive_length, args.sweep, args.max_length)
    section6(combinations, args.exhaustive_length)
    print(
        "\nCONCLUSION (COMPUTED): every pattern-conditioned cut over the full "
        "21-letter alphabet of C_7 : C_3 is aperiodic, and the certified "
        "features determine the identity fibre exactly on every word tested. "
        "Together with FULL-ALPH-RED-01 this is computational evidence for "
        "HeightOneForGroup (C_7 : C_3); it is NOT a formal proof -- the "
        "regular expression of height one has not been built or compiled here, "
        "as it was for the two-generator cases.",
        flush=True,
    )
    print(f"runtime: {time.time()-started:.1f}s", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
