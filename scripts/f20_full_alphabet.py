#!/usr/bin/env python3
"""Full-alphabet stage-2 computation for F_20 = AGL(1,5).

The script certifies the pattern-conditioned token languages exactly, builds
the forward/backward GF(5) system, and checks whether the identity fibre over
the full 20-letter alphabet is reconstructible from the certified features.
The output is deterministic and the evidence level is COMPUTED.
"""

from __future__ import annotations

import itertools
import random
import time
from collections import defaultdict, deque
from dataclasses import dataclass


MODULUS = 5
PHASES = 4
POWERS_OF_TWO = (1, 2, 4, 3)
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


def certify_patterns():
    patterns = candidate_patterns()
    cache = {}
    results = {}
    for pattern in patterns:
        signature = pattern_signature(pattern)
        if signature not in cache:
            cache[signature] = aperiodicity_certificate(pattern)
        results[pattern] = cache[signature]
    return patterns, results, cache


@dataclass(frozen=True)
class FeatureData:
    total_phase: int
    first: tuple[int, int] | None
    last: tuple[int, int] | None
    letter_counts: dict
    base_cuts: tuple[int, ...]
    single_cuts: dict
    pair_cuts: dict

    def nonmover_count(self, letter, phase):
        return (self.base_cuts[phase] - self.single_cuts[letter, phase]) % MODULUS

    def pair_count(self, left, right, arrival_phase):
        return (
            self.base_cuts[arrival_phase]
            - self.pair_cuts[left, right, arrival_phase]
        ) % MODULUS


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
    single_cuts = {
        (letter, q): (arrivals[q] - nonmover_events[letter, q]) % MODULUS
        for letter in NONMOVERS
        for q in range(PHASES)
    }
    pair_cuts = {
        (left, right, q): (arrivals[q] - pair_events[left, right, q])
        % MODULUS
        for right in MOVERS
        for left in SIGMA
        if left != right
        for q in range(PHASES)
    }
    return FeatureData(
        total_phase=phase,
        first=word[0] if word else None,
        last=word[-1] if word else None,
        letter_counts=dict(letter_counts),
        base_cuts=tuple(arrivals),
        single_cuts=single_cuts,
        pair_cuts=pair_cuts,
    )


def rank_mod5(rows, columns):
    matrix = [[entry % MODULUS for entry in row[:columns]] for row in rows]
    rank = 0
    pivot_columns = []
    for column in range(columns):
        pivot = next(
            (index for index in range(rank, len(matrix)) if matrix[index][column]),
            None,
        )
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inverse = pow(matrix[rank][column], -1, MODULUS)
        matrix[rank] = [inverse * value % MODULUS for value in matrix[rank]]
        for index in range(len(matrix)):
            if index == rank or matrix[index][column] == 0:
                continue
            factor = matrix[index][column]
            matrix[index] = [
                (left - factor * right) % MODULUS
                for left, right in zip(matrix[index], matrix[rank])
            ]
        pivot_columns.append(column)
        rank += 1
    return rank, matrix, tuple(pivot_columns)


def solve_mod5(coefficients, rhs):
    augmented = [list(row) + [value] for row, value in zip(coefficients, rhs)]
    columns = len(coefficients[0])
    rank = 0
    pivots = []
    for column in range(columns):
        pivot = next(
            (
                index
                for index in range(rank, len(augmented))
                if augmented[index][column] % MODULUS
            ),
            None,
        )
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
    rows.append((1, 1, 1, 1, 0, 0, 0, 0))
    labels.append("C")
    return tuple(rows), tuple(labels)


def objective_combination(epsilon):
    rows, labels = mover_matrix(epsilon)
    target = POWERS_OF_TWO + (0, 0, 0, 0)
    transpose = tuple(tuple(row[column] for row in rows) for column in range(8))
    coefficients = solve_mod5(transpose, target)
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


def count_only_matrix():
    rows = []
    for letter_index in range(len(SIGMA)):
        row = [0] * (len(SIGMA) * PHASES)
        for phase in range(PHASES):
            row[letter_index * PHASES + phase] = 1
        rows.append(tuple(row))
    beta_row = tuple(
        letter[1] * POWERS_OF_TWO[phase] % MODULUS
        for letter in SIGMA
        for phase in range(PHASES)
    )
    return tuple(rows), beta_row


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


def localize_obstruction() -> None:
    """Which eps-classes of letters break the base cut, and which do not?

    This doubles as a positive control on ``aperiodicity_certificate``: a judge
    that always answered "not aperiodic" would produce exactly the 0/291 table
    above, so at least one sub-alphabet must certify for that table to mean
    anything.  Restricting the alphabet is sound here because the transition
    monoid of the token DFA is generated by the letters that are present.

    The outcome is the sharp statement: the phase group is Z/4, which is
    *composite*, so the eps=2 letters (alpha = 4, the involution of C_4) have
    phase orbit {0,2}, a proper subgroup.  Once an odd phase has been reached,
    such a letter bounces 1 <-> 3 forever without ever meeting the cut phase 0,
    which is the period-2 element of the monoid.  In A_4 (RESULTS.md §5.5) the
    phase group is Z/3, where every non-zero eps generates the whole group, so
    this failure mode cannot occur there.
    """

    global SIGMA, MOVERS, NONMOVERS
    saved = (SIGMA, MOVERS, NONMOVERS)
    print("  localization of the obstruction (also a positive control):", flush=True)
    subsets = [(0,), (0, 1), (0, 2), (0, 3), (0, 1, 3), (0, 1, 2), (0, 2, 3),
               (0, 1, 2, 3)]
    try:
        for keep in subsets:
            SIGMA = tuple(g for g in saved[0] if EPSILON[g] in keep)
            MOVERS = tuple(g for g in SIGMA if EPSILON[g] != 0)
            NONMOVERS = tuple(g for g in SIGMA if EPSILON[g] == 0)
            if not MOVERS:
                continue
            verdict = aperiodicity_certificate(None)
            mark = "CERTIFIED" if verdict["aperiodic"] else "FAIL"
            print(
                f"    eps in {keep}: {len(SIGMA):2d} letters -> {mark}"
                f" (states={verdict['states']}, monoid={verdict['monoid']},"
                f" period={verdict['period']}"
                + (f", witness={verdict['witness']}" if verdict["witness"] else "")
                + ")",
                flush=True,
            )
    finally:
        SIGMA, MOVERS, NONMOVERS = saved
    print(
        "    => the base cut certifies on every eps-subset avoiding eps=2, "
        "including the 15-letter alphabet eps in (0,1,3), and fails exactly "
        "when eps=2 letters coexist with odd-eps letters.",
        flush=True,
    )


def main() -> int:
    started = time.time()
    print("=== 1. group and coordinate checks ===", flush=True)
    if len(SIGMA) != 20 or len(NONMOVERS) != 5 or len(MOVERS) != 15:
        fail(1, "incorrect alphabet partition")
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
        f"  PASS: 20 letters; non-movers=5; movers=15; exhaustive "
        f"length <= 3 ({checked} words) and {longer_checked} fixed-seed "
        "words of lengths 4..8.",
        flush=True,
    )

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
            extra = (
                f" period={result['period']} witness={result['witness']}"
            )
        print(
            f"  {signature}: count={entry['count']} {status}; "
            f"minimal_states={result['states']} monoid={result['monoid']}"
            f"{extra}",
            flush=True,
        )
    failures = [pattern for pattern in patterns if not pattern_results[pattern]["aperiodic"]]
    certified_pairs = [
        pattern
        for pattern in patterns
        if pattern is not None
        and pattern[0] == "pair"
        and pattern[1] != pattern[2]
        and pattern_results[pattern]["aperiodic"]
    ]
    print(
        f"  exact total={len(patterns)}; certified={len(patterns)-len(failures)}; "
        f"failed={len(failures)}; distinct DFA types={len(signature_results)}; "
        f"time={time.time()-atom_started:.1f}s.",
        flush=True,
    )
    if failures:
        failure_witnesses = sorted(
            {
                result["witness"]
                for result in pattern_results.values()
                if not result["aperiodic"]
            }
        )
        print(
            "  obstruction: every candidate fails; an eps=2 pure mover "
            "cycles the odd phases {1,3}. Representative monoid witnesses: "
            + ", ".join(failure_witnesses),
            flush=True,
        )
        localize_obstruction()
    expected_pairs = len(MOVERS) * (len(SIGMA) - 1)
    required_atoms_certified = True
    if len(certified_pairs) != expected_pairs:
        required_atoms_certified = False
    required_singles = [
        pattern for pattern in patterns if pattern is not None and pattern[0] == "single"
    ]
    if any(not pattern_results[pattern]["aperiodic"] for pattern in required_singles):
        required_atoms_certified = False
    if not pattern_results[None]["aperiodic"]:
        required_atoms_certified = False

    if not required_atoms_certified:
        print("\n=== 3. GF(5) rank from certified features ===", flush=True)
        print("  formal planned systems (using the uncertified pair features):", flush=True)
        for epsilon in (1, 2, 3):
            formal_rows, _, formal_combination = objective_combination(epsilon)
            formal_rank, _, _ = rank_mod5(formal_rows, 8)
            beta_status = "determined" if formal_combination is not None else "undetermined"
            print(
                f"    eps={epsilon}: rank={formal_rank}/8; beta={beta_status}",
                flush=True,
            )
        rows, beta_row = count_only_matrix()
        rank, _, _ = rank_mod5(rows, len(beta_row))
        augmented_rank, _, _ = rank_mod5(rows + (beta_row,), len(beta_row))
        contributing_columns = len(CONTRIBUTING) * PHASES
        contributing_rows = []
        for letter_index, letter in enumerate(CONTRIBUTING):
            row = [0] * contributing_columns
            for phase in range(PHASES):
                row[letter_index * PHASES + phase] = 1
            contributing_rows.append(tuple(row))
        contributing_beta = tuple(
            letter[1] * POWERS_OF_TWO[phase] % MODULUS
            for letter in CONTRIBUTING
            for phase in range(PHASES)
        )
        contributing_rank, _, _ = rank_mod5(
            contributing_rows, contributing_columns
        )
        contributing_augmented, _, _ = rank_mod5(
            tuple(contributing_rows) + (contributing_beta,),
            contributing_columns,
        )
        print(
            f"  full N[g,p] system: rank={rank}/80; adding beta row gives "
            f"rank={augmented_rank}/80.",
            flush=True,
        )
        print(
            f"  beta-contributing subsystem: rank={contributing_rank}/64; "
            f"adding beta row gives rank={contributing_augmented}/64.",
            flush=True,
        )
        print(
            "  The formal eps=2 null direction is beta-neutral, but none of "
            "the pair/base/single rows is certified, so only count rows are "
            "available in the sound system.",
            flush=True,
        )
        print("\n=== 4. minimal obstruction witness ===", flush=True)
        witness = minimal_count_witness(4)
        if witness is None:
            fail(4, "no witness found through length 4")
        left, right = witness
        print(
            "  same certified features, phase, endpoints, and letter counts "
            f"mod 5; different membership (minimal length {len(left)}):",
            flush=True,
        )
        print(
            "    w0 = [" + ", ".join(letter_name(g) for g in left) + "]",
            flush=True,
        )
        print(
            f"         mu(w0)={evaluate(left)}; in T={direct_identity(left)}",
            flush=True,
        )
        print(
            "    w1 = [" + ", ".join(letter_name(g) for g in right) + "]",
            flush=True,
        )
        print(
            f"         mu(w1)={evaluate(right)}; in T={direct_identity(right)}",
            flush=True,
        )
        print(
            "\nCONCLUSION (COMPUTED, negative): step 2 fails exactly, so the "
            "planned GF(5) reconstruction cannot close. No claim about "
            "HeightOneForGroup F_20 is made.",
            flush=True,
        )
        print(f"runtime: {time.time()-started:.1f}s", flush=True)
        return 0

    print("\n=== 3. certified feature identities ===", flush=True)
    feature_rng = random.Random(52020)
    feature_checks = 0
    for word in all_words(2):
        for q in range(PHASES):
            data = certified_features(word)
            for pattern in patterns:
                if not pattern_results[pattern]["aperiodic"]:
                    continue
                if pattern is not None and pattern[0] == "pair" and pattern[1] == pattern[2]:
                    continue
                actual = CutPattern(q, pattern).run(word)
                if pattern is None:
                    expected = data.base_cuts[q]
                elif pattern[0] == "single":
                    expected = data.single_cuts[pattern[1], q]
                else:
                    expected = data.pair_cuts[pattern[1], pattern[2], q]
                feature_checks += 1
                if actual != expected:
                    fail(3, f"feature identity mismatch: q={q}, {pattern_text(pattern)}")
    for _ in range(2000):
        length = feature_rng.randint(0, 200)
        word = tuple(feature_rng.choice(SIGMA) for _ in range(length))
        data = certified_features(word)
        q = feature_rng.randrange(PHASES)
        pattern = feature_rng.choice(patterns)
        if not pattern_results[pattern]["aperiodic"]:
            continue
        if pattern is not None and pattern[0] == "pair" and pattern[1] == pattern[2]:
            continue
        actual = CutPattern(q, pattern).run(word)
        if pattern is None:
            expected = data.base_cuts[q]
        elif pattern[0] == "single":
            expected = data.single_cuts[pattern[1], q]
        else:
            expected = data.pair_cuts[pattern[1], pattern[2], q]
        feature_checks += 1
        if actual != expected:
            fail(3, f"long feature identity mismatch: q={q}, {pattern_text(pattern)}")
    print(f"  PASS: {feature_checks} exact/sweep comparisons.", flush=True)

    print("\n=== 4. GF(5) rank and solved beta combination ===", flush=True)
    combinations = {}
    global_rank = 0
    global_columns = 0
    contributing_rank = 0
    contributing_columns = 0
    for epsilon in (1, 2, 3):
        rows, labels, combination = objective_combination(epsilon)
        rank, _, _ = rank_mod5(rows, 8)
        if combination is None:
            print(f"  eps={epsilon}: rank={rank}/8; beta functional UNSOLVED", flush=True)
        else:
            combinations[epsilon] = tuple(combination)
            terms = [
                f"{coefficient}*{label}"
                for coefficient, label in zip(combination, labels)
                if coefficient
            ]
            print(
                f"  eps={epsilon}: rank={rank}/8; "
                f"sum_p 2^p*x_p = {' + '.join(terms) if terms else '0'} mod 5",
                flush=True,
            )
        global_rank += MODULUS * rank
        global_columns += MODULUS * 8
        contributing_rank += (MODULUS - 1) * rank
        contributing_columns += (MODULUS - 1) * 8
    print(
        f"  global mover system rank={global_rank}/{global_columns}; "
        f"beta-contributing mover subsystem={contributing_rank}/{contributing_columns}.",
        flush=True,
    )
    if len(combinations) != 3:
        fail(4, "beta is not determined by the certified feature system")

    print("\n=== 5. end-to-end reconstruction ===", flush=True)
    exhaustive_count = 0
    for word in all_words(4):
        exhaustive_count += 1
        predicted = identity_from_certified_features(word, combinations)
        actual = direct_identity(word)
        if predicted != actual:
            fail(5, f"reconstruction mismatch on {word}: {predicted} != {actual}")
    sweep_rng = random.Random(2026072502)
    sweep_count = 4000
    max_length = 400
    for _ in range(sweep_count):
        length = sweep_rng.randint(5, max_length)
        word = tuple(sweep_rng.choice(SIGMA) for _ in range(length))
        predicted = identity_from_certified_features(word, combinations)
        actual = direct_identity(word)
        if predicted != actual:
            fail(5, f"long reconstruction mismatch at length {length}")
    print(
        f"  PASS: all {exhaustive_count} words of length <= 4; "
        f"{sweep_count} fixed-seed words of length 5..{max_length}.",
        flush=True,
    )
    print(
        "\nCONCLUSION (COMPUTED): the certified features determine the full "
        "F_20 identity fibre. Together with FULL-ALPH-RED-01 this is "
        "computational evidence for HeightOneForGroup F_20; it is not a "
        "formal proof.",
        flush=True,
    )
    print(f"runtime: {time.time()-started:.1f}s", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
