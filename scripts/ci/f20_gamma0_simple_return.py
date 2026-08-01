#!/usr/bin/env python3
"""Exact audit of a new simple-first-return token over ``Gamma_0``.

Write ``Gamma_0 = {a,b,c,d}``, with phases ``0,1,2,3`` respectively.  The
candidate token language consists of the one-letter token ``a`` and all phase
walks which first return to phase zero without repeating a nonzero phase;
arbitrary ``a`` letters may occur between movers.  There are fifteen mover
skeletons.  Hence the language has an explicit star-free description as a
finite union of concatenations whose only unbounded gap is ``a*`` (star-free
over this alphabet).

All machine conclusions below are finite and exact: DFA minimization,
transition-monoid traversal, old-language product reachability, and the
two-letter equivalence use no word-length cutoff.  The displayed word ``bbdd``
is used only as a negative control for deleting the visited-phase hierarchy.
This script makes no claim about ``HeightOneForGroup F_20`` or even about the
height of the full identity fibre over ``Gamma_0``.
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
from dataclasses import dataclass
import itertools
from pathlib import Path
import sys
from typing import Hashable, Iterable

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.ci.f20_alph5_reduction import phase_element  # noqa: E402
from scripts.research import f20_subalphabet_obstruction as old  # noqa: E402


base = old.base

Letter = tuple[int, int]
State = Hashable

A = phase_element(0, 1)
B = phase_element(1, 0)
C = phase_element(2, 0)
D = phase_element(3, 0)

ALPHABET = (A, B, C, D)
TWO_LETTER_ALPHABET = (A, B)
MOVERS = (B, C, D)
LETTER_NAMES = {A: "a", B: "b", C: "c", D: "d"}


@dataclass(frozen=True)
class DFA:
    states: tuple[State, ...]
    transitions: dict[tuple[State, Letter], State]
    start: State
    accepting: frozenset[State]
    alphabet: tuple[Letter, ...]


def show_word(word: Iterable[Letter]) -> str:
    return "".join(LETTER_NAMES[letter] for letter in word)


def phase_walk(skeleton: Iterable[Letter]) -> tuple[int, ...]:
    phase = 0
    out = []
    for letter in skeleton:
        phase = (phase + base.EPSILON[letter]) % 4
        out.append(phase)
    return tuple(out)


def is_first_return(skeleton: tuple[Letter, ...]) -> bool:
    walk = phase_walk(skeleton)
    return bool(walk) and walk[-1] == 0 and 0 not in walk[:-1]


def has_distinct_nonzero_states(skeleton: tuple[Letter, ...]) -> bool:
    walk = phase_walk(skeleton)
    return is_first_return(skeleton) and len(set(walk[:-1])) == len(walk[:-1])


def simple_first_return_skeletons() -> tuple[tuple[Letter, ...], ...]:
    out: list[tuple[Letter, ...]] = []

    def visit(
        phase: int, visited: frozenset[int], word: tuple[Letter, ...]
    ) -> None:
        for mover in MOVERS:
            next_phase = (phase + base.EPSILON[mover]) % 4
            next_word = word + (mover,)
            if next_phase == 0:
                out.append(next_word)
            elif next_phase not in visited:
                visit(next_phase, visited | {next_phase}, next_word)

    visit(0, frozenset(), ())
    return tuple(out)


SKELETONS = simple_first_return_skeletons()
SKELETON_NAMES = tuple(show_word(skeleton) for skeleton in SKELETONS)

# One shortest distinguishing word per old base/single/pair language, in the
# exact order produced by ``old_patterns``.  These are fixed regression inputs,
# not the basis for deciding equivalence.
OLD_WITNESSES = (
    "bbdd",
    "a",
    "dab",
    "cbb",
    "bcb",
    "db",
    "cac",
    "bbc",
    "cc",
    "ddc",
    "bad",
    "bd",
    "dcd",
    "cdd",
)


def simple_first_return_dfa(
    alphabet: tuple[Letter, ...] = ALPHABET,
) -> DFA:
    start = ("start",)
    accept = ("accept",)
    dead = ("dead",)
    states: set[State] = {start, accept, dead}
    transitions: dict[tuple[State, Letter], State] = {}
    queue = deque([start])

    for letter in alphabet:
        transitions[accept, letter] = dead
        transitions[dead, letter] = dead

    while queue:
        state = queue.popleft()
        if state in (accept, dead):
            continue
        for letter in alphabet:
            if state == start:
                if letter == A:
                    next_state: State = accept
                else:
                    phase = base.EPSILON[letter]
                    next_state = (phase, frozenset({phase}))
            else:
                phase, visited = state
                if letter == A:
                    next_state = state
                else:
                    next_phase = (phase + base.EPSILON[letter]) % 4
                    if next_phase == 0:
                        next_state = accept
                    elif next_phase in visited:
                        next_state = dead
                    else:
                        next_state = (next_phase, visited | {next_phase})
            transitions[state, letter] = next_state
            if next_state not in states:
                states.add(next_state)
                queue.append(next_state)

    return DFA(
        states=tuple(states),
        transitions=transitions,
        start=start,
        accepting=frozenset({accept}),
        alphabet=alphabet,
    )


def reachable_states(dfa: DFA) -> frozenset[State]:
    seen = {dfa.start}
    queue = deque([dfa.start])
    while queue:
        state = queue.popleft()
        for letter in dfa.alphabet:
            target = dfa.transitions[state, letter]
            if target not in seen:
                seen.add(target)
                queue.append(target)
    return frozenset(seen)


def minimize_dfa(dfa: DFA) -> DFA:
    reachable = reachable_states(dfa)
    accepting = reachable & dfa.accepting
    rejecting = reachable - accepting
    partitions = [
        block for block in (frozenset(accepting), frozenset(rejecting)) if block
    ]

    while True:
        block_of = {
            state: index
            for index, block in enumerate(partitions)
            for state in block
        }
        refined = []
        for block in partitions:
            groups: dict[tuple[int, ...], set[State]] = defaultdict(set)
            for state in block:
                signature = tuple(
                    block_of[dfa.transitions[state, letter]]
                    for letter in dfa.alphabet
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
    states = tuple(range(len(partitions)))
    transitions = {
        (index, letter): block_of[
            dfa.transitions[next(iter(block)), letter]
        ]
        for index, block in enumerate(partitions)
        for letter in dfa.alphabet
    }
    return DFA(
        states=states,
        transitions=transitions,
        start=block_of[dfa.start],
        accepting=frozenset(block_of[state] for state in dfa.accepting),
        alphabet=dfa.alphabet,
    )


def accepts(dfa: DFA, word: Iterable[Letter]) -> bool:
    state = dfa.start
    for letter in word:
        state = dfa.transitions[state, letter]
    return state in dfa.accepting


def compose_transformation(
    left: tuple[int, ...], right: tuple[int, ...]
) -> tuple[int, ...]:
    return tuple(right[left[index]] for index in range(len(left)))


def transformation_power_data(transformation: tuple[int, ...]) -> tuple[int, int]:
    seen: dict[tuple[int, ...], int] = {}
    power = transformation
    exponent = 1
    while power not in seen:
        seen[power] = exponent
        power = compose_transformation(power, transformation)
        exponent += 1
    return seen[power], exponent - seen[power]


def transition_monoid_audit(dfa: DFA) -> dict[str, object]:
    if tuple(dfa.states) != tuple(range(len(dfa.states))):
        raise ValueError("transition monoids are enumerated only after minimization")

    generators = {
        tuple(dfa.transitions[state, letter] for state in dfa.states)
        for letter in dfa.alphabet
    }
    identity = tuple(dfa.states)
    monoid = {identity}
    queue = deque([identity])
    while queue:
        current = queue.popleft()
        for generator in generators:
            product = compose_transformation(current, generator)
            if product not in monoid:
                monoid.add(product)
                queue.append(product)

    power_data = tuple(
        transformation_power_data(transformation) for transformation in monoid
    )
    periods = tuple(period for _, period in power_data)
    indices = tuple(index for index, _ in power_data)
    return {
        "transition_monoid": len(monoid),
        "aperiodic": max(periods) == 1,
        "maximum_period": max(periods),
        "maximum_stabilization_index": max(indices),
        "stabilization_index_distribution": dict(sorted(Counter(indices).items())),
    }


def generator_period(dfa: DFA, letter: Letter) -> int:
    transformation = tuple(
        dfa.transitions[state, letter] for state in dfa.states
    )
    return transformation_power_data(transformation)[1]


def complete_product_comparison(
    left: DFA, right: DFA
) -> tuple[bool, tuple[Letter, ...] | None, int]:
    if left.alphabet != right.alphabet:
        raise ValueError("product comparison requires the same ordered alphabet")

    start = (left.start, right.start)
    seen = {start}
    queue = deque([start])
    parent: dict[tuple[State, State], tuple[State, State] | None] = {start: None}
    edge: dict[tuple[State, State], Letter] = {}
    first_mismatch = None

    while queue:
        state = queue.popleft()
        left_state, right_state = state
        if first_mismatch is None and (
            (left_state in left.accepting) != (right_state in right.accepting)
        ):
            first_mismatch = state
        for letter in left.alphabet:
            target = (
                left.transitions[left_state, letter],
                right.transitions[right_state, letter],
            )
            if target not in seen:
                seen.add(target)
                parent[target] = state
                edge[target] = letter
                queue.append(target)

    witness = None
    if first_mismatch is not None:
        reversed_word = []
        current = first_mismatch
        while parent[current] is not None:
            reversed_word.append(edge[current])
            current = parent[current]  # type: ignore[assignment]
        witness = tuple(reversed(reversed_word))
    return first_mismatch is None, witness, len(seen)


def old_patterns() -> tuple[object, ...]:
    return (
        None,
        ("single", A),
        *(("pair", left, right) for right in MOVERS for left in ALPHABET),
    )


def old_pattern_dfa(pattern: object) -> DFA:
    states, transitions, start, accepting = base.token_dfa(pattern)
    return DFA(
        states=states,
        transitions=transitions,
        start=start,
        accepting=frozenset(accepting),
        alphabet=ALPHABET,
    )


def two_letter_reference_dfa() -> DFA:
    """DFA for ``a union b a* b a* b a* b``."""

    states = tuple(range(6))
    transitions = {
        (0, A): 4,
        (0, B): 1,
        (1, A): 1,
        (1, B): 2,
        (2, A): 2,
        (2, B): 3,
        (3, A): 3,
        (3, B): 4,
        (4, A): 5,
        (4, B): 5,
        (5, A): 5,
        (5, B): 5,
    }
    return DFA(
        states=states,
        transitions=transitions,
        start=0,
        accepting=frozenset({4}),
        alphabet=TWO_LETTER_ALPHABET,
    )


def skeleton_audit() -> dict[str, object]:
    first_excluded = None
    for length in range(1, 5):
        for word in itertools.product(MOVERS, repeat=length):
            if is_first_return(word) and not has_distinct_nonzero_states(word):
                first_excluded = word
                break
        if first_excluded is not None:
            break
    return {
        "skeletons": len(SKELETONS),
        "all_first_return": all(is_first_return(word) for word in SKELETONS),
        "all_nonzero_states_distinct": all(
            has_distinct_nonzero_states(word) for word in SKELETONS
        ),
        "first_excluded_first_return": show_word(first_excluded or ()),
    }


def candidate_audit() -> dict[str, object]:
    raw = simple_first_return_dfa()
    minimized = minimize_dfa(raw)
    return {
        "reachable_states": len(reachable_states(raw)),
        "minimal_states": len(minimized.states),
        "finite_star_free_construction": len(SKELETONS) == 15,
        **transition_monoid_audit(minimized),
    }


def old_cut_audit() -> dict[str, object]:
    candidate = minimize_dfa(simple_first_return_dfa())
    observed_witnesses = []
    product_states = []
    inequivalent = 0
    all_witnesses_distinguish = True
    all_old_nonaperiodic = True

    with old.alphabet(ALPHABET):
        for pattern in old_patterns():
            old_dfa = minimize_dfa(old_pattern_dfa(pattern))
            equivalent, witness, reachable = complete_product_comparison(
                candidate, old_dfa
            )
            inequivalent += int(not equivalent)
            product_states.append(reachable)
            observed_witnesses.append(show_word(witness or ()))
            all_witnesses_distinguish &= witness is not None and (
                accepts(candidate, witness) != accepts(old_dfa, witness)
            )
            all_old_nonaperiodic &= not transition_monoid_audit(old_dfa)[
                "aperiodic"
            ]

    return {
        "languages": len(old_patterns()),
        "inequivalent": inequivalent,
        "product_reachable_states": sum(product_states),
        "product_state_range": (min(product_states), max(product_states)),
        "observed_witnesses": tuple(observed_witnesses),
        "witnesses_match": tuple(observed_witnesses) == OLD_WITNESSES,
        "all_witnesses_distinguish": all_witnesses_distinguish,
        "all_old_nonaperiodic": all_old_nonaperiodic,
    }


def two_letter_audit() -> dict[str, object]:
    candidate = minimize_dfa(simple_first_return_dfa(TWO_LETTER_ALPHABET))
    reference = minimize_dfa(two_letter_reference_dfa())
    equivalent, witness, product_states = complete_product_comparison(
        candidate, reference
    )
    monoid = transition_monoid_audit(candidate)
    return {
        "candidate_minimal_states": len(candidate.states),
        "reference_minimal_states": len(reference.states),
        "product_reachable_states": product_states,
        "equivalent": equivalent,
        "counterexample": show_word(witness or ()),
        "transition_monoid": monoid["transition_monoid"],
        "aperiodic": monoid["aperiodic"],
    }


def first_return_control_audit() -> dict[str, object]:
    candidate = minimize_dfa(simple_first_return_dfa())
    with old.alphabet(ALPHABET):
        natural = minimize_dfa(old_pattern_dfa(None))
    monoid = transition_monoid_audit(natural)
    witness = (B, B, D, D)
    return {
        "minimal_states": len(natural.states),
        "transition_monoid": monoid["transition_monoid"],
        "maximum_period": monoid["maximum_period"],
        "periodic_letter": "c",
        "periodic_letter_period": generator_period(natural, C),
        "hierarchy_witness": show_word(witness),
        "natural_accepts_witness": accepts(natural, witness),
        "candidate_accepts_witness": accepts(candidate, witness),
    }


def audit() -> dict[str, object]:
    return {
        "skeletons": skeleton_audit(),
        "candidate": candidate_audit(),
        "old_cut": old_cut_audit(),
        "two_letter": two_letter_audit(),
        "control": first_return_control_audit(),
    }


def main() -> int:
    result = audit()
    expected = {
        "skeletons": {
            "skeletons": 15,
            "all_first_return": True,
            "all_nonzero_states_distinct": True,
            "first_excluded_first_return": "bbdd",
        },
        "candidate": {
            "reachable_states": 15,
            "minimal_states": 15,
            "finite_star_free_construction": True,
            "transition_monoid": 50,
            "aperiodic": True,
            "maximum_period": 1,
            "maximum_stabilization_index": 5,
            "stabilization_index_distribution": {1: 3, 2: 36, 3: 5, 4: 4, 5: 2},
        },
        "old_cut": {
            "languages": 14,
            "inequivalent": 14,
            "product_reachable_states": 331,
            "product_state_range": (19, 26),
            "observed_witnesses": OLD_WITNESSES,
            "witnesses_match": True,
            "all_witnesses_distinguish": True,
            "all_old_nonaperiodic": True,
        },
        "two_letter": {
            "candidate_minimal_states": 6,
            "reference_minimal_states": 6,
            "product_reachable_states": 6,
            "equivalent": True,
            "counterexample": "",
            "transition_monoid": 16,
            "aperiodic": True,
        },
        "control": {
            "minimal_states": 6,
            "transition_monoid": 62,
            "maximum_period": 2,
            "periodic_letter": "c",
            "periodic_letter_period": 2,
            "hierarchy_witness": "bbdd",
            "natural_accepts_witness": True,
            "candidate_accepts_witness": False,
        },
    }
    if result != expected:
        print("F20 Gamma0 simple-first-return token: FAIL")
        print(result)
        return 1

    print(
        "F20 Gamma0 simple-first-return token: PASS; "
        "15 skeletons, 15-state minimal DFA, 50-element aperiodic monoid"
    )
    print(
        "old cuts: 14/14 inequivalent by complete product reachability; "
        "two-letter restriction equals the F20-STD-01 token"
    )
    print(
        "negative control: deleting the visited-phase hierarchy gives "
        "the 6-state first-return DFA with c of period 2 (witness bbdd)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
