#!/usr/bin/env python3
"""Finite checks used by the height-one proof for ``C_7 : C_3``.

This module deliberately checks only finite statements.  It does not turn the
Schuetzenberger theorem, the token factorisation argument, or
``C7C3-IDENT-01`` into a computation.  Its jobs are narrower:

* exhaust the transition monoid of every first- and post-cut token DFA used by
  the proof and verify aperiodicity;
* verify, by exact DFA product reachability, the mod-seven token
  factorisation against the direct cut counter; and
* audit that all 57 arithmetic atoms, including the reversal atoms, are
  covered by those token checks.

There is no bounded-word or random-word path in this file.  The command-line
entry point records the traversals through :mod:`tools.verdict`.
"""

from __future__ import annotations

import sys
from collections import Counter, deque
from pathlib import Path
from typing import Hashable, Iterable


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.research import c7c3_identity_proof as c7  # noqa: E402
from tools.regex_cert import (  # noqa: E402
    DFA,
    _concat as dfa_concat,
    _product as dfa_product,
    _star as dfa_star,
)
from tools.verdict import Control, Run, conjunction, exhaustive  # noqa: E402


VERDICT_FILE = ROOT / "data" / "verdicts" / "c7c3_height_one.json"
CLAIM_ID = "C7C3-H1-FINITE-CORE-01"
RUN = Run("scripts/ci/c7c3_height_one.py")


def _patterns() -> tuple[tuple, ...]:
    """The 17 concrete signatures used before coefficient cancellation."""

    anti = tuple(("anti", letter) for letter in c7.MOVERS)
    sets = tuple(("set", letters) for letters in c7.BIT_SETS)
    patterns = anti + sets
    if len(patterns) != 17 or len(set(map(repr, patterns))) != 17:
        raise AssertionError("the C7:C3 token family is not 14 anti + 3 set patterns")
    return patterns


def _cut_component_dfa(
    q: int,
    pattern: tuple,
    *,
    start_phase: int,
    stop_at_cut: bool,
) -> DFA:
    """DFA for reaching the first cut, or for avoiding every cut.

    ``start_phase=0`` gives the initial component ``O``/``V0``.  A cut resets
    the private previous-letter register and leaves phase ``q``, so
    ``start_phase=q`` gives the repeatable post-cut component ``X``/``V``.
    When ``stop_at_cut`` is true the word must end at its first cut; when false
    every word with no cut is accepted.
    """

    cut = c7.Cut(q, pattern)
    accept_cut = ("accept-cut",)
    dead = ("dead",)
    start = (start_phase, None)
    states: set[Hashable] = {start, accept_cut, dead}
    transition: dict[tuple[Hashable, tuple[int, int]], Hashable] = {}
    frontier: deque[tuple[int, tuple[int, int] | None]] = deque([start])

    for terminal in (accept_cut, dead):
        for letter in c7.SIGMA:
            transition[(terminal, letter)] = dead

    while frontier:
        phase, previous = state = frontier.popleft()
        for letter in c7.SIGMA:
            next_phase = (phase + c7.EPSILON[letter]) % c7.PHASES
            if next_phase == q and not cut.matches(previous, letter):
                nxt: Hashable = accept_cut
            else:
                nxt = (next_phase, letter)
            transition[(state, letter)] = nxt
            if nxt not in states:
                states.add(nxt)
                if nxt not in (accept_cut, dead):
                    frontier.append(nxt)

    regular = frozenset(states - {accept_cut, dead})
    accepting = frozenset({accept_cut}) if stop_at_cut else regular
    machine = DFA(
        tuple(c7.SIGMA),
        frozenset(states),
        start,
        accepting,
        transition,
    ).minimized()
    machine.validate()
    return machine


def _transition_monoid(machine: DFA) -> set[tuple[int, ...]]:
    """Enumerate the complete transition monoid of a minimal DFA."""

    minimal = machine.minimized().canonical()
    order = tuple(sorted(minimal.states, key=repr))
    index = {state: i for i, state in enumerate(order)}
    generators = {
        tuple(index[minimal.step(state, letter)] for state in order)
        for letter in minimal.alphabet
    }
    identity = tuple(range(len(order)))
    elements = {identity}
    frontier = deque([identity])
    while frontier:
        left = frontier.popleft()
        for right in generators:
            product = tuple(right[left[i]] for i in range(len(order)))
            if product not in elements:
                elements.add(product)
                frontier.append(product)
    return elements


def _period(transformation: tuple[int, ...]) -> int:
    """Eventual period of one transformation under composition with itself."""

    seen: dict[tuple[int, ...], int] = {}
    power = transformation
    exponent = 1
    while power not in seen:
        seen[power] = exponent
        power = tuple(transformation[power[i]] for i in range(len(transformation)))
        exponent += 1
    return exponent - seen[power]


def _aperiodic(machine: DFA) -> tuple[bool, int, tuple[int, ...] | None]:
    monoid = _transition_monoid(machine)
    for transformation in monoid:
        if _period(transformation) != 1:
            return False, len(monoid), transformation
    return True, len(monoid), None


def _check_token_aperiodicity(
    *,
    include_first_tokens: bool = True,
    use_repeat_control: bool = False,
) -> tuple[bool, int, int, str]:
    patterns = list(_patterns())
    if use_repeat_control:
        # The old pure-repeat/single-letter pattern has a cyclic element of
        # period three.  It is outside the proof family and is the negative
        # control used to show that the monoid judge can reject a pattern.
        patterns.append(("single", c7.MOVERS[0]))

    roles = (("post-cut", lambda q: q),)
    if include_first_tokens:
        roles += (("first", lambda _q: 0),)

    cases = 0
    monoid_elements = 0
    for pattern in patterns:
        for q in range(c7.PHASES):
            for role, start_phase in roles:
                machine = _cut_component_dfa(
                    q,
                    pattern,
                    start_phase=start_phase(q),
                    stop_at_cut=True,
                )
                ok, size, witness = _aperiodic(machine)
                cases += 1
                monoid_elements += size
                if not ok:
                    return (
                        False,
                        cases,
                        max(monoid_elements, 1),
                        f"periodic {role} token at q={q}, pattern={pattern!r}, "
                        f"monoid element={witness!r}",
                    )

    if not include_first_tokens:
        return (
            False,
            cases,
            max(monoid_elements, 1),
            "coverage omission: the initial first-token automata were not checked",
        )
    return (
        True,
        cases,
        max(monoid_elements, 1),
        f"all {cases} minimal first/post token DFAs have aperiodic transition monoids",
    )


def check_token_aperiodicity(
    include_first_tokens: bool = True,
    use_repeat_control: bool = False,
) -> tuple[bool, int, str]:
    """Public acceptance check for all ``17 * 3 * 2`` token automata."""

    ok, cases, _, detail = _check_token_aperiodicity(
        include_first_tokens=include_first_tokens,
        use_repeat_control=use_repeat_control,
    )
    return ok, cases, detail


def _direct_cut_counter_dfa(q: int, pattern: tuple, residue: int) -> DFA:
    """The direct ``Cut.run`` machine, accepting one residue modulo seven."""

    cut = c7.Cut(q, pattern)
    start = (0, None, 0)
    states: set[tuple[int, tuple[int, int] | None, int]] = {start}
    transition = {}
    frontier = deque([start])
    while frontier:
        phase, previous, count = state = frontier.popleft()
        for letter in c7.SIGMA:
            next_phase = (phase + c7.EPSILON[letter]) % c7.PHASES
            next_count = count
            if next_phase == q:
                if cut.matches(previous, letter):
                    next_previous = letter
                else:
                    next_previous = None
                    next_count = (count + 1) % c7.MODULUS
            else:
                next_previous = letter
            nxt = (next_phase, next_previous, next_count)
            transition[(state, letter)] = nxt
            if nxt not in states:
                states.add(nxt)
                frontier.append(nxt)
    machine = DFA(
        tuple(c7.SIGMA),
        frozenset(states),
        start,
        frozenset(state for state in states if state[2] == residue),
        transition,
    ).minimized()
    machine.validate()
    return machine


def _eps_dfa(alphabet: Iterable[tuple[int, int]]) -> DFA:
    alpha = tuple(alphabet)
    transition = {
        (state, letter): 1
        for state in (0, 1)
        for letter in alpha
    }
    return DFA(alpha, frozenset({0, 1}), 0, frozenset({0}), transition)


def _dfa_power(machine: DFA, exponent: int) -> DFA:
    if exponent < 0:
        raise ValueError("a DFA language power needs a nonnegative exponent")
    result = _eps_dfa(machine.alphabet)
    for _ in range(exponent):
        result = dfa_concat(result, machine)
    return result


def _dfa_union(left: DFA, right: DFA) -> DFA:
    return dfa_product(left, right, lambda l, r: l or r)


def _equivalent(left: DFA, right: DFA) -> tuple[bool, int, tuple | None]:
    """Complete product BFS, returning a shortest distinguishing word if any."""

    if left.alphabet != right.alphabet:
        return False, 1, ()
    start = (left.start, right.start)
    seen = {start}
    witness: dict[tuple[Hashable, Hashable], tuple] = {start: ()}
    frontier = deque([start])
    while frontier:
        lstate, rstate = state = frontier.popleft()
        if (lstate in left.accept) != (rstate in right.accept):
            return False, len(seen), witness[state]
        for letter in left.alphabet:
            nxt = (left.step(lstate, letter), right.step(rstate, letter))
            if nxt not in seen:
                seen.add(nxt)
                witness[nxt] = witness[state] + (letter,)
                frontier.append(nxt)
    return True, len(seen), None


def _residue_formula_dfa(
    q: int,
    pattern: tuple,
    residue: int,
    *,
    loop_power: int,
    include_zero_cut_case: bool,
) -> DFA:
    """Compile ``O X^r (X^loop_power)* V``, plus ``V0`` at residue zero."""

    opening = _cut_component_dfa(
        q, pattern, start_phase=0, stop_at_cut=True
    )
    block = _cut_component_dfa(
        q, pattern, start_phase=q, stop_at_cut=True
    )
    tail = _cut_component_dfa(
        q, pattern, start_phase=q, stop_at_cut=False
    )
    zero_cut = _cut_component_dfa(
        q, pattern, start_phase=0, stop_at_cut=False
    )

    repeated = _dfa_power(block, loop_power)
    loop = dfa_star(repeated)
    prefix = dfa_concat(opening, _dfa_power(block, (residue - 1) % c7.MODULUS))
    positive = dfa_concat(dfa_concat(prefix, loop), tail)
    if residue == 0 and include_zero_cut_case:
        return _dfa_union(zero_cut, positive)
    return positive


def _check_residue_factorization(
    *,
    loop_power: int = 7,
    include_zero_cut_case: bool = True,
) -> tuple[bool, int, int, str]:
    cases = 0
    visited_pairs = 0
    for pattern in _patterns():
        for q in range(c7.PHASES):
            for residue in range(c7.MODULUS):
                formula = _residue_formula_dfa(
                    q,
                    pattern,
                    residue,
                    loop_power=loop_power,
                    include_zero_cut_case=include_zero_cut_case,
                )
                direct = _direct_cut_counter_dfa(q, pattern, residue)
                ok, visited, witness = _equivalent(formula, direct)
                cases += 1
                visited_pairs += visited
                if not ok:
                    return (
                        False,
                        cases,
                        max(visited_pairs, 1),
                        f"factorisation failed at q={q}, residue={residue}, "
                        f"pattern={pattern!r}; distinguishing word={witness!r}",
                    )
    return (
        True,
        cases,
        max(visited_pairs, 1),
        f"all {cases} direct cut counters equal "
        f"O X^((h-1) mod 7) (X^7)* V "
        f"(with V0 at residue zero)",
    )


def check_residue_factorization(
    loop_power: int = 7,
    include_zero_cut_case: bool = True,
) -> tuple[bool, int, str]:
    """Public exact check for all ``17 * 3 * 7`` residue languages."""

    ok, cases, _, detail = _check_residue_factorization(
        loop_power=loop_power,
        include_zero_cut_case=include_zero_cut_case,
    )
    return ok, cases, detail


def _check_atom_coverage(
    *, allow_reversal: bool = True,
) -> tuple[bool, int, int, str]:
    atoms = tuple(c7.ATOMS)
    unique = set(atoms)
    counts = Counter((direction, pattern[0]) for direction, _q, pattern in atoms)
    valid_patterns = set(map(repr, _patterns()))

    errors = []
    if len(atoms) != 57 or len(unique) != 57:
        errors.append(f"expected 57 distinct atoms, got {len(atoms)}/{len(unique)}")
    if counts != Counter({("forward", "anti"): 24,
                          ("backward", "anti"): 24,
                          ("forward", "set"): 9}):
        errors.append(f"unexpected direction/pattern census {dict(counts)!r}")
    if any(repr(pattern) not in valid_patterns for _direction, _q, pattern in atoms):
        errors.append("an arithmetic atom is outside the 17 certified patterns")
    if any(q not in range(c7.PHASES) for _direction, q, _pattern in atoms):
        errors.append("an arithmetic atom has an invalid cut phase")
    if not allow_reversal and any(direction == "backward" for direction, _q, _p in atoms):
        errors.append("coverage omission: reversal/backward atoms were disabled")
    if not any(direction == "forward" for direction, _q, _p in atoms):
        errors.append("coverage omission: no forward atom")
    if allow_reversal and not any(direction == "backward" for direction, _q, _p in atoms):
        errors.append("coverage omission: no reversal/backward atom")

    checked_fields = len(atoms) * 3
    if errors:
        return False, len(atoms), max(checked_fields, 1), "; ".join(errors)
    return (
        True,
        len(atoms),
        checked_fields,
        "57 distinct arithmetic atoms covered: 33 forward and 24 via reversal",
    )


def check_atom_coverage(allow_reversal: bool = True) -> tuple[bool, int, str]:
    """Audit the exact post-cancellation arithmetic atom family."""

    ok, atoms, _, detail = _check_atom_coverage(allow_reversal=allow_reversal)
    return ok, atoms, detail


def main() -> int:
    token_ok, token_cases, token_universe, token_detail = _check_token_aperiodicity()
    missing_first_ok, _, _, _ = _check_token_aperiodicity(include_first_tokens=False)
    repeat_ok, _, _, _ = _check_token_aperiodicity(use_repeat_control=True)
    token_check = RUN.add(
        exhaustive(
            "C7:C3 first/post token aperiodicity",
            CLAIM_ID,
            passed=token_ok and token_cases == 17 * 3 * 2,
            universe=token_universe,
            detail=token_detail,
            controls=(
                Control(
                    "omit first tokens",
                    "remove the initial first-token role from the token family",
                    rejected=not missing_first_ok,
                ),
                Control(
                    "add periodic single pattern",
                    "add a same-letter pure-repeat pattern of period three",
                    rejected=not repeat_ok,
                ),
            ),
        )
    )

    residue_ok, residue_cases, residue_universe, residue_detail = (
        _check_residue_factorization()
    )
    six_ok, _, _, _ = _check_residue_factorization(loop_power=6)
    no_zero_ok, _, _, _ = _check_residue_factorization(include_zero_cut_case=False)
    residue_check = RUN.add(
        exhaustive(
            "C7:C3 mod-seven cut factorisation",
            CLAIM_ID,
            passed=residue_ok and residue_cases == 17 * 3 * 7,
            universe=residue_universe,
            detail=residue_detail,
            controls=(
                Control(
                    "six-token loop",
                    "replace the seven-token loop X^7 by X^6",
                    rejected=not six_ok,
                ),
                Control(
                    "omit zero-cut case",
                    "delete V0 from the residue-zero formula",
                    rejected=not no_zero_ok,
                ),
            ),
        )
    )

    atoms_ok, atom_count, atom_universe, atom_detail = _check_atom_coverage()
    no_reverse_ok, _, _, _ = _check_atom_coverage(allow_reversal=False)
    atom_check = RUN.add(
        exhaustive(
            "C7:C3 arithmetic atom coverage",
            CLAIM_ID,
            passed=atoms_ok and atom_count == 57,
            universe=atom_universe,
            detail=atom_detail,
            controls=(
                Control(
                    "omit reversal",
                    "remove every backward atom supplied by word reversal",
                    rejected=not no_reverse_ok,
                ),
            ),
        )
    )

    RUN.add(
        conjunction(
            "C7:C3 finite token core",
            CLAIM_ID,
            parts=(token_check, residue_check, atom_check),
            detail=(
                "the complete finite core consists of first/post token "
                "aperiodicity, exact mod-seven factorisation, and all 57 atoms"
            ),
            rationale=(
                "C7C3-H1-FINITE-CORE-01 asserts exactly these three finite statements; "
                "the external Schuetzenberger theorem and C7C3-IDENT-01 remain "
                "separate mathematical inputs to the height-one proof."
            ),
        )
    )
    return RUN.finish(VERDICT_FILE)


if __name__ == "__main__":
    raise SystemExit(main())
