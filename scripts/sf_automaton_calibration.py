#!/usr/bin/env python3
"""Calibrate the SF-automaton pipeline against results already in this repository.

What this script establishes, all by exact automaton constructions (no
sampling, no length cutoffs):

  [0] ground truth for L2 is recompiled from the PRINTED regex of Weis 2011
      p.115 and asserted equal to the six-state walk automaton;
  [1] the letter-labelled minimal DFA of L2 has loop complexity 2, and state
      elimination on it returns a star-height-2 expression for L2;
  [2] the four-diagonal walk graph with its two a-self-loops absorbed has
      loop complexity 1, and its first-return and escape languages are
      exactly the ones printed in notes/weis_l2_full_height_one.md §3 --
      for both anchors D2 and D3;
  [3] every anchor-walk atom W_d(x) is the language of a rank-1 SF-automaton
      and therefore has generalized star height at most 1;
  [4] both letter-parity atoms are languages of rank-1 SF-automata;
  [5] hence the four atom families that WEIS-L2-GSH-01 intersects are each
      rank-1 SF-automaton languages, i.e. L2 lies in the Boolean closure of
      rank-1 SF-automata.

What this script does NOT establish: that L2 itself is not the language of
some rank-1 SF-automaton.  No rank-1 SF-automaton for L2 is known, but the
labels range over all star-free languages, so this is a search result and
never a star-height lower bound (README research rule 1).

Usage:
    python3 scripts/sf_automaton_calibration.py
    python3 scripts/sf_automaton_calibration.py --certificate
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from tools import sf_automaton as sfa  # noqa: E402
from tools.regex_cert import compile_regex, equivalence_witness  # noqa: E402
from tools.targets import build_target, word_problem_dfa  # noqa: E402

AB = ("a", "b")
A = sfa.letter("a")
B = sfa.letter("b")
A_STAR = sfa.A_STAR
B_STAR = sfa.B_STAR
ALIASES = sfa.ALIASES


def fail(message: str) -> None:
    print(f"[FAIL] {message}")
    sys.exit(1)


def same_language(expression, target) -> bool:
    return (
        equivalence_witness(compile_regex(expression, AB).minimized(), target) is None
    )


def printed_l2_expression():
    """L2 = ( a b* a | b a* b (a b* a)* b a* b )*, exactly as printed."""

    aba = sfa.concat(A, sfa.star(B), A)
    bab = sfa.concat(B, sfa.star(A), B)
    return sfa.star(sfa.union(aba, sfa.concat(bab, sfa.star(aba), bab)))


def step_ground_truth():
    print("[0] ground truth for L2")
    printed = compile_regex(printed_l2_expression(), AB).minimized()
    walk = sfa.weis_l2_minimal_dfa()
    if len(printed.states) != 6:
        fail(f"printed L2 regex minimizes to {len(printed.states)} states, expected 6")
    if equivalence_witness(printed, walk) is not None:
        fail("the six-vertex walk automaton does not define the printed L2")
    print("    [ok] printed regex compiles to the 6-state walk automaton of")
    print("         a = (0 1)(3 4), b = (0 2 3 5), start = accept = v0.")
    return walk


def step_letter_labelled(target):
    print("[1] L2 as a letter-labelled SF-automaton (the trivial view)")
    machine = sfa.from_dfa(target)
    rank = machine.loop_complexity()
    expression = machine.to_expression()
    if rank != 2:
        fail(f"expected loop complexity 2 for the minimal DFA of L2, got {rank}")
    if not same_language(expression, target):
        fail("state elimination on the minimal DFA of L2 changed the language")
    print(f"    [ok] loop complexity = {rank}; elimination returns star height "
          f"{expression.star_height()} and denotes exactly L2.")
    print("    [note] this is the r_SF <= 2 upper bound; it does not reach 1.")
    return rank


def step_diagonal_graph():
    print("[2] the four-diagonal graph with a-self-loops absorbed")
    graph = sfa.WEIS_L2_DIAGONAL_GRAPH
    rank = graph.loop_complexity()
    if rank != 1:
        fail(f"expected loop complexity 1 for the diagonal graph, got {rank}")
    print(f"    [ok] loop complexity = {rank}: every cycle passes through D2,")
    print("         and through D3, because a* is star-free.")

    published = {
        "D2": {
            "return": sfa.concat(
                sfa.union(A, sfa.concat(B, A_STAR, B, A_STAR, B)), sfa.any_of(AB)
            ),
            "escape": {
                "D3": sfa.union(A, sfa.concat(B, A_STAR, B, A_STAR, B)),
                "D1": sfa.concat(B, A_STAR),
                "D0": sfa.concat(B, A_STAR, B, A_STAR),
            },
        },
        "D3": {
            "return": sfa.union(
                sfa.concat(sfa.any_of(AB), A),
                sfa.concat(sfa.any_of(AB), B, A_STAR, B, A_STAR, B),
            ),
            "escape": {
                "D2": sfa.any_of(AB),
                "D1": sfa.concat(sfa.any_of(AB), B, A_STAR),
                "D0": sfa.concat(sfa.any_of(AB), B, A_STAR, B, A_STAR),
            },
        },
    }

    for anchor, expected in published.items():
        got_return = sfa.first_return(graph, anchor)
        if got_return.star_height() != 0:
            fail(f"first-return language at {anchor} is not star-free")
        if not same_language(got_return, compile_regex(expected["return"], AB).minimized()):
            fail(f"first-return language at {anchor} differs from the published one")
        print(f"    [ok] R_{{{anchor}}} = {sfa.pretty(got_return, ALIASES)}")
        print(f"         (star-free, matches notes/weis_l2_full_height_one.md §3)")
        got_escape = sfa.escapes(graph, anchor)
        for target_state, want in expected["escape"].items():
            expr = got_escape[target_state]
            if expr.star_height() != 0:
                fail(f"escape language {anchor} -> {target_state} is not star-free")
            if not same_language(expr, compile_regex(want, AB).minimized()):
                fail(f"escape language {anchor} -> {target_state} differs from the published one")
        print(f"    [ok] all escape languages S_{{{anchor}}} match as well.")
    return graph


def step_walk_atoms(graph):
    print("[3] the anchor-walk atoms W_d(x) as rank-1 SF-automaton languages")
    certified = {}
    for anchor in ("D2", "D3"):
        for target_state in graph.states:
            atom = sfa.SFAutomaton(
                alphabet=AB,
                states=graph.states,
                start=frozenset({anchor}),
                accept=frozenset({target_state}),
                edges=graph.edges,
                description=f"W_{anchor}({target_state})",
            )
            rank = atom.loop_complexity()
            expression = atom.to_expression()
            walk = sfa.weis_l2_diagonal_walk_dfa(anchor, target_state)
            if rank != 1:
                fail(f"W_{anchor}({target_state}) has loop complexity {rank}, expected 1")
            if expression.star_height() > 1:
                fail(f"W_{anchor}({target_state}) eliminated to height {expression.star_height()}")
            if not same_language(expression, walk):
                fail(f"W_{anchor}({target_state}) is not the diagonal walk language")
            certified[(anchor, target_state)] = (atom, expression, walk)
        print(f"    [ok] anchor {anchor}: all 4 atoms have loop complexity 1, star")
        print(f"         height <= 1, and equal the exact diagonal walk language.")
    return certified


def step_parity_atoms():
    print("[4] the letter-parity atoms as rank-1 SF-automaton languages")
    targets = {
        "even_a": word_problem_dfa({"a": (1, 0), "b": (0, 1)}),
        "even_b": word_problem_dfa({"a": (0, 1), "b": (1, 0)}),
    }
    for name, target in targets.items():
        machine = sfa.CALIBRATION[name]
        rank = machine.loop_complexity()
        expression = machine.to_expression()
        if rank != 1:
            fail(f"{name} has loop complexity {rank}, expected 1")
        if not same_language(expression, target):
            fail(f"{name} does not define its target language")
        print(f"    [ok] {name}: loop complexity 1, star height "
              f"{expression.star_height()}, expression "
              f"{sfa.pretty(expression, ALIASES)}")


def step_summary(rank_letter):
    print("[5] summary of the measurement")
    print("    WEIS-L2-GSH-01 writes L2 as a union of 8 fibres, each an")
    print("    intersection of 2 parity atoms and 2 anchor-walk atoms.")
    print("    Every one of those atoms is now certified to be the language of")
    print("    a rank-1 SF-automaton, so")
    print("        L2 in BoolComb(rank-1 SF-automata),")
    print(f"        r_SF(L2) <= {rank_letter}   (letter-labelled minimal DFA).")
    print("    No rank-1 SF-automaton for L2 itself is known.  Labels range over")
    print("    all star-free languages, so that is a SEARCH RESULT and NEVER a")
    print("    star-height lower bound (README research rule 1).")
    print("    This is the CORE2 'rank 2 collapses to rank 1' gap, measured on a")
    print("    concrete literature-backed language.")


def write_certificates(certified):
    written = []
    anchor_atom, _, walk = certified[("D2", "D2")]
    path = REPO / "data/certificates/height1_weis_l2_anchor_atom.json"
    payload = anchor_atom.certificate(
        walk,
        "K_{D2} = (R_{D2})*, the anchor-walk atom of the Weis L2 height-one proof "
        "(notes/weis_l2_full_height_one.md §3), emitted by state elimination on a "
        "star-free-labelled automaton of loop complexity 1 "
        "(scripts/sf_automaton_calibration.py, notes/sf_labeled_automata.md). "
        "Target: the four-diagonal walk automaton, start = accept = D2.",
    )
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    written.append(path)

    z3 = sfa.CALIBRATION["z3"]
    path = REPO / "data/certificates/height1_z3_sf_automaton.json"
    payload = z3.certificate(
        build_target("z3"),
        "{ w : |w|_a = 0 mod 3 } from a star-free-labelled automaton of loop "
        "complexity 1 (b* absorbed into the incoming edges of every residue "
        "state); scripts/sf_automaton_calibration.py.",
    )
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    written.append(path)

    for path in written:
        print(f"    [ok] wrote {path.relative_to(REPO)}")
    print("    re-check them with `python3 scripts/check_certificate.py <path>`;")
    print("    ./scripts/check.sh picks them up automatically.")


def main() -> int:
    target = step_ground_truth()
    rank_letter = step_letter_labelled(target)
    graph = step_diagonal_graph()
    certified = step_walk_atoms(graph)
    step_parity_atoms()
    step_summary(rank_letter)
    if "--certificate" in sys.argv:
        print("[6] certificates")
        write_certificates(certified)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
