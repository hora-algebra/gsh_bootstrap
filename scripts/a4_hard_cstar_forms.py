#!/usr/bin/env python3
"""Derive explicit star-free expressions for the two HARD cut-core
languages `C*` of N-A4-FULL-033 (same-type-mover digram pattern
('2',h,g) and filler digram pattern ('2',f,g)), and certify them by
EXACT DFA equivalence on the reduced 6-letter alphabet of
`a4_pattern_token_starfree.py` (fully general for these token automata).

C* = set of words (from cut phase q=0) in which every landing on 0 is a
pattern-matched landing and which end at a landing (or are empty).
"""
import sys
sys.path.insert(0, 'scripts')
from a4_pattern_token_starfree import (
    make_alpha, cstar_dfa, dfa_equiv, dfa_words, dfa_minimize, to_dfa,
    atoms, cat, uni, inter, comp, EPSW, blocks, big_uni, big_inter)


def show_dfa(name, dfa, alpha):
    n, t, s, a = dfa
    print(f"  {name}: {n} states, start {s}, accept {sorted(a)}")
    for i in range(n):
        row = ", ".join(f"{ch}->{t[i][ch]}" for ch in alpha)
        print(f"    state {i}: {row}")


def main():
    for e in (1, 2):
        alpha, EPS = make_alpha(e)
        B = blocks(alpha, EPS)
        print(f"===== eps(g) = {e} =====")
        for name, match in [
            ("same-type ('2',u,g)", lambda buf, ch: ch == 'g' and buf == 'u'),
            ("filler    ('2',f,g)", lambda buf, ch: ch == 'g' and buf == 'f1'),
        ]:
            cs = dfa_minimize(cstar_dfa(alpha, EPS, match), alpha)
            print(f"-- {name} --")
            show_dfa("C*", cs, alpha)
            print("  shortest words:", dfa_words(cs, alpha, 6, 12))
    return 0


if __name__ == "__main__":
    sys.exit(main())
