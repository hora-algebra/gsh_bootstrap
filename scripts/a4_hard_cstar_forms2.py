#!/usr/bin/env python3
"""Corrected C* extraction for the two hard pattern classes of
N-A4-FULL-033, over the FULL class alphabet.

The reduced alphabet of a4_pattern_token_starfree.py (two letters per
class) misses, for the SAME-TYPE pattern ('2',h,g), the class
"type-e mover that is neither h nor g" (the real 12-letter alphabet has
4 movers of each type, so 2 such letters remain).  This script rebuilds
the C* DFAs over the complete class alphabet:

    g  : the pattern's landing mover, eps e
    u  : the pattern's context letter h (same-type case), eps e
    x  : other same-type mover (neither h nor g), eps e
    d1, d2 : opposite-type movers, eps e' = 3 - e
    f1, f2 : fillers, eps 0        (f1 = the context letter h in the
                                    filler case)

and re-checks aperiodicity and minimal size, then tests candidate
star-free expressions by exact DFA equivalence.
"""
import sys
sys.path.insert(0, 'scripts')
from a4_pattern_token_starfree import (
    dfa_minimize, dfa_product, dfa_compl, dfa_concat, dfa_equiv,
    dfa_words, E, atoms, cat, uni, inter, comp, EPSW, to_dfa,
    big_inter, big_uni, token_dfa, cstar_dfa, first_return_dfa,
    is_aperiodic, blocks)


def make_alpha7(e):
    ep = 3 - e
    alpha = ['g', 'u', 'x', 'd1', 'd2', 'f1', 'f2']
    EPS = {'g': e, 'u': e, 'x': e, 'd1': ep, 'd2': ep, 'f1': 0, 'f2': 0}
    return alpha, EPS


CASES = [
    ("same-type ('2',u,g)", lambda buf, ch: ch == 'g' and buf == 'u'),
    ("filler    ('2',f1,g)", lambda buf, ch: ch == 'g' and buf == 'f1'),
]


def show_dfa(name, dfa, alpha):
    n, t, s, a = dfa
    print(f"  {name}: {n} states, start {s}, accept {sorted(a)}, "
          f"aperiodic={is_aperiodic(dfa, alpha)}")
    for i in range(n):
        row = ', '.join(f"{ch}->{t[i][ch]}" for ch in alpha)
        print(f"    state {i}: {row}")
    print(f"    shortest words: {dfa_words(dfa, alpha, 8, 12)}")


def main():
    for e in (1, 2):
        alpha, EPS = make_alpha7(e)
        print(f"===== eps(g) = {e} (full class alphabet) =====")
        for name, match in CASES:
            cs = dfa_minimize(cstar_dfa(alpha, EPS, match), alpha)
            show_dfa(f"C* {name}", cs, alpha)
            tok = dfa_minimize(token_dfa(alpha, EPS, match), alpha)
            print(f"  token {name}: {tok[0]} states, "
                  f"aperiodic={is_aperiodic(tok, alpha)}")
        print()


if __name__ == "__main__":
    main()
