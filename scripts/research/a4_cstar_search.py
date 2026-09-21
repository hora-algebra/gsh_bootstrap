#!/usr/bin/env python3
"""Interactive search for explicit star-free expressions for the two hard
C* cores (same-type and filler digram patterns), over the full 7-class
alphabet.  Candidates are checked by exact DFA equivalence; witnesses
guide refinement.

Usage: python scripts/a4_cstar_search.py
"""
import sys
import os.path as _op  # noqa: E402
_GSHROOT = _op.dirname(_op.dirname(_op.dirname(_op.abspath(__file__))))
# Import by absolute path rather than a cwd-relative one: these modules are
# split across scripts/research (CI re-runs them) and scripts/search (long
# searches and negative results), and run_research.py invokes them from the
# repository root while a human runs them from anywhere.
sys.path[:0] = [_op.join(_GSHROOT, 'scripts', 'research'),
                _op.join(_GSHROOT, 'scripts', 'search')]
from a4_pattern_token_starfree import (
    dfa_minimize, dfa_equiv, dfa_words, E, atoms, cat, uni, inter, comp,
    EPSW, to_dfa, big_inter, big_uni, cstar_dfa, is_aperiodic)
from a4_hard_cstar_forms2 import make_alpha7, CASES


def run(w, EPS, match, q=0):
    """Simulate the C* automaton on w; return 'ACC'/'REJ' and trace."""
    ph, buf, boundary = 0, None, True
    for ch in w:
        nph = (ph + EPS[ch]) % 3
        if nph == q:
            if match(buf, ch):
                ph, buf, boundary = nph, ch, True
            else:
                return 'DEAD'
        else:
            ph, buf, boundary = nph, ch, False
    return 'ACC' if boundary else 'MID'


def check(name, expr, target_dfa, alpha, EPS, match):
    w = dfa_equiv(to_dfa(expr, alpha), target_dfa, alpha)
    if w is None:
        print(f"  {name}: OK (exact equivalence)")
        return True
    verdict = run(w, EPS, match)
    print(f"  {name}: WITNESS {w}  (C* automaton says: {verdict})")
    return False


def build_blocks(alpha, EPS):
    movers = [c for c in alpha if EPS[c] != 0]
    fills = [c for c in alpha if EPS[c] == 0]
    m1 = [c for c in alpha if EPS[c] == 1]
    m2 = [c for c in alpha if EPS[c] == 2]
    ss = comp(inter(EPSW, comp(EPSW)))          # Sigma*
    sp = cat(atoms(alpha), ss)                  # Sigma+
    fw = comp(cat(ss, atoms(movers), ss))       # fill*
    A1, A2, M = atoms(m1), atoms(m2), atoms(movers)
    P = uni(cat(A1, fw, A1), cat(A2, fw, A2))   # pairSame
    return dict(ss=ss, sp=sp, fw=fw, A1=A1, A2=A2, M=M, P=P,
                movers=movers, fills=fills, m1=m1, m2=m2)


def main():
    e = 1                     # class-level DFA identical for e=1,2
    alpha, EPS = make_alpha7(e)
    B = build_blocks(alpha, EPS)
    ss, fw, M = B['ss'], B['fw'], B['M']
    Ecl = atoms(['g', 'u', 'x'])                # type-e movers
    Dcl = atoms(['d1', 'd2'])                   # type-e' movers
    Fcl = atoms(['f1', 'f2'])
    G, U = atoms(['g']), atoms(['u'])

    print("=== same-type C* ===")
    cs_same = dfa_minimize(cstar_dfa(alpha, EPS, CASES[0][1]), alpha)

    # Hypothesis v1: nonempty words =
    #   starts with mover, ends with adjacent u g,
    #   no fill immediately after a landing:  approximated by
    #   no factor (u g) (fill)  ... certainly wrong; get witnesses.
    v1 = uni(EPSW,
             inter(cat(M, ss),
                   cat(ss, U, G),
                   comp(cat(ss, U, G, Fcl, ss))))
    check("same v1", v1, cs_same, alpha, EPS, CASES[0][1])

    print("=== filler C* ===")
    cs_fill = dfa_minimize(cstar_dfa(alpha, EPS, CASES[1][1]), alpha)
    F1 = atoms(['f1'])
    v1f = uni(EPSW,
              inter(cat(M, ss),
                    cat(ss, F1, G),
                    comp(cat(ss, F1, G, Fcl, ss))))
    check("fill v1", v1f, cs_fill, alpha, EPS, CASES[1][1])


if __name__ == "__main__":
    main()
