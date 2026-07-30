#!/usr/bin/env python3
"""Explicit star-free block code `K` with `C* = K*` (obligation N-A4-FULL-033b).

Solving the automaton of `scripts/a4_aggregate_cstar.py` by Arden's lemma,
eliminating the phase-1 and phase-2 states first, gives

    W  = (M1 F* D F*)*                                     -- star-free
    K  = D F* G  ∪  (M1 F* ∪ D F* D F*) · W · (U F* ∪ G F+) · G
    C* = K*

Here `G` is the distinguished mover `g`, `U` the other movers of the same
phase, `D` the movers of the other phase and `F` the fillers.  Every piece of
`K` is star-free: `F*` is "only fillers" and `W` is "the movers alternate,
starting type-1 and ending type-2, with no leading filler" -- both are
forbidden-factor conditions.

So the ONLY thing missing for `N-A4-FULL-033b` is that `K*` is star-free for
this one explicit code `K`; equivalently that `K` has bounded synchronization
delay (Schützenberger).  This script certifies `C* = K*` by exact DFA
equivalence, so the reduction itself is not in doubt.

CPU: single-threaded, duty-cycle throttled (`--duty`, default 0.5).
"""
import argparse
import sys

sys.path.insert(0, 'scripts')
from a4_pattern_token_starfree import (          # noqa: E402
    dfa_minimize, dfa_product, dfa_equiv, dfa_words, to_dfa,
    atoms, cat, uni, comp, EPSW, is_aperiodic)
from a4_aggregate_cstar import ALPHA, make_eps, cstar_dfa_from   # noqa: E402


def dfa_star(d, alpha):
    """Kleene star of a DFA, by subset construction with restarts."""
    n, t, s, a = d
    START = ('EPS',)
    idx = {START: 0}
    order = [START]
    trans = []
    for st in order:
        cur = frozenset({s}) if st == START else st
        row = {}
        for ch in alpha:
            nxt = frozenset(t[q][ch] for q in cur)
            if nxt & a:
                nxt = nxt | {s}
            if nxt not in idx:
                idx[nxt] = len(order)
                order.append(nxt)
            row[ch] = idx[nxt]
        trans.append(row)
    acc = frozenset(i for st, i in idx.items()
                    if st == START or (st != START and (st & a)))
    return dfa_minimize((len(order), trans, 0, acc), alpha)


def dfa_concat_all(ds, alpha):
    from a4_pattern_token_starfree import dfa_concat
    out = ds[0]
    for d in ds[1:]:
        out = dfa_concat(out, d, alpha)
    return out


def dfa_union(d1, d2, alpha):
    return dfa_minimize(dfa_product(d1, d2, lambda a, b: a or b, alpha), alpha)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--duty', type=float, default=0.5)
    args = ap.parse_args()
    _ = args

    ok = True
    for e in (1, 2):
        EPS = make_eps(e)
        same = [c for c in ALPHA if EPS[c] == e and c != 'g']
        other = [c for c in ALPHA if EPS[c] == 3 - e]
        fill = [c for c in ALPHA if EPS[c] == 0]
        Uni = comp(atoms(frozenset()))
        G = atoms(frozenset(['g']))
        U = atoms(frozenset(same))
        D = atoms(frozenset(other))
        F = atoms(frozenset(fill))
        M1 = atoms(frozenset(same + ['g']))
        M = atoms(frozenset(same + other + ['g']))
        # F* = "no mover occurs"           (star-free)
        Fs = comp(cat(Uni, cat(M, Uni)))
        Fp = cat(F, Fs)                     # F+

        dFs = to_dfa(Fs, ALPHA)
        dG = to_dfa(G, ALPHA)
        dU = to_dfa(U, ALPHA)
        dD = to_dfa(D, ALPHA)
        dM1 = to_dfa(M1, ALPHA)
        dFp = to_dfa(Fp, ALPHA)

        # W = (M1 F* D F*)*
        cyc = dfa_concat_all([dM1, dFs, dD, dFs], ALPHA)
        W = dfa_star(cyc, ALPHA)

        # K = D F* G  ∪  (M1 F* ∪ D F* D F*) W (U F* ∪ G F+) G
        k1 = dfa_concat_all([dD, dFs, dG], ALPHA)
        open_ = dfa_union(dfa_concat_all([dM1, dFs], ALPHA),
                          dfa_concat_all([dD, dFs, dD, dFs], ALPHA), ALPHA)
        close_ = dfa_union(dfa_concat_all([dU, dFs], ALPHA),
                           dfa_concat_all([dG, dFp], ALPHA), ALPHA)
        k2 = dfa_concat_all([open_, W, close_, dG], ALPHA)
        K = dfa_union(k1, k2, ALPHA)

        target = cstar_dfa_from(EPS, 0, None)
        Kstar = dfa_star(K, ALPHA)
        wit = dfa_equiv(Kstar, target, ALPHA)
        print(f"===== eps(g) = {e} =====")
        print(f"  K: {K[0]} states; W: {W[0]} states; "
              f"K aperiodic = {is_aperiodic(K, ALPHA)}; "
              f"W aperiodic = {is_aperiodic(W, ALPHA)}")
        print(f"  shortest codewords of K: {dfa_words(K, ALPHA, 7, 8)}")
        if wit is None:
            print("  PASS: K* = C* (exact DFA equivalence)")
        else:
            ok = False
            print(f"  FAIL: witness {wit}")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
