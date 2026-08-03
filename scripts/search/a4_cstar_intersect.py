#!/usr/bin/env python3
"""Find a star-free expression for the aggregate cut core `C*` of
N-A4-FULL-033b as an INTERSECTION of small star-free supersets.

Blind size-ordered enumeration (`a4_aggregate_cstar.py`) fails: no expression
of size <= 6 denotes any of the residuals.  But a Boolean-algebra element is
usually a conjunction of *simple* conditions, each individually cheap, whose
combined size is far beyond a blind search.  So:

  1. enumerate star-free languages of size <= N (modulo language identity);
  2. keep only those that CONTAIN the target;
  3. intersect them all and check whether the result is exactly the target;
  4. if so, extract a small sufficient sub-family greedily.

CPU: single-threaded with a duty-cycle throttle (`--duty`, default 0.5).
"""
import argparse
import sys
import time

import os.path as _op  # noqa: E402
_GSHROOT = _op.dirname(_op.dirname(_op.dirname(_op.abspath(__file__))))
# Import by absolute path rather than a cwd-relative one: these modules are
# split across scripts/research (CI re-runs them) and scripts/search (long
# searches and negative results), and run_research.py invokes them from the
# repository root while a human runs them from anywhere.
sys.path[:0] = [_op.join(_GSHROOT, 'scripts', 'research'),
                _op.join(_GSHROOT, 'scripts', 'search')]
from a4_pattern_token_starfree import (          # noqa: E402
    dfa_minimize, dfa_product, dfa_compl, dfa_concat, dfa_words, to_dfa,
    atoms, cat, uni, inter, comp, EPSW, is_aperiodic)
from a4_aggregate_cstar import (                 # noqa: E402
    ALPHA, make_eps, cstar_dfa_from, canon)

_DUTY = [0.5, time.perf_counter()]


def set_duty(d):
    _DUTY[0] = max(0.05, min(1.0, d))
    _DUTY[1] = time.perf_counter()


def throttle(slice_s=0.05):
    d = _DUTY[0]
    if d >= 1.0:
        return
    now = time.perf_counter()
    worked = now - _DUTY[1]
    if worked >= slice_s:
        time.sleep(worked * (1.0 - d) / d)
        _DUTY[1] = time.perf_counter()


def seeds(e):
    """Primitives plus the structurally-derived conditions of the C₃ walk.

    In `C*` every landing is a `g` at phase 2 whose predecessor is not `g`;
    at phase 1 only type-1 movers are legal and at phase 2 only `g` or a
    type-2 mover.  That yields the following *necessary* conditions, each
    star-free and each a superset of `C*`:

      * no leading filler (a filler at phase 0 is an unmatched landing);
      * the word is empty or ends in `g` (it must end at a landing);
      * `gggg` is impossible (its run dies from every state);
      * three consecutive movers of type 1 cover all three phases, so the one
        at phase 2 must be `g`: no three consecutive type-1 movers are all
        `u`;
      * three consecutive type-2 movers are impossible (phase 0→2→1, and a
        type-2 mover at phase 1 is illegal).
    """
    EPS = make_eps(e)
    same = [c for c in ALPHA if EPS[c] == e and c != 'g']
    other = [c for c in ALPHA if EPS[c] == 3 - e]
    fill = [c for c in ALPHA if EPS[c] == 0]
    Uni = comp(atoms(frozenset()))
    G = atoms(frozenset(['g']))
    Um = atoms(frozenset(same))
    D = atoms(frozenset(other))
    F = atoms(frozenset(fill))
    M1 = atoms(frozenset(same + ['g']))
    M = atoms(frozenset(same + other + ['g']))
    Fs = comp(cat(Uni, cat(M, Uni)))          # only fillers

    def nofac(x):
        return comp(cat(Uni, cat(x, Uni)))

    return {
        'eps': EPSW,
        'U': Uni,
        'G': G,
        'Um': Um,
        'D': D,
        'F': F,
        'M1': M1,
        'M': M,
        'Fs': Fs,
        'noLeadF': comp(cat(F, Uni)),
        'endG': uni(EPSW, cat(Uni, G)),
        'noGGGG': nofac(cat(G, cat(G, cat(G, G)))),
        'no3Um': nofac(cat(Um, cat(Fs, cat(Um, cat(Fs, Um))))),
        'no3D': nofac(cat(D, cat(Fs, cat(D, cat(Fs, D))))),
    }


def enumerate_langs(e, max_size, verbose=True):
    """All star-free languages of expression size <= max_size, as
    key -> (name, expr, minimal dfa)."""
    layers = {1: {}}
    for name, expr in seeds(e).items():
        d = dfa_minimize(to_dfa(expr, ALPHA), ALPHA)
        layers[1].setdefault(canon(d), (name, expr, d))
    known = dict(layers[1])
    for size in range(2, max_size + 1):
        layers[size] = {}
        for k, (nm, ex, d) in list(layers[size - 1].items()):
            throttle()
            nd = dfa_minimize(dfa_compl(d), ALPHA)
            key = canon(nd)
            if key not in known:
                item = (f"~({nm})", comp(ex), nd)
                layers[size][key] = item
                known[key] = item
        for i in range(1, size):
            j = size - i
            if j < 1 or j not in layers:
                continue
            for k1, (n1, e1, d1) in list(layers[i].items()):
                throttle()
                for k2, (n2, e2, d2) in list(layers[j].items()):
                    for op, sym, mk in (
                        (lambda a, b: a or b, '|', uni),
                        (lambda a, b: a and b, '&', inter),
                    ):
                        nd = dfa_minimize(dfa_product(d1, d2, op, ALPHA), ALPHA)
                        key = canon(nd)
                        if key not in known:
                            item = (f"({n1}{sym}{n2})", mk(e1, e2), nd)
                            layers[size][key] = item
                            known[key] = item
                    nd = dfa_concat(d1, d2, ALPHA)
                    key = canon(nd)
                    if key not in known:
                        item = (f"({n1}.{n2})", cat(e1, e2), nd)
                        layers[size][key] = item
                        known[key] = item
        if verbose:
            print(f"      size {size}: {len(layers[size])} new "
                  f"({len(known)} total)", flush=True)
    return known


def is_superset(cand, target):
    """target ⊆ cand ?"""
    diff = dfa_minimize(
        dfa_product(target, cand, lambda a, b: a and not b, ALPHA), ALPHA)
    return not dfa_words(diff, ALPHA, 14, 1)


def intersect(d1, d2):
    return dfa_minimize(dfa_product(d1, d2, lambda a, b: a and b, ALPHA), ALPHA)


def find_conjunction(target, known, verbose=True):
    """Intersect all star-free supersets; if that hits the target exactly,
    greedily shrink to a small sufficient sub-family."""
    sup = []
    for key, (nm, ex, d) in known.items():
        throttle()
        if is_superset(d, target):
            sup.append((nm, ex, d))
    if verbose:
        print(f"      {len(sup)} star-free supersets found", flush=True)
    if not sup:
        return None
    acc = sup[0][2]
    for _, _, d in sup[1:]:
        throttle()
        acc = intersect(acc, d)
    if canon(acc) != canon(target):
        wit = dfa_words(dfa_minimize(
            dfa_product(acc, target, lambda a, b: a and not b, ALPHA), ALPHA),
            ALPHA, 12, 3)
        if verbose:
            print(f"      full intersection is STRICTLY larger; witnesses {wit}",
                  flush=True)
        return None
    # greedy shrink
    chosen = []
    cur = None
    while True:
        if cur is not None and canon(cur) == canon(target):
            break
        best = None
        for nm, ex, d in sup:
            throttle()
            if (nm, ex, d) in chosen:
                continue
            nxt = d if cur is None else intersect(cur, d)
            bad = len(dfa_words(dfa_minimize(
                dfa_product(nxt, target, lambda a, b: a and not b, ALPHA),
                ALPHA), ALPHA, 12, 40))
            if best is None or bad < best[0]:
                best = (bad, nm, ex, d, nxt)
        if best is None:
            return None
        chosen.append((best[1], best[2], best[3]))
        cur = best[4]
        if verbose:
            print(f"        + {best[1]}   (residual bad words ≤12: {best[0]})",
                  flush=True)
        if len(chosen) > 12:
            return None
    return [c[0] for c in chosen]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--max-size', type=int, default=4)
    ap.add_argument('--duty', type=float, default=0.5)
    ap.add_argument('--eps', type=int, default=1)
    args = ap.parse_args()
    set_duty(args.duty)

    e = args.eps
    EPS = make_eps(e)
    cs = cstar_dfa_from(EPS, 0, None)
    n, t, s0, acc = cs
    print(f"===== eps(g) = {e}: C* has {n} states, "
          f"aperiodic = {is_aperiodic(cs, ALPHA)} =====")
    print(f"  enumerating star-free languages up to size {args.max_size} ...")
    known = enumerate_langs(e, args.max_size)
    for i in range(n):
        di = dfa_minimize((n, t, i, acc), ALPHA)
        if di[3] == frozenset():
            print(f"  residual L{i} = 0 (empty)")
            continue
        print(f"  --- residual L{i} ---", flush=True)
        res = find_conjunction(di, known)
        print(f"    L{i} = {' & '.join(res) if res else 'NOT EXPRESSIBLE at this size'}")
    return 0


if __name__ == '__main__':
    sys.exit(main())
