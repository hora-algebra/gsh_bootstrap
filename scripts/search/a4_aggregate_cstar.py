#!/usr/bin/env python3
"""The AGGREGATE cut-core `C*` for a mover `g` (obligation N-A4-FULL-033).

`a4_pattern_token_starfree.py` treats the three digram pattern classes
`('2',h,g)` separately.  For the GF(2) recovery of
`scripts/a4_pair_recovery_identity.py` only the *sum over all h != g* is
needed, i.e. the single pattern

    matched landing := landing letter is g and the previous letter is not g
                       (a landing at position 1 counts as matched)

which gives one cut system per mover instead of three.  This script

  1. builds the corresponding `C*` DFA ("every landing matched, word ends at
     a landing"), minimises it and decides aperiodicity exactly;
  2. searches, by size-ordered enumeration modulo minimal-DFA identity, for
     explicit star-free expressions for `C*` and for the residual language
     of every state -- these are exactly the expressions consumed by the
     Lean derivative certificate `GSH/Regex/Certificate.lean`.

Alphabet classes (fully general: the token automaton only reads a letter's
phase class and whether it equals `g`):
    g        the distinguished mover, phase e
    u1, u2   other movers of phase e
    d1, d2   movers of phase e' = 3 - e
    f1, f2   fillers (phase 0)

RESULTS (2026-07-28)
--------------------
* The minimal DFA of `C*` has 5 states and is APERIODIC, and it is the *same*
  automaton for `e = 1` and `e = 2`, so one parameterised Lean construction
  covers all eight movers.  State table (0 = phase 0 = accept, 1 = phase 1,
  2 = phase 2 with previous letter != g, 4 = phase 2 with previous letter g,
  3 = dead):

      0: g->1 u->1 d->2 f->3
      1: g->4 u->2 d->3 f->1
      2: g->0 u->3 d->1 f->2
      4: g->3 u->3 d->1 f->2

  Note `L4 = L2 \\ g.Sigma*`, so only three distinct nonempty residuals must
  be exhibited for the Lean derivative certificate.
* Size-ordered enumeration of star-free expressions over the generators
  {eps, Sigma*, g, U, D, F} modulo language identity finds NO expression for
  any of the four residuals up to size 6 (774 293 distinct languages
  enumerated).  Blind search beyond that is not practical in this
  implementation; a guided construction (or Schuetzenberger's theorem) is
  needed.  Useful facts for a guided construction: `gggg`, `uuu`, `ddd` are
  forbidden factors, and `uu`, `dd`, `ud` are "reset" words (after them the
  state is known), while `f` and `gd` preserve the ambiguity between the two
  phase-2 states -- which is why the automaton is aperiodic but not definite.
* Structural fact explaining why the *easy* classes are easy, and why no
  choice of end-pattern avoids the hard ones: for a fixed word `pi`,

      R ∩ Sigma*.pi  =  {pi}   whenever  phaseSum(pi) = 0 (mod 3)

  (if `r = p.pi` is a first return and `phaseSum(pi) = 0` then
  `phaseSum(p) = 0`, so `p` would be an earlier landing unless `p = eps`),
  and it is infinite whenever `phaseSum(pi) != 0`.  The two closed forms
  `C* = h*` (h a filler, `phaseSum(h) = 0`) and `C* = (dg)*`
  (`phaseSum(dg) = 0`) are exactly the phase-0 patterns; every pattern that
  isolates a *single* `N[g,p]` for a mover `g` necessarily has phase
  `!= 0`, hence an infinite cut core.
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
    dfa_minimize, dfa_product, dfa_compl, dfa_concat, dfa_equiv, dfa_words,
    to_dfa, atoms, cat, uni, inter, comp, is_aperiodic)

ALPHA = ['g', 'u1', 'u2', 'd1', 'd2', 'f1', 'f2']

# ---- CPU throttling -------------------------------------------------------
# The enumeration below is CPU-bound; keep this process at a bounded duty
# cycle so it does not saturate a core.  `--duty D` (default 0.5) sleeps
# (1-D)/D seconds per D seconds of work.
_DUTY = [0.5, time.perf_counter()]


def set_duty(d):
    _DUTY[0] = max(0.05, min(1.0, d))
    _DUTY[1] = time.perf_counter()


def throttle(slice_s=0.05):
    """Yield the CPU periodically to hold the configured duty cycle."""
    d = _DUTY[0]
    if d >= 1.0:
        return
    now = time.perf_counter()
    worked = now - _DUTY[1]
    if worked >= slice_s:
        time.sleep(worked * (1.0 - d) / d)
        _DUTY[1] = time.perf_counter()


def make_eps(e):
    ep = 3 - e
    return {'g': e, 'u1': e, 'u2': e, 'd1': ep, 'd2': ep, 'f1': 0, 'f2': 0}


def matched(prev, ch):
    return ch == 'g' and prev != 'g'


def cstar_dfa_from(EPS, start_phase, start_prev, q=0):
    """`C*` seen from the state `(phase, previous letter)`."""
    DEAD = ('DEAD',)
    start = (start_phase, start_prev)
    idx = {start: 0}
    order = [start]
    trans = []
    for st in order:
        row = {}
        if st == DEAD:
            for ch in ALPHA:
                row[ch] = idx[DEAD]
            trans.append(row)
            continue
        ph, prev = st
        for ch in ALPHA:
            nph = (ph + EPS[ch]) % 3
            ns = DEAD if (nph == q and not matched(prev, ch)) else (nph, ch)
            if ns not in idx:
                idx[ns] = len(order)
                order.append(ns)
            row[ch] = idx[ns]
        trans.append(row)
    acc = frozenset(i for st, i in idx.items() if st != DEAD and st[0] == q)
    return dfa_minimize((len(order), trans, 0, acc), ALPHA)


# ------------------------------------------------------------------ search

def canon(dfa):
    """Canonical key of a minimal DFA (BFS-renumbered)."""
    n, t, s, a = dfa
    order = [s]
    seen = {s: 0}
    for st in order:
        for ch in ALPHA:
            nx = t[st][ch]
            if nx not in seen:
                seen[nx] = len(order)
                order.append(nx)
    rows = tuple(tuple(seen[t[st][ch]] for ch in ALPHA) for st in order)
    return (len(order), rows, frozenset(seen[x] for x in a if x in seen))


def seeds(e):
    """Size-1 generators: the empty word, Sigma*, and the four letter
    classes (as single-letter languages)."""
    EPS = make_eps(e)
    same = [c for c in ALPHA if EPS[c] == e and c != 'g']
    other = [c for c in ALPHA if EPS[c] == 3 - e]
    fill = [c for c in ALPHA if EPS[c] == 0]
    out = {
        'eps': __import__('a4_pattern_token_starfree').EPSW,
        'U': comp(atoms(frozenset())),
        'G': atoms(frozenset(['g'])),
        'Um': atoms(frozenset(same)),
        'D': atoms(frozenset(other)),
        'F': atoms(frozenset(fill)),
    }
    return out


def search(targets, e, max_size, verbose=True):
    """Size-ordered enumeration of star-free expressions modulo language
    identity.  `targets` is a dict name -> minimal DFA; returns a dict
    name -> printable expression (missing keys were not found)."""
    tgt_keys = {canon(d): name for name, d in targets.items()}
    found = {}
    layers = {1: {}}
    for name, expr in seeds(e).items():
        d = dfa_minimize(to_dfa(expr, ALPHA), ALPHA)
        layers[1].setdefault(canon(d), (name, expr, d))
    known = dict(layers[1])
    for k in known:
        if k in tgt_keys:
            found[tgt_keys[k]] = known[k][0]

    for size in range(2, max_size + 1):
        layers[size] = {}
        # complement of a smaller expression
        for k, (nm, ex, d) in list(layers[size - 1].items()):
            nd = dfa_minimize(dfa_compl(d), ALPHA)
            key = canon(nd)
            if key not in known:
                item = (f"~({nm})", comp(ex), nd)
                layers[size][key] = item
                known[key] = item
        # binary combinations
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
        for k in layers[size]:
            if k in tgt_keys and tgt_keys[k] not in found:
                found[tgt_keys[k]] = layers[size][k][0]
        if verbose:
            print(f"      size {size}: {len(layers[size])} new languages "
                  f"({len(known)} total); found so far: {sorted(found)}",
                  flush=True)
        if len(found) == len(targets):
            break
    return found


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--max-size', type=int, default=5)
    ap.add_argument('--no-search', action='store_true')
    ap.add_argument('--duty', type=float, default=0.5,
                    help='CPU duty cycle of the search (default 0.5)')
    args = ap.parse_args()
    set_duty(args.duty)

    for e in (1, 2):
        EPS = make_eps(e)
        print(f"===== eps(g) = {e} =====")
        cs = cstar_dfa_from(EPS, 0, None)
        n, t, s0, acc = cs
        print(f"  C* minimal DFA: {n} states, start {s0}, accept {sorted(acc)}, "
              f"aperiodic = {is_aperiodic(cs, ALPHA)}")
        for i in range(n):
            print("    state %d: %s" % (
                i, ', '.join(f"{c}->{t[i][c]}" for c in ALPHA)))
        print("    shortest words:", dfa_words(cs, ALPHA, 7, 8))
        if args.no_search:
            continue
        targets = {}
        for i in range(n):
            di = dfa_minimize((n, t, i, acc), ALPHA)
            if di[3] == frozenset():
                print(f"    residual from state {i}: empty language (= 0)")
                continue
            targets[f"L{i}"] = di
        print(f"    searching {sorted(targets)} up to size {args.max_size} ...")
        res = search(targets, e, args.max_size, verbose=True)
        for name in sorted(targets):
            print(f"      {name} = {res.get(name, 'NOT FOUND')}")
        if len(res) == len(targets):
            print("    all residuals expressed star-free.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
