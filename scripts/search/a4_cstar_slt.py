#!/usr/bin/env python3
"""Test whether the two hard C* cores are k-locally testable over the
ANNOTATED MOVER SEQUENCE, i.e. membership is determined by the set of
sliding windows of k consecutive movers (with begin/end markers and an
adjacency bit "were there fills between?"), plus fill-position data.

If yes for small k, an explicit star-free expression follows mechanically
(finite conjunction of forbidden-window factors), which is what the Lean
formalization of N-A4-FULL-033 needs.

Marked sequence of w:  |-  b0 m1 b1 m2 ... m_n bn  -|
  mi   : mover CLASS of the i-th mover (classes: g, u, x, d for the
         same-type pattern; g, u(unused), x, d for filler -- we keep
         letter classes {g,u,x,d}; fills are the annotation)
  bi   : 1 if at least one fill letter sits between (idempotent), else 0
  b0   : fills before the first mover; bn: fills after the last mover.

A k-window is a tuple (s0, b0', s1, b1', ..., s_{k-1}) of k symbols from
{|-, -|, g,u,x,d} with adjacency bits between them (windows may include
the markers at the ends).

Method: enumerate ALLOWED windows by a product reachability computation
on the C* DFA; build the SLT-candidate DFA whose states are the last
(k-1) annotated symbols; compare with the C* DFA exactly.
"""
import sys
import itertools
from collections import deque
import os.path as _op  # noqa: E402
_GSHROOT = _op.dirname(_op.dirname(_op.dirname(_op.abspath(__file__))))
# Import by absolute path rather than a cwd-relative one: these modules are
# split across scripts/research (CI re-runs them) and scripts/search (long
# searches and negative results), and run_research.py invokes them from the
# repository root while a human runs them from anywhere.
sys.path[:0] = [_op.join(_GSHROOT, 'scripts', 'research'),
                _op.join(_GSHROOT, 'scripts', 'search')]
from a4_pattern_token_starfree import (dfa_minimize, dfa_equiv, dfa_words,
                                       cstar_dfa, is_aperiodic)
from a4_hard_cstar_forms2 import make_alpha7, CASES

BOT, TOP = '|-', '-|'          # begin / end markers


def mover_class(ch):
    return {'g': 'g', 'u': 'u', 'x': 'x', 'd1': 'd', 'd2': 'd'}[ch]


CLASS_REP = {'g': 'g', 'u': 'u', 'x': 'x', 'd': 'd1'}


def annotate(w, EPS):
    """Marked annotated sequence: list alternating symbol, bit, symbol...
    [BOT, b0, m1, b1, ..., mn, bn, TOP]."""
    seq = [BOT]
    bit = 0
    for ch in w:
        if EPS[ch] == 0:
            bit = 1
        else:
            seq.append(bit)
            seq.append(mover_class(ch))
            bit = 0
    seq.append(bit)
    seq.append(TOP)
    return seq


def windows(seq, k):
    """All k-symbol windows (symbols incl. markers) with their bits."""
    syms = seq[0::2]
    bits = seq[1::2]
    out = set()
    for i in range(len(syms) - k + 1):
        win = tuple(itertools.chain.from_iterable(
            (syms[i + j], bits[i + j]) for j in range(k - 1))) + \
            (syms[i + k - 1],)
        out.add(win)
    return out


def allowed_windows(dfa, alpha, EPS, k, maxlen):
    """Windows occurring in SOME accepted word (bounded exhaustive +
    breadth-first over the DFA to length maxlen; maxlen must comfortably
    exceed any pumping in a 5-state machine, so >= 2k+10 is plenty)."""
    n, t, s, acc = dfa
    allow = set()
    # BFS over (state, recent annotated suffix) is complex; instead use
    # exhaustive words over class representatives with one fill letter.
    reps = ['g', 'u', 'x', 'd1']
    fill = 'f1'
    def accepted(w):
        st = s
        for ch in w:
            st = t[st][ch]
        return st in acc
    # enumerate words as annotated mover sequences directly:
    # choose mover count 0..maxmov, bits pattern; realize with reps/fill.
    maxmov = maxlen
    for nm in range(0, maxmov + 1):
        for movs in itertools.product(reps, repeat=nm):
            for bits in itertools.product((0, 1), repeat=nm + 1):
                w = []
                if bits[0]:
                    w.append(fill)
                for i, m in enumerate(movs):
                    w.append(m)
                    if bits[i + 1]:
                        w.append(fill)
                if accepted(w):
                    allow |= windows(annotate(w, EPS), k)
        # prune: nothing new for two consecutive sizes -> stop early
    return allow


def slt_dfa(allow, k):
    """DFA over the 5-letter class alphabet {g,u,x,d,f} implementing:
    every k-window of the marked annotated sequence is in allow.
    State: (last (k-1) annotated symbols as tuple, pending bit) or DEAD.
    Symbols in state tuples: markers or mover classes with bits between.
    """
    alpha = ['g', 'u', 'x', 'd1', 'd2', 'f1', 'f2']
    def cls(ch):
        return 'f' if ch in ('f1', 'f2') else mover_class(ch)
    DEAD = 'DEAD'
    start = ((BOT,), 0)
    idx = {start: 0, DEAD: 1}
    order = [start, DEAD]
    trans = []
    def win_ok(hist, bit, sym):
        """If appending (bit, sym) to hist completes a k-window, check."""
        h = hist + (bit, sym)
        # h alternates sym,bit,...; windows are suffixes of length k syms
        syms = h[0::2]
        if len(syms) >= k:
            win = h[-(2 * k - 1):]
            return win in allow
        # shorter than k: it's a prefix window; check only at TOP
        if sym == TOP:
            return h in allow or any(
                w[:len(h)] == h for w in allow)  # prefix of allowed?
        return True
    for st in order:
        row = {}
        if st == DEAD:
            for ch in alpha:
                row[ch] = idx[DEAD]
            trans.append(row)
            continue
        hist, bit = st
        for ch in alpha:
            c = cls(ch)
            if c == 'f':
                ns = (hist, 1)
            else:
                if not win_ok(hist, bit, c):
                    ns = DEAD
                else:
                    h = hist + (bit, c)
                    syms = h[0::2]
                    if len(syms) >= k:
                        h = h[-(2 * (k - 1) - 1):] if k >= 2 else ()
                    ns = (h, 0)
            if ns not in idx:
                idx[ns] = len(order)
                order.append(ns)
            row[ch] = idx[ns]
        trans.append(row)
    # accepting: appending (bit, TOP) must be OK for all suffix windows
    acc = set()
    for st, i in idx.items():
        if st == 'DEAD':
            continue
        hist, bit = st
        if win_ok(hist, bit, TOP):
            acc.add(i)
    return dfa_minimize((len(order), trans, 0, frozenset(acc)), alpha)


def main():
    e = 1
    alpha, EPS = make_alpha7(e)
    for name, match in CASES:
        cs = dfa_minimize(cstar_dfa(alpha, EPS, match), alpha)
        print(f"=== {name} ===")
        for k in (2, 3, 4):
            allow = allowed_windows(cs, alpha, EPS, k, maxlen=2 * k + 4)
            cand = slt_dfa(allow, k)
            w = dfa_equiv(cand, cs, alpha)
            print(f"  k={k}: windows={len(allow)}  "
                  f"{'EQUIVALENT (SLT!)' if w is None else 'witness ' + repr(w)}")
            if w is None:
                for win in sorted(allow, key=repr):
                    print(f"      {win}")
                break


if __name__ == "__main__":
    main()
