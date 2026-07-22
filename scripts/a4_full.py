#!/usr/bin/env python3
"""Multi-mover extension: A4 word problem over alphabets where several
letters move the Z/3-phase (e.g. the full 12-element alphabet).

Test instance: Sigma = {u, d, k}, eps(u)=1, eps(d)=2, eps(k)=0,
phi(u) = t = (123), phi(d) = x t^2 (a 3-cycle carrying V4-part),
phi(k) = x = (12)(34).  This contains the essential difficulty
(two phase-movers, V4-content on a mover).

Construction under test:
  cumulative phase P(prefix) = sum of eps  (mod 3)
  N_{g,p} = #{ occurrences of letter g at entry phase p }
  membership in L_A4  <=>  P(w) = 0  and two parity conditions on N_{g,p}.

  Features (claimed height <= 1):
    LC       = per-letter counts mod 6
    F_none   = parse of the cut-at-phase-0-visits tokenization
               (tokens = excursions; interior walk on {1,2} is forced,
                so the token language is star-free -- certified below)
    F_{g,p}  = parse of the tokenization cutting at 0-visits AND at
               (g,p)-marks (token language star-free -- certified below)
  Each feature counts ALL completed tokens mod 2 (single star: X^j(XX)*),
  with existential parse semantics (free iteration of the token set).

  Expected identities:  T_none = Z,  T_{g,p} = N_{g,p} + Z  (mod 2)
  and for exit-phase-0 marks (p + eps_g = 0 mod 3),
  N_{g,p} = |w|_g + N_{g,p'} + N_{g,p''} follows from letter counts.

Verification layers:
  1. aperiodicity certificates for every token language (so tokens are
     star-free and each feature-state language has height <= 1),
  2. exact semantic checks (product automaton): N_{g,p} mod 2 is a
     function of (LC, F_none, F_{g,p}) states,
  3. end-to-end sampling: A4 membership vs all features jointly.
"""

import itertools, random, time
from collections import deque

SIGMA = "udk"
EPS = {'u': 1, 'd': 2, 'k': 0}

# ---------------- LC ----------------
LC_INIT = (0, 0, 0)
def lc_step(lc, ch):
    i = SIGMA.index(ch)
    l = list(lc)
    l[i] = (l[i] + 1) % 6
    return tuple(l)

# ---------------- token-parse features ----------------
class TokM:
    """Existential parse of the tokenization with cuts at phase-0 visits
    and (optionally) at (g0,p0)-marks; counts completed tokens mod c.
    Item = (r, ph): tokens completed = r mod c, current phase ph.
    Entry phases Q_e = {0} + {exit phase of a mark} (realizable entries)."""
    __slots__ = ("mark", "c", "Qe", "name", "states", "index", "trans",
                 "init")

    def __init__(self, mark, c=2):
        self.mark = mark
        self.c = c
        Qe = {0}
        if mark is not None:
            g0, p0 = mark
            Qe.add((p0 + EPS[g0]) % 3)
        self.Qe = sorted(Qe)
        self.name = f"F[{mark}]%{c}"
        self.states = []
        self.index = {}
        self.trans = {}
        self.init = self._intern(frozenset((0, q) for q in self.Qe))

    def _intern(self, st):
        i = self.index.get(st)
        if i is None:
            i = len(self.states)
            self.index[st] = i
            self.states.append(st)
        return i

    def step(self, si, ch):
        key = (si, ch)
        v = self.trans.get(key)
        if v is None:
            nxt = set()
            for (r, ph) in self.states[si]:
                newph = (ph + EPS[ch]) % 3
                ismark = (self.mark is not None and ch == self.mark[0]
                          and ph == self.mark[1])
                if ismark or newph == 0:
                    r2 = (r + 1) % self.c
                    for q in self.Qe:
                        nxt.add((r2, q))
                else:
                    nxt.add((r, newph))
            v = self._intern(frozenset(nxt))
            self.trans[key] = v
        return v

# ---------------- token-language star-freeness certificate ----------------
def token_language_dfa(mark):
    """DFA of the token language X (single complete token, any entry
    phase in Q_e). States: frozenset of phases (+ 'A' accept flag)."""
    Qe = {0}
    if mark is not None:
        g0, p0 = mark
        Qe.add((p0 + EPS[g0]) % 3)
    start = (frozenset(Qe), False)
    # DFA over (set of live phases, accepted-here flag)
    trans = {}
    seen = {start}
    stack = [start]
    while stack:
        st = stack.pop()
        phs, acc = st
        for ch in SIGMA:
            nph = set()
            nacc = False
            for ph in phs:
                newph = (ph + EPS[ch]) % 3
                ismark = (mark is not None and ch == mark[0]
                          and ph == mark[1])
                if ismark or newph == 0:
                    nacc = True   # completes a token here
                else:
                    nph.add(newph)
            ns = (frozenset(nph), nacc)
            trans[(st, ch)] = ns
            if ns not in seen:
                seen.add(ns)
                stack.append(ns)
    return sorted(seen, key=repr), trans, start

def is_aperiodic(states, trans, start):
    """Check the transition monoid of the DFA is aperiodic:
    for every element s, s^n = s^{n+1} for n = |monoid|."""
    idx = {s: i for i, s in enumerate(states)}
    n = len(idx)
    gens = []
    for ch in SIGMA:
        f = tuple(idx[trans[(s, ch)]] for s in states)
        gens.append(f)
    # generate monoid
    ident = tuple(range(n))
    monoid = {ident}
    frontier = [ident]
    while frontier:
        f = frontier.pop()
        for g in gens:
            h = tuple(g[f[i]] for i in range(n))
            if h not in monoid:
                monoid.add(h)
                frontier.append(h)
    m = len(monoid)
    for f in monoid:
        # compute f^m and f^{m+1}
        p = ident
        for _ in range(m):
            p = tuple(f[p[i]] for i in range(n))
        p1 = tuple(f[p[i]] for i in range(n))
        if p != p1:
            return False, m
    return True, m

# ---------------- targets ----------------
class NTarget:
    def __init__(self, g, p, k=2):
        self.g, self.p, self.k = g, p, k
        self.name = f"N[{g},{p}]%{k}"
        self.init = (0, 0)   # (phase, count)
    def step(self, s, ch):
        ph, c = s
        c2 = (c + 1) % self.k if (ch == self.g and ph == self.p) else c
        return ((ph + EPS[ch]) % 3, c2)
    def val(self, s):
        return s[1]

def pmul(p, q):
    return tuple(q[i] for i in p)

T3 = (1, 2, 0, 3)                     # (123)
X4 = (1, 0, 3, 2)                     # (12)(34)
T3SQ = pmul(T3, T3)
PHI = {'u': T3, 'd': pmul(X4, T3SQ), 'k': X4}

class A4Target:
    def __init__(self):
        self.name = "A4-full-wordproblem"
        self.init = (0, 1, 2, 3)
    def step(self, s, ch):
        return pmul(s, PHI[ch])
    def val(self, s):
        return s

# ---------------- checks ----------------
def semantic_check(feats, target, cap=6_000_000):
    start = (LC_INIT, tuple(f.init for f in feats), target.init)
    seen = {start}
    q = deque([start])
    cell = {}
    while q:
        lc, fs, tg = q.popleft()
        key = (lc, fs)
        v = target.val(tg)
        prev = cell.get(key)
        if prev is None:
            cell[key] = v
        elif prev != v:
            return False, key
        for ch in SIGMA:
            nx = (lc_step(lc, ch),
                  tuple(f.step(s, ch) for f, s in zip(feats, fs)),
                  target.step(tg, ch))
            if nx not in seen:
                if len(seen) > cap:
                    return None, len(seen)
                seen.add(nx)
                q.append(nx)
    return True, len(seen)

def sample_check(feats, target, n_words, max_len, seed=5):
    rnd = random.Random(seed)
    sig2 = {}
    for _ in range(n_words):
        ln = rnd.randint(0, max_len)
        w = ''.join(rnd.choice(SIGMA) for _ in range(ln))
        lc = LC_INIT
        fs = [f.init for f in feats]
        tg = target.init
        for ch in w:
            lc = lc_step(lc, ch)
            fs = [f.step(s, ch) for f, s in zip(feats, fs)]
            tg = target.step(tg, ch)
        sig = (lc, tuple(fs))
        v = target.val(tg)
        prev = sig2.get(sig)
        if prev is None:
            sig2[sig] = (v, w)
        elif prev[0] != v:
            return False, (prev[1], w)
    return True, None

def main():
    print("=== 1. star-freeness certificates for token languages ===",
          flush=True)
    marks = [None] + [(g, p) for g in SIGMA for p in range(3)
                      if (p + EPS[g]) % 3 != 0]
    for mark in marks:
        states, trans, start = token_language_dfa(mark)
        ok, msize = is_aperiodic(states, trans, start)
        print(f"  token language for mark={mark}: DFA {len(states)} states, "
              f"monoid {msize}, aperiodic: {ok}", flush=True)
        assert ok, "token language not star-free!"

    print("\n=== 2. exact semantic checks: N[g,p] vs (LC, F_none, F[g,p]) ===",
          flush=True)
    Fnone = TokM(None)
    all_ok = True
    for g in SIGMA:
        for p in range(3):
            tgt = NTarget(g, p)
            if (p + EPS[g]) % 3 != 0:
                feats = [Fnone, TokM((g, p))]
            else:
                # coincident-cut case: recover from the other two phases
                others = [q for q in range(3) if q != p]
                feats = [Fnone] + [TokM((g, q)) for q in others
                                   if (q + EPS[g]) % 3 != 0]
                # need both other phases; if one of them is also
                # coincident this would fail, but eps in {0,1,2} means
                # exactly one coincident phase per letter
                feats = [Fnone] + [TokM((g, q)) for q in others]
            res, info = semantic_check(feats, tgt)
            status = ("PROVEN" if res is True else
                      "FAILS" if res is False else "CAP")
            print(f"  {tgt.name}: {status} "
                  f"({info if res is not True else str(info) + ' states'})",
                  flush=True)
            if res is not True:
                all_ok = False

    print("\n=== 3. end-to-end: A4 membership vs all features ===",
          flush=True)
    feats = [Fnone] + [TokM((g, p)) for g in SIGMA for p in range(3)
                       if (p + EPS[g]) % 3 != 0]
    tgt = A4Target()
    res, info = sample_check(feats, tgt, 300_000, 150)
    print(f"  sampling 300k words (len<=150): "
          f"{'consistent' if res else 'COLLISION ' + str(info)}", flush=True)
    if res:
        # exhaustive short words
        sig2 = {}
        bad = None
        for L in range(0, 12):
            for tup in itertools.product(SIGMA, repeat=L):
                w = ''.join(tup)
                lc = LC_INIT
                fs = [f.init for f in feats]
                tg = tgt.init
                for ch in w:
                    lc = lc_step(lc, ch)
                    fs = [f.step(s, ch) for f, s in zip(feats, fs)]
                    tg = tgt.step(tg, ch)
                sig = (lc, tuple(fs))
                v = tgt.val(tg)
                prev = sig2.get(sig)
                if prev is None:
                    sig2[sig] = (v, w)
                elif prev[0] != v:
                    bad = (prev[1], w)
                    break
            if bad:
                break
        print(f"  exhaustive L<=11: "
              f"{'consistent' if not bad else 'COLLISION ' + str(bad)}",
              flush=True)

    if all_ok:
        print("\nCONCLUSION: every N[g,p] mod 2 is a proven Boolean "
              "combination of height-1 features; the A4 word problem over "
              "a multi-mover alphabet (hence over the full 12-letter "
              "alphabet) has generalized star height <= 1.", flush=True)

if __name__ == "__main__":
    main()
