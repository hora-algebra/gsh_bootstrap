#!/usr/bin/env python3
"""Designed (not searched) height-1 representation attempt for the A4 word
problem and the single-residue staged-counting languages W(h,k,r,m).

Construction under test:
  W-language: N_r = #{b : (#a before it) = r mod m}, value N_r mod k.
  Feature: TokO(opener_r, {b, C_m}, c) where
     opener_r = "Ba"*r (b* a repeated r times; reaches phase r),
     C_m = "a" + "Ba"*(m-1)  (consumes m a's, interior blocks at phases
           r+1..r+m-1, all unmarked for single-residue marks),
     c = counting modulus for completed tokens.
  Claim: N_r mod k is a function of (LC-state, TokO-state), where
     LC = (#a mod 48, #b mod 8).
  Each TokO/LC state-indicator language has generalized star height <= 1
  (opener is star-free, token counting is one star, partial tokens are
  star-free suffix factors, Boolean combinations are free).

  If the claim verifies semantically (product automaton), then W(h,k,r,m)
  has height <= 1, and hence so do:
    A4 word problem  = Boolean combo of stage-3 W's (proved in chat),
    M1, M2, FULL(=L(aab,0,4)) = Boolean combos of stage-4/8 W's.
"""

import random, sys, time
from collections import deque

# ---------------- LC ----------------
LCA, LCB = 48, 8
LC_INIT = 0
def lc_step(lc, ch):
    na, nb = divmod(lc, LCB)
    if ch == 'a':
        return ((na + 1) % LCA) * LCB + nb
    return na * LCB + ((nb + 1) % LCB)
N_LC = LCA * LCB

# ---------------- TokO feature ----------------
class TokO:
    __slots__ = ("opener", "specs", "c", "name", "states", "index",
                 "trans", "init")

    def __init__(self, opener, specs, c):
        self.opener = opener
        self.specs = tuple(specs)
        self.c = c
        self.name = f"[{opener}]{{{','.join(specs)}}}%{c}"
        self.states = []
        self.index = {}
        self.trans = {}
        self.init = self._intern(self._closure({('O', 0)}))

    def _closure(self, items):
        seen = set()
        stack = list(items)
        while stack:
            it = stack.pop()
            if it in seen:
                continue
            seen.add(it)
            if it[0] == 'O':
                p = it[1]
                if p == len(self.opener):
                    stack.append((0, -1, 0))
                elif self.opener[p] == 'B':
                    stack.append(('O', p + 1))
            else:
                r, t, p = it
                if t == -1:
                    for ti in range(len(self.specs)):
                        stack.append((r, ti, 0))
                else:
                    spec = self.specs[t]
                    if p == len(spec):
                        stack.append(((r + 1) % self.c, -1, 0))
                    elif spec[p] == 'B':
                        stack.append((r, t, p + 1))
        return frozenset(seen)

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
            for it in self.states[si]:
                if it[0] == 'O':
                    p = it[1]
                    if p < len(self.opener):
                        s = self.opener[p]
                        if s == ch:
                            nxt.add(('O', p + 1))
                        elif s == 'B' and ch == 'b':
                            nxt.add(('O', p))
                else:
                    r, t, p = it
                    if t == -1:
                        continue
                    spec = self.specs[t]
                    if p == len(spec):
                        continue
                    s = spec[p]
                    if s == ch:
                        nxt.add((r, t, p + 1))
                    elif s == 'B' and ch == 'b':
                        nxt.add((r, t, p))
            v = self._intern(self._closure(nxt))
            self.trans[key] = v
        return v

    def dfa_size(self):
        seen = {self.init}
        q = deque([self.init])
        while q:
            s = q.popleft()
            for ch in ('a', 'b'):
                n = self.step(s, ch)
                if n not in seen:
                    seen.add(n)
                    q.append(n)
        return len(seen)

def opener_for(r):
    return "Ba" * r

def conn_for(m):
    return "a" + "Ba" * (m - 1)

# ---------------- targets ----------------
class WTarget:
    """N_r mod k with stage m (marks at single residue r)."""
    def __init__(self, m, r, k):
        self.m, self.r, self.k = m, r, k
        self.name = f"W(stage{m},res{r},mod{k})"
        self.init = (0, 0)
    def step(self, s, ch):
        p, c = s
        if ch == 'a':
            return ((p + 1) % self.m, c)
        return (p, (c + (1 if p == self.r else 0)) % self.k)
    def val(self, s):
        return s[1]

def pmul(p, q):  # apply p then q
    return tuple(q[i] for i in p)

class A4Target:
    """Word problem of A4, phi(a)=(123), phi(b)=(12)(34)."""
    PA = (1, 2, 0, 3)
    PB = (1, 0, 3, 2)
    def __init__(self):
        self.name = "A4-wordproblem"
        self.init = (0, 1, 2, 3)
    def step(self, s, ch):
        return pmul(s, self.PA if ch == 'a' else self.PB)
    def val(self, s):
        return s  # full group element (identity iff (0,1,2,3))

class FullTarget:
    """binom(w,aab) mod 4."""
    def __init__(self):
        self.name = "FULL(aab mod4)"
        self.init = (0, 0)
    def step(self, s, ch):
        p, c = s
        if ch == 'a':
            return ((p + 1) % 8, c)
        f = (0, 0, 1, 3, 2, 2, 3, 1)[p]
        return (p, (c + f) % 4)
    def val(self, s):
        return s[1]

# ---------------- checks ----------------
def semantic_check_single(feat, target, cap=3_000_000):
    """Exact: is target.val a function of (lc, feat-state)? product BFS."""
    start = (LC_INIT, feat.init, target.init)
    seen = {start}
    q = deque([start])
    cell = {}
    witness = {}
    while q:
        lc, fs, tg = q.popleft()
        key = (lc, fs)
        v = target.val(tg)
        prev = cell.get(key)
        if prev is None:
            cell[key] = v
        elif prev != v:
            return False, (key, prev, v)
        for ch in ('a', 'b'):
            nx = (lc_step(lc, ch), feat.step(fs, ch), target.step(tg, ch))
            if nx not in seen:
                if len(seen) > cap:
                    return None, None
                seen.add(nx)
                q.append(nx)
    return True, len(seen)

def sample_check_multi(feats, targets, n_words, max_len, seed=11):
    rnd = random.Random(seed)
    sig2 = {}
    alive = [True] * len(targets)
    coll = [None] * len(targets)
    for _ in range(n_words):
        ln = rnd.randint(0, max_len)
        w = ''.join(rnd.choice('ab') for _ in range(ln))
        lc = LC_INIT
        fss = [f.init for f in feats]
        tgs = [t.init for t in targets]
        for ch in w:
            lc = lc_step(lc, ch)
            fss = [f.step(s, ch) for f, s in zip(feats, fss)]
            tgs = [t.step(s, ch) for t, s in zip(targets, tgs)]
        sig = (lc, tuple(fss))
        vals = tuple(t.val(s) for t, s in zip(targets, tgs))
        prev = sig2.get(sig)
        if prev is None:
            sig2[sig] = (vals, w)
        else:
            pv, pw = prev
            for i in range(len(targets)):
                if alive[i] and pv[i] != vals[i]:
                    alive[i] = False
                    coll[i] = (pw, w)
    return alive, coll

def exhaustive_check_multi(feats, targets, L):
    sig2 = {}
    alive = [True] * len(targets)
    coll = [None] * len(targets)
    frontier = [(LC_INIT, tuple(f.init for f in feats),
                 tuple(t.init for t in targets), "")]
    for depth in range(L + 1):
        nxt = []
        for lc, fss, tgs, w in frontier:
            sig = (lc, fss)
            vals = tuple(t.val(s) for t, s in zip(targets, tgs))
            prev = sig2.get(sig)
            if prev is None:
                sig2[sig] = (vals, w)
            else:
                pv, pw = prev
                for i in range(len(targets)):
                    if alive[i] and pv[i] != vals[i]:
                        alive[i] = False
                        coll[i] = (pw, w)
            if depth < L and any(alive):
                for ch in ('a', 'b'):
                    nxt.append((lc_step(lc, ch),
                                tuple(f.step(s, ch) for f, s in zip(feats, fss)),
                                tuple(t.step(s, ch) for t, s in zip(targets, tgs)),
                                w + ch))
        frontier = nxt
        if not any(alive):
            break
    return alive, coll

# ---------------- main ----------------
def main():
    print("=== single-residue W-language tests (exact semantic checks) ===",
          flush=True)
    tests = [
        # (m, r, k)
        (3, 0, 2), (3, 1, 2), (3, 2, 2),
        (4, 2, 4), (4, 3, 4),
        (8, 3, 2), (8, 4, 2), (8, 5, 2), (8, 6, 2),
    ]
    ok_all = {}
    for m, r, k in tests:
        feat = TokO(opener_for(r), ["b", conn_for(m)], k)
        tgt = WTarget(m, r, k)
        res, info = semantic_check_single(feat, tgt)
        ok_all[(m, r, k)] = res
        if res is True:
            print(f"  {tgt.name} vs {feat.name}: PROVEN function of features "
                  f"(product states: {info}, feat DFA {feat.dfa_size()})",
                  flush=True)
        elif res is False:
            print(f"  {tgt.name} vs {feat.name}: FAILS (cell {info[0]}, "
                  f"values {info[1]} vs {info[2]})", flush=True)
        else:
            print(f"  {tgt.name} vs {feat.name}: cap exceeded", flush=True)

    # negative control: wrong opener must fail
    feat = TokO(opener_for(3), ["b", conn_for(4)], 4)
    tgt = WTarget(4, 2, 4)
    res, info = semantic_check_single(feat, tgt)
    print(f"  [negative control] {tgt.name} vs wrong opener r=3: "
          f"{'FAILS as expected' if res is False else 'UNEXPECTED ' + str(res)}",
          flush=True)

    print("\n=== composite targets (sampling) ===", flush=True)
    # A4: stage-3 features
    f3 = [TokO(opener_for(r), ["b", conn_for(3)], 2) for r in range(3)]
    a4 = A4Target()
    alive, coll = sample_check_multi(f3, [a4], 400_000, 200)
    if alive[0]:
        print("  A4 vs stage-3 features: consistent on 400k random words "
              "(len<=200)", flush=True)
        alive2, coll2 = exhaustive_check_multi(f3, [a4], 15)
        print(f"  A4 exhaustive L<=15: "
              f"{'consistent' if alive2[0] else 'COLLISION ' + str(coll2[0])}",
              flush=True)
    else:
        pw, w = coll[0]
        print(f"  A4: COLLISION  '{pw}' vs '{w}'", flush=True)

    # FULL: stage-4 mod-4 features (r=2,3) + stage-8 mod-2 features (r=3..6)
    f4 = [TokO(opener_for(r), ["b", conn_for(4)], 4) for r in (2, 3)]
    f8 = [TokO(opener_for(r), ["b", conn_for(8)], 2) for r in (3, 4, 5, 6)]
    full = FullTarget()
    alive, coll = sample_check_multi(f4 + f8, [full], 150_000, 120)
    if alive[0]:
        print("  FULL(aab mod4) vs designed features: consistent on 150k "
              "random words (len<=120)", flush=True)
        alive2, coll2 = exhaustive_check_multi(f4 + f8, [full], 13)
        print(f"  FULL exhaustive L<=13: "
              f"{'consistent' if alive2[0] else 'COLLISION ' + str(coll2[0])}",
              flush=True)
    else:
        pw, w = coll[0]
        print(f"  FULL: COLLISION  '{pw}' vs '{w}'", flush=True)

if __name__ == "__main__":
    main()
