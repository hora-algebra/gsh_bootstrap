#!/usr/bin/env python3
"""Search for generalized-star-height-1 representations of M1 / M2,
the two components of the candidate language L(aab,0,4).

Targets (all defined on w in {a,b}*, m_j = number of a's before j-th b):
  Thomas : #{b : a-count even} mod 2                       (known height 1)
  PST    : binom(w,aab) mod 2 = #{b : a-count%4 in {2,3}} mod 2   (known height 1)
  M1     : #{b : a-count%4 in {2,3}} mod 4                 (open)
  M2     : #{b : a-count%8 in {3,4,5,6}} mod 2             (open)
  FULL   : binom(w,aab) mod 4 = (M1 + 2*M2) mod 4          (open, the candidate)

Feature languages (each provably of generalized star height <= 1):
  LC       : (#a mod 32, #b mod 8)          -- commutative counting
  TOK(X,c) : determinized state of the counting NFA for X*-factorisations
             with token count mod c; X a finite set of tokens over {a,b,B},
             B = b* (so each token is star-free, X* is one star).

Test: is the target value a function of the joint feature state?
  - sampling check over all words of length <= L  (filter, gives counterexample pairs)
  - semantic check via product automaton          (machine-checked proof if it passes)
"""

import random, sys, time
from itertools import combinations

# ---------------- target automaton ----------------
# state = (p, c1, c2, cT): p = #a mod 8, c1 = M1-count mod 4,
# c2 = M2-count mod 2, cT = Thomas-count mod 2
T_INIT = (0, 0, 0, 0)

def t_step(s, ch):
    p, c1, c2, cT = s
    if ch == 'a':
        return ((p + 1) % 8, c1, c2, cT)
    return (p,
            (c1 + (1 if p % 4 in (2, 3) else 0)) % 4,
            (c2 + (1 if p in (3, 4, 5, 6) else 0)) % 2,
            (cT + (1 if p % 2 == 0 else 0)) % 2)

TARGETS = [
    ("Thomas(m2,k2)", lambda s: s[3]),
    ("PST(aab mod2)", lambda s: s[1] % 2),
    ("M1(mod4)",      lambda s: s[1]),
    ("M2(mod2)",      lambda s: s[2]),
    ("FULL(aab mod4)", lambda s: (s[1] + 2 * s[2]) % 4),
]
NT = len(TARGETS)

def brute_binom_aab(w):
    ca = caa = caab = 0
    for ch in w:
        if ch == 'a':
            caa += ca
            ca += 1
        else:
            caab += caa
    return caab

def selftest():
    rnd = random.Random(0)
    for _ in range(3000):
        w = ''.join(rnd.choice('ab') for _ in range(rnd.randint(0, 40)))
        s = T_INIT
        for ch in w:
            s = t_step(s, ch)
        assert (s[1] + 2 * s[2]) % 4 == brute_binom_aab(w) % 4, w
        assert s[1] % 2 == brute_binom_aab(w) % 2, w
    print("selftest OK: FULL = M1 + 2*M2 (mod 4), PST = M1 mod 2")

# ---------------- LC feature ----------------
# encoded as integer lc = (na%32)*8 + (nb%8)
LC_INIT = 0

def lc_step(lc, ch):
    na, nb = lc >> 3, lc & 7
    if ch == 'a':
        return (((na + 1) % 32) << 3) | nb
    return (na << 3) | ((nb + 1) % 8)

# ---------------- token feature ----------------
class Tok:
    __slots__ = ("specs", "c", "name", "states", "index", "trans", "init")

    def __init__(self, specs, c):
        self.specs = tuple(specs)
        self.c = c
        self.name = "{" + ",".join(specs) + "}%%" + str(c)
        self.states = []
        self.index = {}
        self.trans = {}
        self.init = self._intern(self._closure({(0, -1, 0)}))

    def _closure(self, items):
        seen = set()
        stack = list(items)
        while stack:
            it = stack.pop()
            if it in seen:
                continue
            seen.add(it)
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
            for (r, t, p) in self.states[si]:
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

# ---------------- sampling check ----------------
def sample_check(tok, L):
    """BFS all words length <= L; signature = (lc, tokstate).
    Returns (alive per target, counterexample pairs, nodes visited)."""
    sig2 = {}
    alive = [True] * NT
    coll = [None] * NT
    frontier = [(LC_INIT, tok.init, T_INIT, "")]
    nodes = 0
    for depth in range(L + 1):
        nxt = []
        for lc, ts, tg, w in frontier:
            nodes += 1
            sig = (lc, ts)
            vals = tuple(f(tg) for _, f in TARGETS)
            prev = sig2.get(sig)
            if prev is None:
                sig2[sig] = (vals, w)
            else:
                pv, pw = prev
                for i in range(NT):
                    if alive[i] and pv[i] != vals[i]:
                        alive[i] = False
                        coll[i] = (pw, w)
            if depth < L and any(alive):
                nxt.append((lc_step(lc, 'a'), tok.step(ts, 'a'),
                            t_step(tg, 'a'), w + 'a'))
                nxt.append((lc_step(lc, 'b'), tok.step(ts, 'b'),
                            t_step(tg, 'b'), w + 'b'))
        frontier = nxt
        if not any(alive):
            break
    return alive, coll, nodes

def sample_check_pair(tok1, tok2, L):
    sig2 = {}
    alive = [True] * NT
    coll = [None] * NT
    frontier = [(LC_INIT, tok1.init, tok2.init, T_INIT, "")]
    for depth in range(L + 1):
        nxt = []
        for lc, t1, t2, tg, w in frontier:
            sig = (lc, t1, t2)
            vals = tuple(f(tg) for _, f in TARGETS)
            prev = sig2.get(sig)
            if prev is None:
                sig2[sig] = (vals, w)
            else:
                pv, pw = prev
                for i in range(NT):
                    if alive[i] and pv[i] != vals[i]:
                        alive[i] = False
                        coll[i] = (pw, w)
            if depth < L and any(alive):
                nxt.append((lc_step(lc, 'a'), tok1.step(t1, 'a'),
                            tok2.step(t2, 'a'), t_step(tg, 'a'), w + 'a'))
                nxt.append((lc_step(lc, 'b'), tok1.step(t1, 'b'),
                            tok2.step(t2, 'b'), t_step(tg, 'b'), w + 'b'))
        frontier = nxt
        if not any(alive):
            break
    return alive, coll

# ---------------- semantic check (product automaton) ----------------
def semantic_check(tok, cap=600000):
    """Exact check: is each target value a function of (lc, tokstate)?
    Returns list of bool per target, or None if state cap exceeded."""
    from collections import deque
    start = (LC_INIT, tok.init, T_INIT)
    seen = {start}
    q = deque([start])
    cell = {}
    while q:
        lc, ts, tg = q.popleft()
        key = (lc, ts)
        d = cell.get(key)
        if d is None:
            d = [set() for _ in range(NT)]
            cell[key] = d
        for i, (_, f) in enumerate(TARGETS):
            d[i].add(f(tg))
        for ch in ('a', 'b'):
            nx = (lc_step(lc, ch), tok.step(ts, ch), t_step(tg, ch))
            if nx not in seen:
                if len(seen) > cap:
                    return None
                seen.add(nx)
                q.append(nx)
    return [all(len(d[i]) == 1 for d in cell.values()) for i in range(NT)]

# ---------------- token pools ----------------
MARKS = ["b", "ab", "ba", "aab", "baa", "aba", "abb", "bab", "bba"]
CONNS = ["aa", "aaa", "aaaa",
         "aBa", "aaBa", "aBaa", "aaBaa",
         "aBaBa", "aaBaBa", "aBaBaa",
         "aBaBaBa", "aaBaBaBa", "aBaBaBaa",
         "aBaBaBaBa", "aaBaBaBaBa", "aBaBaBaBaa"]

HAND = [
    ["b", "aBa"],                          # Thomas's classic tiling
    ["b", "ab", "aBaBa", "aaBaBa"],        # hand design for M1
    ["b", "ab", "aBaBaBaBa", "aaBaBaBaBa"],  # hand design for M2
    ["b", "aBaBaBa"],
    ["b", "aBa", "aBaBa"],
    ["b", "aBa", "aBaBaBa"],
]

def gen_sets():
    seen = set()
    out = []

    def add(toks):
        key = tuple(sorted(toks))
        if key not in seen:
            seen.add(key)
            out.append(list(toks))

    for h in HAND:
        add(h)
    for m in MARKS:
        for c in CONNS:
            add([m, c])
    for m2 in combinations(MARKS, 2):
        for c in CONNS:
            add(list(m2) + [c])
    for m in MARKS:
        for c2 in combinations(CONNS, 2):
            add([m] + list(c2))
    for m2 in combinations(MARKS, 2):
        for c2 in combinations(CONNS, 2):
            add(list(m2) + list(c2))
    return out

# ---------------- main ----------------
def main():
    t0 = time.time()
    selftest()
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else 600.0

    # step 1: validate pipeline on the classic control
    ctl = Tok(["b", "aBa"], 4)
    ok = semantic_check(ctl)
    print(f"[control] semantic check for {ctl.name}: "
          f"{[TARGETS[i][0] for i in range(NT) if ok and ok[i]] if ok else 'CAP'}")

    # step 2: big sweep, single token feature
    sets = gen_sets()
    rnd = random.Random(1)
    rnd.shuffle(sets)
    # hand designs first
    sets = [s for s in HAND] + [s for s in sets if sorted(s) not in
                                [sorted(h) for h in HAND]]
    print(f"sweep over {len(sets)} token sets, words up to length {L}, "
          f"budget {budget}s")
    survivors = {i: [] for i in range(NT)}
    examples = {}
    tested = 0
    for toks in sets:
        if time.time() - t0 > budget:
            print(f"  time budget reached after {tested} sets")
            break
        tok = Tok(toks, 4)
        alive, coll, _ = sample_check(tok, L)
        tested += 1
        for i in range(NT):
            if alive[i]:
                survivors[i].append(toks)
            elif i >= 2 and tuple(toks) not in examples:
                examples[tuple(toks)] = (i, coll[i])
    print(f"tested {tested} sets in {time.time()-t0:.1f}s")
    for i in range(NT):
        print(f"  {TARGETS[i][0]}: {len(survivors[i])} sample-survivors")
        for toks in survivors[i][:10]:
            print(f"      {toks}")

    # step 3: semantic check on survivors of the open targets
    proven = []
    for i in (2, 3, 4):
        for toks in survivors[i][:40]:
            tok = Tok(toks, 4)
            ok = semantic_check(tok)
            if ok is None:
                print(f"[semantic] {tok.name}: state cap exceeded")
            elif ok[i]:
                print(f"[semantic] PROOF: {TARGETS[i][0]} is a Boolean "
                      f"combination of LC and {tok.name} !!")
                proven.append((i, toks))
            else:
                print(f"[semantic] {tok.name}: passes samples up to {L} "
                      f"but fails semantically for {TARGETS[i][0]}")

    # step 4: counterexample certificates for the hand designs
    print("\ncounterexample pairs (same features, different target value):")
    for h in HAND:
        tok = Tok(h, 4)
        alive, coll, _ = sample_check(tok, L)
        for i in range(NT):
            if not alive[i] and i >= 1:
                pw, w = coll[i]
                print(f"  {tok.name} / {TARGETS[i][0]}: "
                      f"'{pw}' vs '{w}'")

    # step 5: pairs of token features from a shortlist (sampling only)
    if not proven:
        short = [Tok(h, 4) for h in HAND] + \
                [Tok(s, 4) for s in survivors[2][:6]] + \
                [Tok(s, 4) for s in survivors[3][:6]]
        # dedupe by name
        byname = {}
        for t in short:
            byname[t.name] = t
        short = list(byname.values())[:14]
        print(f"\npair sweep over {len(short)} shortlisted features:")
        found = 0
        for t1, t2 in combinations(short, 2):
            if time.time() - t0 > budget * 2:
                print("  pair budget reached")
                break
            alive, coll = sample_check_pair(t1, t2, min(L, 12))
            for i in (2, 3, 4):
                if alive[i]:
                    print(f"  sample-consistent (L<={min(L,12)}): "
                          f"{TARGETS[i][0]} vs ({t1.name}, {t2.name})")
                    found += 1
        if found == 0:
            print("  no pair is sample-consistent for M1/M2/FULL")

    print(f"\ntotal time {time.time()-t0:.1f}s")

if __name__ == "__main__":
    main()
