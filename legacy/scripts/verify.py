#!/usr/bin/env python3
"""Deep verification of the promising feature pairs found by search.py.

For each candidate pair (T1, T2) of token-counting features:
  stage 1: random deep sampling (long words) for quick falsification
  stage 2: exhaustive sampling over all words of length <= L
  stage 3: exact semantic check via product-automaton reachability
           (if it passes, this is a machine-checked proof that the target
            is a Boolean combination of height-1 languages)
"""

import random, sys, time
from collections import deque
from search import Tok, TARGETS, NT, T_INIT, t_step, LC_INIT, lc_step, selftest

PAIRS = [
    (["b", "ab", "aBaBa", "aaBaBa"], ["b", "aBa", "aBaBa"]),
    (["b", "ab", "aBaBa", "aaBaBa"], ["b", "aBa", "aBaBaBa"]),
    (["b", "ab", "aBaBa", "aaBaBa"], ["b", "ab", "aBaBaBaBa", "aaBaBaBaBa"]),
]

def dfa_size(tok):
    seen = {tok.init}
    q = deque([tok.init])
    while q:
        s = q.popleft()
        for ch in ('a', 'b'):
            n = tok.step(s, ch)
            if n not in seen:
                seen.add(n)
                q.append(n)
    return len(seen)

def random_check(t1, t2, n_words, max_len, seed=7):
    rnd = random.Random(seed)
    sig2 = {}
    alive = [True] * NT
    coll = [None] * NT
    for _ in range(n_words):
        ln = rnd.randint(0, max_len)
        w = ''.join(rnd.choice('ab') for _ in range(ln))
        s1, s2, tg, lc = t1.init, t2.init, T_INIT, LC_INIT
        for ch in w:
            s1 = t1.step(s1, ch); s2 = t2.step(s2, ch)
            tg = t_step(tg, ch); lc = lc_step(lc, ch)
        sig = (lc, s1, s2)
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
    return alive, coll

def exhaustive_check(t1, t2, L):
    sig2 = {}
    alive = [True] * NT
    coll = [None] * NT
    frontier = [(LC_INIT, t1.init, t2.init, T_INIT)]
    words = [""]
    for depth in range(L + 1):
        nxt = []; nw = []
        for (lc, s1, s2, tg), w in zip(frontier, words):
            sig = (lc, s1, s2)
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
            if depth < L:
                nxt.append((lc_step(lc, 'a'), t1.step(s1, 'a'),
                            t2.step(s2, 'a'), t_step(tg, 'a')))
                nw.append(w + 'a')
                nxt.append((lc_step(lc, 'b'), t1.step(s1, 'b'),
                            t2.step(s2, 'b'), t_step(tg, 'b')))
                nw.append(w + 'b')
        frontier = nxt; words = nw
        if not any(alive[2:]):
            break
    return alive, coll

# encode target state (p,c1,c2,cT) -> 7 bits (ignore cT: 6 bits used)
def tgt_enc(tg):
    p, c1, c2, cT = tg
    return ((p * 4 + c1) * 2 + c2)

TGT_STATES = [(p, c1, c2, 0) for p in range(8) for c1 in range(4)
              for c2 in range(2)]

def semantic_pair_check(t1, t2, cap_states=40_000_000):
    """Exact product reachability. Returns per-target bool (only meaningful
    for targets independent of cT: PST, M1, M2, FULL)."""
    S1, S2 = dfa_size(t1), dfa_size(t2)
    NLC = 256
    NTG = 64
    total = NLC * S1 * S2 * NTG
    print(f"    S1={S1} S2={S2}, encoded space = {total:,}")
    if total > 2_600_000_000:
        print("    too large, skipping exact check")
        return None
    visited = bytearray((total + 7) // 8)
    # precompute target transitions on encoded 6-bit states
    tsteps = {}
    for tg in TGT_STATES:
        e = tgt_enc(tg)
        tsteps[(e, 'a')] = tgt_enc(t_step(tg, 'a'))
        tsteps[(e, 'b')] = tgt_enc(t_step(tg, 'b'))
    # readouts per encoded target state: (PST, M1, M2, FULL)
    def readouts(e):
        c2 = e & 1
        c1 = (e >> 1) & 3
        return (c1 % 2, c1, c2, (c1 + 2 * c2) % 4)
    start = ((LC_INIT * S1 + t1.init) * S2 + t2.init) * NTG + tgt_enc(T_INIT)
    visited[start >> 3] |= 1 << (start & 7)
    q = deque([start])
    cell = {}
    bad = [False] * 4
    n = 0
    t0 = time.time()
    while q:
        code = q.popleft()
        n += 1
        e = code % NTG
        rest = code // NTG
        s2 = rest % S2
        rest //= S2
        s1 = rest % S1
        lc = rest // S1
        key = rest * S2 + s2  # (lc, s1, s2) combined
        r = readouts(e)
        prev = cell.get(key)
        if prev is None:
            cell[key] = r
        else:
            for i in range(4):
                if prev[i] != r[i]:
                    bad[i] = True
        if not q and False:
            pass
        for ch in ('a', 'b'):
            nc = ((lc_step(lc, ch) * S1 + t1.step(s1, ch)) * S2
                  + t2.step(s2, ch)) * NTG + tsteps[(e, ch)]
            byte, bit = nc >> 3, 1 << (nc & 7)
            if not (visited[byte] & bit):
                visited[byte] |= bit
                q.append(nc)
        if n % 2_000_000 == 0:
            print(f"    ... {n:,} states, queue {len(q):,}, "
                  f"{time.time()-t0:.0f}s")
        if n > cap_states:
            print("    state cap exceeded")
            return None
    print(f"    reachable product states: {n:,} ({time.time()-t0:.1f}s)")
    names = ["PST(aab mod2)", "M1(mod4)", "M2(mod2)", "FULL(aab mod4)"]
    return {names[i]: (not bad[i]) for i in range(4)}

def main():
    selftest()
    for toks1, toks2 in PAIRS:
        t1, t2 = Tok(toks1, 4), Tok(toks2, 4)
        print(f"\n=== pair {t1.name}  +  {t2.name} ===")
        alive, coll = random_check(t1, t2, 300_000, 200)
        print("  random deep sampling (300k words, len<=200):")
        for i in range(1, NT):
            if alive[i]:
                print(f"    {TARGETS[i][0]}: consistent")
            else:
                pw, w = coll[i]
                print(f"    {TARGETS[i][0]}: COLLISION  '{pw}' vs '{w}'")
        if not any(alive[2:]):
            continue
        alive, coll = exhaustive_check(t1, t2, 16)
        print("  exhaustive sampling L<=16:")
        for i in range(1, NT):
            if alive[i]:
                print(f"    {TARGETS[i][0]}: consistent")
            else:
                pw, w = coll[i]
                print(f"    {TARGETS[i][0]}: COLLISION  '{pw}' vs '{w}'")
        if not any(alive[2:]):
            continue
        print("  exact semantic check:")
        res = semantic_pair_check(t1, t2)
        if res:
            for k, v in res.items():
                print(f"    {k}: {'PROVEN height <= 1 !!' if v else 'fails'}")

if __name__ == "__main__":
    main()
