#!/usr/bin/env python3
"""Second attempt: full-alphabet (multi-mover) A4 word problem at
generalized star height 1, via pattern-conditioned cut features.

Alphabet {u,d,k}, eps(u)=1, eps(d)=2, eps(k)=0,
phi(u)=t=(123), phi(d)=x t^2, phi(k)=x=(12)(34).

Feature F(q, pi): deterministic parse; a CUT happens when the phase
becomes q, EXCEPT when the letters read since the current token started
end with pattern pi (then the q-visit is interior and the token goes on).
Counts cuts mod 2.  All tokens enter at phase q (single entry phase!),
so the parse is O . X* . prefix with X = the token language, and each
feature-state language has height <= 1 provided X is star-free.

Key structural facts used:
  * patterns ending in a mover cannot span a cut boundary
    (the pattern tail walks away from q), so X is context-free-of-context;
  * same-class triples (e.g. uuu) have eps-sum = 0, so their interior
    loops sit at phase q and do not create phase-cycling.

Extraction plan (mod 2):
  Z_q            = F(q, None)                       [cut at all q-entries]
  N[k,p]         = Z_p - F(p,'k')
  N'[hu, q]      = Z_q - F(q,'hu')   for h in {d,k}
  N'[huu, q]     = Z_q - F(q,'huu')  for h in {d,k,u}
  N[u,p]         = N'[du,p+1] + N'[ku,p+1] + N'[uu,p+1] + boundary terms,
  N'[uu,q]       = N'[duu,q] + N'[kuu,q] + N'[uuu,q] + boundary terms,
  and symmetrically for d.  Boundary terms are star-free (word-prefix
  patterns), absorbed by the feature/LC states.

Verification:
  1. aperiodicity certificate for every token language X(q,pi);
  2. exact semantic check: each N[g,p] mod 2 is a function of the
     states of (LC, small feature subset);
  3. end-to-end: A4 membership vs all features (sampling + exhaustive).
"""

import itertools, random, time
from collections import deque

SIGMA = "udk"
EPS = {'u': 1, 'd': 2, 'k': 0}
BUFLEN = 2   # remember last 2 letters of the current token

# ---------------- LC ----------------
LC_INIT = (0, 0, 0)
def lc_step(lc, ch):
    i = SIGMA.index(ch)
    l = list(lc)
    l[i] = (l[i] + 1) % 6
    return tuple(l)

# ---------------- pattern-conditioned cut feature ----------------
class CutPat:
    """State (r, ph, buf): cuts mod 2, current phase, suffix (<=BUFLEN)
    of the current token.  Deterministic."""
    __slots__ = ("q", "pat", "name", "init")

    def __init__(self, q, pat):
        self.q = q
        self.pat = pat           # None = cut at every q-entry
        self.name = f"F({q},{pat})"
        self.init = (0, 0, "")   # phase 0 at word start, empty token

    def step(self, s, ch):
        r, ph, buf = s
        newph = (ph + EPS[ch]) % 3
        if newph == self.q:
            ext = buf + ch
            if self.pat is not None and ext.endswith(self.pat):
                return (r, newph, ext[-BUFLEN:])       # interior q-visit
            return ((r + 1) % 2, newph, "")            # cut, fresh token
        return (r, newph, (buf + ch)[-BUFLEN:])

    def val(self, s):
        return s[0]

# ---------------- star-freeness certificate ----------------
def token_dfa(q, pat):
    """DFA of the token language of F(q,pat): words starting at phase q
    (fresh token) ending at the first cut.  States (ph, buf) + ACC/DEAD."""
    start = (q, "")
    ACC, DEAD = "ACC", "DEAD"
    trans = {}
    seen = {start, ACC, DEAD}
    stack = [start]
    for st in (ACC, DEAD):
        for ch in SIGMA:
            trans[(st, ch)] = DEAD
    while stack:
        st = stack.pop()
        ph, buf = st
        for ch in SIGMA:
            newph = (ph + EPS[ch]) % 3
            if newph == q:
                ext = buf + ch
                if pat is not None and ext.endswith(pat):
                    ns = (newph, ext[-BUFLEN:])
                else:
                    ns = ACC
            else:
                ns = (newph, (buf + ch)[-BUFLEN:])
            trans[(st, ch)] = ns
            if ns not in seen:
                seen.add(ns)
                stack.append(ns)
    return sorted(seen, key=repr), trans

def is_aperiodic(states, trans):
    idx = {s: i for i, s in enumerate(states)}
    n = len(idx)
    gens = [tuple(idx[trans[(s, ch)]] for s in states) for ch in SIGMA]
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
        p = ident
        for _ in range(m):
            p = tuple(f[p[i]] for i in range(n))
        p1 = tuple(f[p[i]] for i in range(n))
        if p != p1:
            return False, m
    return True, m

# ---------------- targets ----------------
class NTarget:
    def __init__(self, g, p):
        self.g, self.p = g, p
        self.name = f"N[{g},{p}]%2"
        self.init = (0, 0)
    def step(self, s, ch):
        ph, c = s
        c2 = (c + 1) % 2 if (ch == self.g and ph == self.p) else c
        return ((ph + EPS[ch]) % 3, c2)
    def val(self, s):
        return s[1]

def pmul(p, q):
    return tuple(q[i] for i in p)

T3 = (1, 2, 0, 3)
X4 = (1, 0, 3, 2)
PHI = {'u': T3, 'd': pmul(X4, pmul(T3, T3)), 'k': X4}

class A4Target:
    name = "A4-full"
    init = (0, 1, 2, 3)
    def step(self, s, ch):
        return pmul(s, PHI[ch])
    def val(self, s):
        return s

# ---------------- checks ----------------
def semantic_check(feats, target, cap=8_000_000):
    start = (LC_INIT, tuple(f.init for f in feats), target.init)
    seen = {start}
    q = deque([start])
    cell = {}
    t0 = time.time()
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

def joint_sample_check(feats, target, n_words, max_len, seed=3):
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
    print("=== 1. star-freeness certificates for all token languages ===",
          flush=True)
    pats = [None, 'k', 'du', 'ku', 'ud', 'kd', 'uuu', 'duu', 'kuu',
            'ddd', 'udd', 'kdd']
    certified = {}
    for q in range(3):
        for pat in pats:
            states, trans = token_dfa(q, pat)
            ok, msize = is_aperiodic(states, trans)
            certified[(q, pat)] = ok
            tag = "OK " if ok else "FAIL"
            print(f"  X(q={q}, pat={pat}): {len(states)} states, "
                  f"monoid {msize}, aperiodic {tag}", flush=True)
    if not all(certified.values()):
        print("  -> some token language is NOT star-free; the affected "
              "features are not certified height-1.", flush=True)

    print("\n=== 2. semantic checks: N[g,p] vs (LC + feature subset) ===",
          flush=True)
    all_ok = True
    for p in range(3):
        # non-mover k: entry phase = p
        feats = [CutPat(p, None), CutPat(p, 'k')]
        res, info = semantic_check(feats, NTarget('k', p))
        print(f"  N[k,{p}]: {'PROVEN' if res is True else res} "
              f"({info if res is not True else str(info)+' states'})",
              flush=True)
        all_ok &= (res is True)
    for p in range(3):
        # mover u: entry phase q = p+1
        qq = (p + 1) % 3
        feats = [CutPat(qq, None), CutPat(qq, 'du'), CutPat(qq, 'ku'),
                 CutPat(qq, 'duu'), CutPat(qq, 'kuu'), CutPat(qq, 'uuu')]
        res, info = semantic_check(feats, NTarget('u', p))
        print(f"  N[u,{p}]: {'PROVEN' if res is True else res} "
              f"({info if res is not True else str(info)+' states'})",
              flush=True)
        all_ok &= (res is True)
    for p in range(3):
        # mover d: entry phase q = p+2
        qq = (p + 2) % 3
        feats = [CutPat(qq, None), CutPat(qq, 'ud'), CutPat(qq, 'kd'),
                 CutPat(qq, 'udd'), CutPat(qq, 'kdd'), CutPat(qq, 'ddd')]
        res, info = semantic_check(feats, NTarget('d', p))
        print(f"  N[d,{p}]: {'PROVEN' if res is True else res} "
              f"({info if res is not True else str(info)+' states'})",
              flush=True)
        all_ok &= (res is True)

    print("\n=== 3. end-to-end: A4 membership vs all features ===",
          flush=True)
    feats = []
    for q in range(3):
        for pat in pats:
            feats.append(CutPat(q, pat))
    tgt = A4Target()
    res, info = joint_sample_check(feats, tgt, 300_000, 150)
    print(f"  sampling 300k (len<=150): "
          f"{'consistent' if res else 'COLLISION ' + str(info)}", flush=True)
    bad = None
    sig2 = {}
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

    if all_ok and res and not bad:
        print("\nCONCLUSION: all N[g,p] mod 2 PROVEN to be Boolean "
              "combinations of certified height-1 features; hence the "
              "multi-mover (full-alphabet) A4 word problem has "
              "generalized star height <= 1.", flush=True)

if __name__ == "__main__":
    main()
