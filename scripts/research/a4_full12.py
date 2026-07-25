#!/usr/bin/env python3
"""THE full-alphabet case: Sigma = all 12 elements of A4.

Every element is v t^e with v in V4, e in {0,1,2} (t = (012), fixing 3).
eps(g) = e is the Z/3 phase move of g; V4 letters are non-movers,
the 8 three-cycles are movers (4 with eps=1, 4 with eps=2).

Height-1 extractable data (all cut features have every token entering
at phase q, hence O . X* . prefix with X star-free -- certified below):

  fwd:  Z_q                       (cut at every q-entry)
        N[h,q]   per non-mover h  (via F(q,'h'))
        N'[hg,q] per mover g, any h != g   (via F(q,'hg'))
  bwd:  the same features on reversed(w)   (height 1 closed under
        reversal), plus letter counts and total phase P.

Per-mover-g linear system over F2, unknowns x_p = N[g,p] mod 2 and
n_q = N'[gg,q] mod 2:

  fwd:  x_p + n_{p+e}  = A_p + s.[p=0]          (A_p = sum_{h!=g} N'[hg,p+e])
  bwd:  x_m + n_{m+2e} = At_{r(m)} + st.[r(m)=0],  r(m) = P - e - m
  sum:  x_0+x_1+x_2 = |w|_g mod 2

e != 0 and e != 2e mod 3  =>  the system has full rank (verified).

Checks:
  1. aperiodicity certificates for all token languages (q=0 suffices,
     other q are isomorphic via phase shift);
  2. feature-vs-event identities (no-boundary-span property) on samples;
  3. per-word reconstruction of every N[g,p] mod 2 from extractable
     data only, exhaustive short + random long words;
  4. group element = t^P . (V4-part), V4-part linear in N[g,p] mod 2.
"""

import itertools, random, time
from collections import deque

# ---------- A4 ----------
def pmul(p, q):  # apply p then q
    return tuple(q[i] for i in p)

IDENT = (0, 1, 2, 3)
T = (1, 2, 0, 3)
T2 = pmul(T, T)
V4 = [IDENT, (1, 0, 3, 2), (2, 3, 0, 1), (3, 2, 1, 0)]

ELEMS = []
EPS = {}
VPART = {}
for v in V4:
    for e, te in ((0, IDENT), (1, T), (2, T2)):
        g = pmul(v, te)          # g = v . t^e
        ELEMS.append(g)
        EPS[g] = e
        VPART[g] = v
SIGMA = ELEMS                    # 12 letters
NONMOVERS = [g for g in SIGMA if EPS[g] == 0]
MOVERS = [g for g in SIGMA if EPS[g] != 0]
VIDX = {v: i for i, v in enumerate(V4)}

# conjugation tau(v) = t v t^{-1} in the same "then"-product convention
def tau(v):
    return pmul(pmul(T, v), T2)

def tau_pow(v, k):
    for _ in range(k % 3):
        v = tau(v)
    return v

# sanity: phi(w) = (sum_j tau^{p_j}(v_j)) . t^P  -- checked in test 4.

# ---------- direct quantities ----------
def direct_all(w):
    """N[g,p] mod 2, N'[hg,q] mod 2 (h,g any), total phase P, product."""
    N = {}
    NP = {}
    ph = 0
    prev = None
    prod = IDENT
    for g in w:
        N[(g, ph)] = N.get((g, ph), 0) ^ 1
        newph = (ph + EPS[g]) % 3
        if prev is not None:
            NP[(prev, g, newph)] = NP.get((prev, g, newph), 0) ^ 1
        prod = pmul(prod, g)
        prev = g
        ph = newph
    return N, NP, ph, prod

# ---------- cut features (for certification / identity tests) ----------
class CutPat:
    """pat: None | ('1',h) | ('2',h,g); token-local suffix matching."""
    def __init__(self, q, pat):
        self.q, self.pat = q, pat
    def match(self, buf, ch):
        p = self.pat
        if p is None:
            return False
        if p[0] == '1':
            return ch == p[1]
        return ch == p[2] and buf is not None and buf == p[1]
    def run(self, w):
        r, ph, buf = 0, 0, None
        for ch in w:
            newph = (ph + EPS[ch]) % 3
            if newph == self.q:
                if self.match(buf, ch):
                    ph, buf = newph, ch
                else:
                    r, ph, buf = r ^ 1, newph, None
            else:
                ph, buf = newph, ch
        return r

def token_dfa(pat):
    """token language DFA for q=0 (others isomorphic)."""
    q = 0
    ACC, DEAD = "A", "D"
    start = (q, None)
    trans, seen, stack = {}, {start, ACC, DEAD}, [start]
    f = CutPat(q, pat)
    for st in (ACC, DEAD):
        for ch in SIGMA:
            trans[(st, ch)] = DEAD
    while stack:
        st = stack.pop()
        ph, buf = st
        for ch in SIGMA:
            newph = (ph + EPS[ch]) % 3
            if newph == q:
                ns = (newph, ch) if f.match(buf, ch) else ACC
            else:
                ns = (newph, ch)
            trans[(st, ch)] = ns
            if ns not in seen:
                seen.add(ns)
                stack.append(ns)
    return sorted(seen, key=repr), trans

def is_aperiodic(states, trans):
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)
    gens = {tuple(idx[trans[(s, ch)]] for s in states) for ch in SIGMA}
    monoid = set(gens)
    frontier = list(gens)
    while frontier:
        f = frontier.pop()
        for g in gens:
            h = tuple(g[f[i]] for i in range(n))
            if h not in monoid:
                monoid.add(h)
                frontier.append(h)
        if len(monoid) > 500_000:
            return None, len(monoid)
    for f in monoid:
        # orbit of powers of f must reach a fixed point (period 1)
        seen_p = {}
        g = f
        k = 0
        while g not in seen_p:
            seen_p[g] = k
            g = tuple(f[g[i]] for i in range(n))
            k += 1
        if k - seen_p[g] != 1:
            return False, len(monoid)
    return True, len(monoid)

# ---------- reconstruction from extractable data only ----------
def solve_f2(rows):
    """rows: list of (coeff-list length 6, rhs). Return unique solution
    or None."""
    m = [list(r[0]) + [r[1]] for r in rows]
    rank = 0
    n = 6
    for col in range(n):
        piv = None
        for i in range(rank, len(m)):
            if m[i][col]:
                piv = i
                break
        if piv is None:
            return None
        m[rank], m[piv] = m[piv], m[rank]
        for i in range(len(m)):
            if i != rank and m[i][col]:
                m[i] = [(a ^ b) for a, b in zip(m[i], m[rank])]
        rank += 1
    for i in range(rank, len(m)):
        if m[i][n]:
            return "inconsistent"
    return [m[i][n] for i in range(n)]

def reconstruct(w):
    """Recover all N[g,p] mod 2 using ONLY height-1 extractable data."""
    Nw, NPw, P, _ = direct_all(w)
    wr = w[::-1]
    Nr, NPr, Pr, _ = direct_all(wr)
    assert Pr == P
    lc = {g: sum(1 for c in w if c == g) % 2 for g in SIGMA}
    out = {}
    # non-movers: directly extractable
    for h in NONMOVERS:
        for p in range(3):
            out[(h, p)] = Nw.get((h, p), 0)
    # movers: linear system per letter
    for g in MOVERS:
        e = EPS[g]
        s = 1 if (w and w[0] == g) else 0
        st = 1 if (w and w[-1] == g) else 0
        rows = []
        for p in range(3):
            A = 0
            for h in SIGMA:
                if h != g:
                    A ^= NPw.get((h, g, (p + e) % 3), 0)
            rhs = A ^ (s if p == 0 else 0)
            co = [0] * 6
            co[p] = 1                    # x_p
            co[3 + (p + e) % 3] = 1      # n_{p+e}
            rows.append((co, rhs))
        for m_ in range(3):
            r = (P - e - m_) % 3
            At = 0
            for h in SIGMA:
                if h != g:
                    At ^= NPr.get((h, g, (r + e) % 3), 0)
            rhs = At ^ (st if r == 0 else 0)
            co = [0] * 6
            co[m_] = 1                   # x_m
            co[3 + (m_ + 2 * e) % 3] = 1 # n_{m+2e}
            rows.append((co, rhs))
        rows.append(([1, 1, 1, 0, 0, 0], lc[g]))
        sol = solve_f2(rows)
        if sol is None or sol == "inconsistent":
            return None, sol
        for p in range(3):
            out[(g, p)] = sol[p]
    return out, P

def group_from_counts(counts, P):
    v = IDENT
    for (g, p), bit in counts.items():
        if bit:
            v = pmul(v, tau_pow(VPART[g], p))
    return pmul(v, (IDENT, T, T2)[P])

def main():
    rnd = random.Random(11)

    print("=== 1. aperiodicity certificates (q=0; other q isomorphic) ===",
          flush=True)
    pats = [None] + [('1', h) for h in NONMOVERS]
    for g in MOVERS:
        for h in SIGMA:
            if h != g:
                pats.append(('2', h, g))
    fails = []
    t0 = time.time()
    for i, pat in enumerate(pats):
        states, trans = token_dfa(pat)
        ok, msize = is_aperiodic(states, trans)
        if ok is not True:
            fails.append((pat, ok, msize))
    print(f"  checked {len(pats)} token languages in "
          f"{time.time()-t0:.1f}s; failures: {len(fails)}", flush=True)
    for pat, ok, msize in fails[:10]:
        print(f"    FAIL {pat}: aperiodic={ok}, monoid={msize}", flush=True)

    print("\n=== 2. feature-vs-event identities (no-span property) ===",
          flush=True)
    bad = 0
    for trial in range(400):
        ln = rnd.randint(0, 60)
        w = [rnd.choice(SIGMA) for _ in range(ln)]
        Nw, NPw, P, _ = direct_all(w)
        for _ in range(6):
            q = rnd.randrange(3)
            pat = rnd.choice(pats)
            f = CutPat(q, pat).run(w)
            Zq = sum(Nw.get((g, (q - EPS[g]) % 3), 0) for g in SIGMA) % 2
            if pat is None:
                expect = Zq
            elif pat[0] == '1':
                expect = Zq ^ Nw.get((pat[1], q), 0)
            else:
                expect = Zq ^ NPw.get((pat[1], pat[2], q), 0)
            if f != expect:
                bad += 1
    print(f"  2400 random feature/word checks, mismatches: {bad}",
          flush=True)

    print("\n=== 3. reconstruction of N[g,p] from extractable data ===",
          flush=True)
    ok = True
    cnt = 0
    for L in range(0, 5):
        for tup in itertools.product(SIGMA, repeat=L):
            w = list(tup)
            rec, P = reconstruct(w)
            Nw, _, P2, _ = direct_all(w)
            truth = {(g, p): Nw.get((g, p), 0) for g in SIGMA
                     for p in range(3)}
            if rec != truth:
                print(f"  MISMATCH len {L}: {w}", flush=True)
                ok = False
                break
            cnt += 1
        if not ok:
            break
    print(f"  exhaustive length <= 4: {cnt} words "
          f"{'OK' if ok else 'FAILED'}", flush=True)
    if ok:
        for _ in range(4000):
            ln = rnd.randint(5, 300)
            w = [rnd.choice(SIGMA) for _ in range(ln)]
            rec, P = reconstruct(w)
            Nw, _, _, _ = direct_all(w)
            truth = {(g, p): Nw.get((g, p), 0) for g in SIGMA
                     for p in range(3)}
            if rec != truth:
                print(f"  MISMATCH random len {ln}", flush=True)
                ok = False
                break
        print(f"  random 4000 words (length <= 300): "
              f"{'OK' if ok else 'FAILED'}", flush=True)

    print("\n=== 4. group element from (P, N[g,p] mod 2) ===", flush=True)
    ok4 = True
    for _ in range(20000):
        ln = rnd.randint(0, 200)
        w = [rnd.choice(SIGMA) for _ in range(ln)]
        Nw, _, P, prod = direct_all(w)
        counts = {(g, p): Nw.get((g, p), 0) for g in SIGMA
                  for p in range(3)}
        if group_from_counts(counts, P) != prod:
            print("  FORMULA MISMATCH", flush=True)
            ok4 = False
            break
    print(f"  20000 random words: {'OK' if ok4 else 'FAILED'}", flush=True)

    if not fails and bad == 0 and ok and ok4:
        print("\nCONCLUSION: the word problem of A4 with ALL 12 group "
              "elements as alphabet has generalized star height <= 1.",
              flush=True)

if __name__ == "__main__":
    main()
