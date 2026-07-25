#!/usr/bin/env python3
"""Full-alphabet (multi-mover) A4 word problem, height-1 construction,
third attempt: certified cut features + REVERSAL closure.

Alphabet {u,d,k}, eps(u)=1, eps(d)=2, eps(k)=0;
phi(u)=t=(123), phi(d)=x t^2, phi(k)=x=(12)(34);  A4 = <t, x>.

Certified height-1 extractable quantities (mod 2), from a4_full2.py
aperiodicity certificates (patterns None and 'k' only -- both OK):

  forward, for q in Z/3:
    Z_q       = F(q,None).cuts   (# entries into phase q)
    Zk_q      = F(q,'k').cuts    (# entries into q not via letter k)
    z_q       = N[k,q] = Z_q + Zk_q                    (proven exactly)
    S_q       = Z_q + z_q  = N[u,q-1] + N[d,q-2]       (mover entries)

  backward (same features run on the reversed word; height 1 is closed
  under reversal, so these are still height-1 expressible), for qt:
    Zt_qt, zt_qt analogously;  algebra:  reversed entry phase of a
    letter g equals P - eps_g - (its forward entry phase), P = total
    phase.  Hence
    St_qt = Zt_qt + zt_qt = N[u,P-qt] + N[d,P-qt] = C_{P-qt},
    where C_s := N[u,s] + N[d,s]  (same-phase mover sum!).

  linear system over F2 (x_p = N[u,p], y_p = N[d,p]):
    S_0 = x_2 + y_1,  S_1 = x_0 + y_2,  S_2 = x_1 + y_0,
    C_s = x_s + y_s,  sum_p x_p = |w|_u  =>
    x_0 = |u| + S_0 + C_1,  x_1 = |u| + S_1 + C_2,  x_2 = |u| + S_2 + C_0,
    y_p = C_p + x_p,        z_p as above.

Checks in this file:
  1. identity check (exhaustive to length 12 + random long words):
     formulas above reproduce every N[g,p] mod 2 exactly;
  2. exact automaton proof: A4 membership is a function of
     (P, all N[g,p] mod 2) -- small product BFS;
  3. hence A4-full is a Boolean combination of height-1 languages.
"""

import itertools, random
from collections import deque

SIGMA = "udk"
EPS = {'u': 1, 'd': 2, 'k': 0}
BUFLEN = 2

class CutPat:
    __slots__ = ("q", "pat")
    def __init__(self, q, pat):
        self.q, self.pat = q, pat
    def run(self, w):
        r, ph, buf = 0, 0, ""
        for ch in w:
            newph = (ph + EPS[ch]) % 3
            if newph == self.q:
                ext = buf + ch
                if self.pat is not None and ext.endswith(self.pat):
                    ph, buf = newph, ext[-BUFLEN:]
                else:
                    r, ph, buf = (r + 1) % 2, newph, ""
            else:
                ph, buf = newph, (buf + ch)[-BUFLEN:]
        return r

FWD = {(q, pat): CutPat(q, pat) for q in range(3) for pat in (None, 'k')}

def direct_counts(w):
    """N[g,p] mod 2 for all g,p and total phase P."""
    n = {(g, p): 0 for g in SIGMA for p in range(3)}
    ph = 0
    for ch in w:
        n[(ch, ph)] ^= 1
        ph = (ph + EPS[ch]) % 3
    return n, ph

def formula_counts(w):
    """Recover all N[g,p] mod 2 from certified height-1 data only:
    forward features on w, the same features on reversed(w), letter
    counts mod 2, total phase P (a function of letter counts)."""
    lu = w.count('u') % 2
    ld = w.count('d') % 2
    P = (w.count('u') + 2 * w.count('d')) % 3
    wr = w[::-1]
    Z = {q: FWD[(q, None)].run(w) for q in range(3)}
    Zk = {q: FWD[(q, 'k')].run(w) for q in range(3)}
    Zt = {q: FWD[(q, None)].run(wr) for q in range(3)}
    Zkt = {q: FWD[(q, 'k')].run(wr) for q in range(3)}
    z = {q: (Z[q] + Zk[q]) % 2 for q in range(3)}           # N[k,q]
    S = {q: (Z[q] + z[q]) % 2 for q in range(3)}            # mover entries
    zt = {q: (Zt[q] + Zkt[q]) % 2 for q in range(3)}
    St = {q: (Zt[q] + zt[q]) % 2 for q in range(3)}
    C = {s: St[(P - s) % 3] for s in range(3)}              # N[u,s]+N[d,s]
    x = {0: (lu + S[0] + C[1]) % 2,
         1: (lu + S[1] + C[2]) % 2,
         2: (lu + S[2] + C[0]) % 2}
    y = {p: (C[p] + x[p]) % 2 for p in range(3)}
    # sanity: y should also satisfy sum = |d| mod 2
    assert (y[0] + y[1] + y[2]) % 2 == ld
    out = {}
    for p in range(3):
        out[('u', p)] = x[p]
        out[('d', p)] = y[p]
        out[('k', p)] = z[p]
    return out, P

def identity_check():
    print("=== 1. identity check: formulas vs direct counts ===", flush=True)
    # exhaustive
    for L in range(0, 13):
        for tup in itertools.product(SIGMA, repeat=L):
            w = ''.join(tup)
            f, Pf = formula_counts(w)
            d, Pd = direct_counts(w)
            if f != d or Pf != Pd:
                print(f"  MISMATCH at w={w!r}: {f} vs {d}", flush=True)
                return False
        if L in (8, 10, 12):
            print(f"  exhaustive length <= {L}: OK", flush=True)
    # random long
    rnd = random.Random(7)
    for _ in range(20000):
        ln = rnd.randint(13, 400)
        w = ''.join(rnd.choice(SIGMA) for _ in range(ln))
        f, _ = formula_counts(w)
        d, _ = direct_counts(w)
        if f != d:
            print(f"  MISMATCH at random w={w!r}", flush=True)
            return False
    print("  random 20000 words (length <= 400): OK", flush=True)
    return True

def pmul(p, q):
    return tuple(q[i] for i in p)

T3 = (1, 2, 0, 3)
X4 = (1, 0, 3, 2)
PHI = {'u': T3, 'd': pmul(X4, pmul(T3, T3)), 'k': X4}

def a4_functionality_check():
    """Exact BFS: the reached A4 element is a function of
    (total phase P, all N[g,p] mod 2)."""
    print("\n=== 2. exact proof: A4 element = f(P, N[g,p] mod 2) ===",
          flush=True)
    ident = (0, 1, 2, 3)
    start = (ident, 0, (0,) * 9)   # perm, phase, 9 parity bits
    seen = {start}
    q = deque([start])
    cell = {}
    ok = True
    while q:
        perm, ph, bits = q.popleft()
        key = (ph, bits)
        if key in cell and cell[key] != perm:
            print(f"  COLLISION at {key}: {cell[key]} vs {perm}", flush=True)
            ok = False
            break
        cell[key] = perm
        for ch in SIGMA:
            gi = SIGMA.index(ch)
            nb = list(bits)
            nb[gi * 3 + ph] ^= 1
            nx = (pmul(perm, PHI[ch]), (ph + EPS[ch]) % 3, tuple(nb))
            if nx not in seen:
                seen.add(nx)
                q.append(nx)
    if ok:
        print(f"  PROVEN over {len(seen)} product states "
              f"({len(cell)} feature cells).", flush=True)
    return ok

def main():
    ok1 = identity_check()
    ok2 = a4_functionality_check()
    if ok1 and ok2:
        print("\nCONCLUSION:", flush=True)
        print("  * every N[g,p] mod 2 is a Boolean combination of", flush=True)
        print("    certified height-1 features of w and of reversed(w),",
              flush=True)
        print("    plus letter counts mod 2/3 (height 1, commutative);",
              flush=True)
        print("  * A4 membership (any target element) is a function of",
              flush=True)
        print("    (P, N[g,p] mod 2) -- proven exactly;", flush=True)
        print("  => the FULL-ALPHABET (multi-mover) A4 word problem has",
              flush=True)
        print("     generalized star height <= 1.", flush=True)

if __name__ == "__main__":
    main()
