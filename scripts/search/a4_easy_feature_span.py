#!/usr/bin/env python3
"""Decisive experiment for the Lean formalization route of N-A4-FULL-033.

Question: can every mover pair-parity N[g,p] mod 2 be recovered from
"EASY" height-1 features only, i.e. features whose token/core languages
have trivially star-free cores (no 5-state aperiodic C* needed)?

Easy feature basis (forward and on the reversed word):
  - total phase P mod 3 (case condition)
  - first letter / last letter of w (case condition)
  - letter counts |w|_g mod 2               (CountHeight, done in Lean)
  - Z_q = landing parity at q, q=0,1,2      (plain cut; C* trivial)
  - N[h,q] mod 2 for NONMOVERS h            (pattern ('1',h); C* = h*)
  - N'[hg,q] mod 2 for movers g and h of the OPPOSITE mover type
                                            (pattern ('2',h,g); C* = (hg)*)
  - #hg mod 2, phase-blind adjacent digram counts, all ordered pairs
                                            (run/token cutting; star-free cores)

The HARD features of a4_full12.py (same-type-mover and filler digram
patterns, 5-state aperiodic C*) are deliberately EXCLUDED.

Method: exact functionality test by collision search, exhaustive over a
6-letter subalphabet (words up to length L) plus random full-alphabet
words.  If two words agree on all easy features (incl. case conditions)
but differ on some N[g,p] mod 2, the easy basis is insufficient and the
hard C* cores must be formalized; otherwise we proceed to solve for an
affine GF(2) representation.
"""
import itertools, random, sys

def pmul(p, q):
    return tuple(q[i] for i in p)

IDENT = (0, 1, 2, 3)
T = (1, 2, 0, 3)
T2 = pmul(T, T)
V4 = [IDENT, (1, 0, 3, 2), (2, 3, 0, 1), (3, 2, 1, 0)]
ELEMS = []
EPS = {}
for v in V4:
    for e, te in ((0, IDENT), (1, T), (2, T2)):
        g = pmul(v, te)
        ELEMS.append(g)
        EPS[g] = e
SIGMA = ELEMS
NONMOVERS = [g for g in SIGMA if EPS[g] == 0]
MOVERS = [g for g in SIGMA if EPS[g] != 0]

def n_counts(w):
    """N[g,p] mod 2 for all g, digram N'[hg,q] mod 2, P."""
    N = {}
    NP = {}
    ph = 0
    prev = None
    for g in w:
        N[(g, ph)] = N.get((g, ph), 0) ^ 1
        nph = (ph + EPS[g]) % 3
        if prev is not None:
            NP[(prev, g, nph)] = NP.get((prev, g, nph), 0) ^ 1
        prev = g
        ph = nph
    return N, NP, ph

def easy_features(w):
    N, NP, P = n_counts(w)
    f = []
    # case conditions
    f.append(('P', P))
    f.append(('first', w[0] if w else None))
    f.append(('last', w[-1] if w else None))
    # letter counts mod 2
    for g in SIGMA:
        f.append(('lc', g, sum(1 for c in w if c == g) % 2))
    # Z_q
    for q in range(3):
        z = 0
        for g in SIGMA:
            z ^= N.get((g, (q - EPS[g]) % 3), 0)
        f.append(('Z', q, z))
    # nonmover unigrams
    for h in NONMOVERS:
        for q in range(3):
            f.append(('U', h, q, N.get((h, q), 0)))
    # opposite-type digrams
    for g in MOVERS:
        for h in MOVERS:
            if EPS[h] == 3 - EPS[g]:
                for q in range(3):
                    f.append(('D', h, g, q, NP.get((h, g, q), 0)))
    # optional hard classes (enabled via WITH_SAME / WITH_FILL)
    if WITH_SAME:
        for g in MOVERS:
            for h in MOVERS:
                if EPS[h] == EPS[g] and h != g:
                    for q in range(3):
                        f.append(('S', h, g, q, NP.get((h, g, q), 0)))
    if WITH_FILL:
        for g in MOVERS:
            for h in NONMOVERS:
                for q in range(3):
                    f.append(('F', h, g, q, NP.get((h, g, q), 0)))
    # phase-blind digram counts (all ordered pairs)
    pb = {}
    for i in range(1, len(w)):
        pb[(w[i-1], w[i])] = pb.get((w[i-1], w[i]), 0) ^ 1
    for h in SIGMA:
        for g in SIGMA:
            f.append(('B', h, g, pb.get((h, g), 0)))
    return tuple(f)

def all_features(w):
    return easy_features(w) + tuple(
        ('rev',) + x for x in easy_features(w[::-1]))

def target(w):
    N, _, _ = n_counts(w)
    return tuple(N.get((g, p), 0) for g in MOVERS for p in range(3))

WITH_SAME = '--same' in sys.argv
WITH_FILL = '--fill' in sys.argv

def main():
    print(f"WITH_SAME={WITH_SAME} WITH_FILL={WITH_FILL}")
    buckets = {}
    tested = 0

    def check(w):
        nonlocal tested
        tested += 1
        fv = all_features(w)
        tv = target(w)
        if fv in buckets:
            w0, tv0 = buckets[fv]
            if tv0 != tv:
                print("COLLISION (easy basis insufficient):")
                print("  w1 =", w0)
                print("  w2 =", w)
                idx = [(MOVERS[i // 3], i % 3)
                       for i in range(len(tv)) if tv[i] != tv0[i]]
                print("  differing N[g,p]:", idx)
                return False
        else:
            buckets[fv] = (w, tv)
        return True

    # exhaustive over a 6-letter subalphabet
    g0 = MOVERS[0]                      # some eps=1 mover
    u0 = next(h for h in MOVERS if EPS[h] == 1 and h != g0)
    d0 = next(h for h in MOVERS if EPS[h] == 2)
    d1 = next(h for h in MOVERS if EPS[h] == 2 and h != d0)
    f0, f1 = NONMOVERS[0], NONMOVERS[1]
    SUB = [g0, u0, d0, d1, f0, f1]
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    maxlen = int(args[0]) if args else 8
    for L in range(0, maxlen + 1):
        for tup in itertools.product(SUB, repeat=L):
            if not check(list(tup)):
                print(f"found at exhaustive length {L}")
                return 1
        print(f"exhaustive length {L} done ({tested} words, "
              f"{len(buckets)} buckets)")
    # random full-alphabet
    rnd = random.Random(7)
    for _ in range(200000):
        ln = rnd.randint(0, 40)
        w = [rnd.choice(SIGMA) for _ in range(ln)]
        if not check(w):
            print("found in random phase")
            return 1
    print(f"NO COLLISION in {tested} words: easy basis may suffice "
          f"(functionality supported; next step: affine solve)")
    return 0

if __name__ == "__main__":
    sys.exit(main())
