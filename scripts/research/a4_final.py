#!/usr/bin/env python3
"""End-to-end independent verification that the A4 word problem is given by
an explicit generalized regular expression of star height 1.

  Alphabet {a,b}, phi(a) = (123), phi(b) = (12)(34).
  L = { w : phi(w) = id }.

Claimed representation. Let N_r(w) = #{ b in w : #a before it = r mod 3 }.
  (1)  w in L  <=>  #a = 0 (3),  N_0+N_2 = 0 (2),  N_1+N_2 = 0 (2).
  (2)  each parity N_r mod 2 is computed by the height-1 expression schema:
         opener  O_r = (b*a)^r          (star-free power)
         tokens  X   = b | a b* a b* a  (star-free)
         core    D = (XX)*  /  XD = X(XX)*   (the only stars: height 1)
         tails   rho_e in { eps, ab*, ab*ab* }
       For the unique e with #a = r + e (mod 3), exactly one of
         O_r D rho_e ,  O_r XD rho_e
       matches, telling #tokens mod 2; then
         N_r = #tokens - (#a - r - e)/3   (mod 2).
       (For #a < r: N_r = 0.)

Independence: expressions are evaluated by Python's `re` engine
(fullmatch); the ground truth is direct permutation composition; N_r is
also cross-checked by direct scanning.
"""

import itertools, random, re, sys

X = r"(?:b|ab*ab*a)"
D = rf"(?:{X}{X})*"
XD = rf"{X}(?:{X}{X})*"
RHO = ["", r"ab*", r"ab*ab*"]

def opener(r):
    return r"(?:b*a)" * r

PIECES = {}
for r in range(3):
    lst = []
    for tokpar, core in ((0, D), (1, XD)):
        for e, rho in enumerate(RHO):
            lst.append((re.compile(opener(r) + core + rho), tokpar, e))
    PIECES[r] = lst

def parity_Nr_expr(w, r):
    """N_r mod 2 via the height-1 expression schema."""
    na = w.count('a')
    if na < r:
        return 0
    hits = []
    for rx, tokpar, e in PIECES[r]:
        if (na - r - e) % 3 == 0 and na - r - e >= 0 and rx.fullmatch(w):
            s = (na - r - e) // 3
            hits.append((tokpar - s) % 2)
    if len(hits) != 1:
        raise RuntimeError(f"ambiguous/missing match: w={w!r} r={r} "
                           f"hits={hits}")
    return hits[0]

def parity_Nr_direct(w, r):
    n = a = 0
    for ch in w:
        if ch == 'a':
            a += 1
        elif a % 3 == r:
            n += 1
    return n % 2

def a4_member_expr(w):
    if w.count('a') % 3 != 0:
        return False
    p0 = parity_Nr_expr(w, 0)
    p1 = parity_Nr_expr(w, 1)
    p2 = parity_Nr_expr(w, 2)
    return (p0 + p2) % 2 == 0 and (p1 + p2) % 2 == 0

PA = (1, 2, 0, 3)   # (123)
PB = (1, 0, 3, 2)   # (12)(34)

def a4_member_direct(w):
    g = (0, 1, 2, 3)
    for ch in w:
        p = PA if ch == 'a' else PB
        g = tuple(p[i] for i in g)
    return g == (0, 1, 2, 3)

def main():
    # exhaustive
    for L in range(0, 17):
        cnt_in = 0
        for tup in itertools.product('ab', repeat=L):
            w = ''.join(tup)
            for r in range(3):
                pe = parity_Nr_expr(w, r)
                pd = parity_Nr_direct(w, r)
                if pe != pd:
                    print(f"N_{r} MISMATCH at '{w}': expr={pe} direct={pd}")
                    return
            me, md = a4_member_expr(w), a4_member_direct(w)
            if me != md:
                print(f"A4 MISMATCH at '{w}': expr={me} direct={md}")
                return
            cnt_in += md
        print(f"len {L}: all {2**L} words OK ({cnt_in} in L_A4)", flush=True)
    # random long words
    rnd = random.Random(123)
    for i in range(30_000):
        ln = rnd.randint(0, 120)
        w = ''.join(rnd.choice('ab') for _ in range(ln))
        for r in range(3):
            if parity_Nr_expr(w, r) != parity_Nr_direct(w, r):
                print(f"N_{r} MISMATCH at random '{w}'")
                return
        if a4_member_expr(w) != a4_member_direct(w):
            print(f"A4 MISMATCH at random '{w}'")
            return
    print("random 30k words (len<=120): all OK", flush=True)
    print("\nCONCLUSION: the explicit star-height-1 expression schema "
          "decides the A4 word problem correctly.")

if __name__ == "__main__":
    main()
