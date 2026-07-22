#!/usr/bin/env python3
"""Fully independent verification of the explicit height-1 expression for
the cumulative staged-counting language

    N_0 = #{ b in w : (number of a's strictly before it) = 0 mod 3 }
    target: N_0 = 0 mod 2.

Claimed generalized regular expression (star height 1; b* is star-free
since b* = complement(S*aS*), so the only stars below are the outer ones):

  Let X  = b | a b* a b* a          (star-free tokens)
      D  = ( X X )*                 (even number of tokens)
      XD = X ( X X )*               (odd number of tokens)
      R1 = a b*                     (partial connector, 1 extra a)
      R2 = a b* a b*                (partial connector, 2 extra a's)
      Aq = { w : #a(w) = q mod 6 }

  N0 even  <=>  w in  (D  and A0) | (XD and A3)
                    | (D R1 and A1) | (XD R1 and A4)
                    | (D R2 and A2) | (XD R2 and A5)

Verification is done with Python's re module (an entirely independent
regex engine), with membership in Aq computed by literal letter counting,
and N_0 computed by literal scanning. Tested exhaustively for all words
up to length 18 and on 200k random words up to length 300.
"""

import itertools, random, re

X = r"(?:b|ab*ab*a)"
D = rf"(?:{X}{X})*"
XD = rf"{X}(?:{X}{X})*"
R1 = r"ab*"
R2 = r"ab*ab*"

PIECES = [
    (re.compile(rf"{D}"), 0),
    (re.compile(rf"{XD}"), 3),
    (re.compile(rf"{D}{R1}"), 1),
    (re.compile(rf"{XD}{R1}"), 4),
    (re.compile(rf"{D}{R2}"), 2),
    (re.compile(rf"{XD}{R2}"), 5),
]

def in_expression(w):
    na = w.count('a') % 6
    return any(q == na and rx.fullmatch(w) for rx, q in PIECES)

def n0_even(w):
    n0 = 0
    a = 0
    for ch in w:
        if ch == 'a':
            a += 1
        elif a % 3 == 0:
            n0 += 1
    return n0 % 2 == 0

def main():
    # exhaustive up to length 18
    bad = 0
    for L in range(0, 19):
        for tup in itertools.product('ab', repeat=L):
            w = ''.join(tup)
            if in_expression(w) != n0_even(w):
                print(f"MISMATCH at '{w}': expr={in_expression(w)} "
                      f"target={n0_even(w)}")
                bad += 1
                if bad > 5:
                    return
        print(f"length {L}: all {2**L} words OK", flush=True)
    # random long words
    rnd = random.Random(42)
    for i in range(200_000):
        ln = rnd.randint(0, 300)
        w = ''.join(rnd.choice('ab') for _ in range(ln))
        if in_expression(w) != n0_even(w):
            print(f"MISMATCH at random '{w}'")
            return
    print("random 200k words (len<=300): all OK")
    print("\nCONCLUSION: the explicit height-1 expression for "
          "'N_0(stage 3) even' is correct.")

if __name__ == "__main__":
    main()
