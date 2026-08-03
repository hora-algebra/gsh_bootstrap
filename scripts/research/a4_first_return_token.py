#!/usr/bin/env python3
"""Certificate: boundary-pair characterization of first-return words on C3.

Only the phase increment eps in {0,1,2} of each letter matters (0 = filler),
so we work over the abstract alphabet {0,1,2}; the 12-letter A4 alphabet
factors through it.

first_return(w): w nonempty, the running prefix sum mod 3 differs from 0 on
every proper nonempty prefix, and equals 0 at the end.

Claimed star-free characterization (boundary pairs), replacing the refuted
"five vertex-simple cycles" token:

  Let movers(w) be the subsequence of nonzero letters and let the "pairs"
  be consecutive movers (only 0s between them).  Then first_return(w) iff
    (a) w == [0]  (single filler lands on 0), or
    (b) w starts and ends with a mover, has exactly 2 movers, and their
        types differ, or
    (c) w starts and ends with a mover, has >= 3 movers, the first pair is
        same-type, the last pair is same-type, and no same-type pair occurs
        strictly inside (an occurrence is strictly inside iff it neither
        starts at the first letter nor ends at the last letter).

All of (a)-(c) are star-free: fillers are avoidSet-definable, "starts/ends
with", ">= 3 movers", and "no factor M_a fill* M_a strictly inside" use only
union, concatenation, and complement.
"""
import itertools
import random
import sys


def first_return(w):
    if not w:
        return False
    s = 0
    for i, e in enumerate(w):
        s = (s + e) % 3
        if s == 0:
            return i == len(w) - 1
    return False


def pair_char(w):
    if not w:
        return False
    if len(w) == 1:
        return w[0] == 0
    if w[0] == 0 or w[-1] == 0:
        return False
    mv = [(i, e) for i, e in enumerate(w) if e != 0]
    k = len(mv)
    if k < 2:
        return False
    pairs = list(zip(mv, mv[1:]))
    if k == 2:
        return mv[0][1] != mv[1][1]
    if pairs[0][0][1] != pairs[0][1][1]:
        return False
    if pairs[-1][0][1] != pairs[-1][1][1]:
        return False
    for (a, b) in pairs:
        if a[1] == b[1]:
            starts_at_first = a[0] == 0
            ends_at_last = b[0] == len(w) - 1
            if not (starts_at_first or ends_at_last):
                return False
    return True


def first_arrival_at_1(w):
    """w's landings on phase 1 (from start 0) happen exactly once, at the
    last letter (opener token for the q=1 cut)."""
    if not w:
        return False
    s = 0
    for i, e in enumerate(w):
        s = (s + e) % 3
        if s == 1:
            return i == len(w) - 1
    return False


def opener1_lean(w):
    """Current Lean opener1 = A1 | A2 fill* A2 (no leading fills, exactly
    the two shapes)."""
    if not w:
        return False
    if len(w) == 1:
        return w[0] == 1
    return (w[0] == 2 and w[-1] == 2 and
            all(e == 0 for e in w[1:-1]))


def opener_pair_char(w):
    """Boundary-pair characterization for the q=1 opener: leading fills
    allowed (fills at phase 0 do not land on 1); mover sequence walks
    {0,2} avoiding 1 until the last letter.

      (a) movers == [1]                       (direct entry), or
      (b) >= 2 movers, last letter is a mover, first pair DIFFERENT-type
          if >= 3 movers, last pair same-type, no same-type pair strictly
          inside-or-at-start except the last pair; first mover eps == 2;
          for exactly 2 movers: (2,2).
    """
    if not w:
        return False
    if w[-1] == 0:
        return False
    mv = [(i, e) for i, e in enumerate(w) if e != 0]
    k = len(mv)
    if k == 0:
        return False
    if k == 1:
        return mv[0][1] == 1
    if mv[0][1] != 2:
        return False
    pairs = list(zip(mv, mv[1:]))
    if k == 2:
        return mv[0][1] == 2 and mv[1][1] == 2
    if pairs[-1][0][1] != pairs[-1][1][1]:
        return False
    for j, (a, b) in enumerate(pairs):
        if a[1] == b[1] and j != len(pairs) - 1:
            return False
    return True


def main():
    for L in range(0, 14):
        for tup in itertools.product((0, 1, 2), repeat=L):
            if first_return(tup) != pair_char(tup):
                print(f"MISMATCH at {tup}: fr={first_return(tup)} "
                      f"char={pair_char(tup)}")
                return 1
        print(f"exhaustive length {L}: OK", flush=True)
    rnd = random.Random(11)
    for _ in range(200000):
        ln = rnd.randint(14, 400)
        w = tuple(rnd.choice((0, 1, 2)) for _ in range(ln))
        if first_return(w) != pair_char(w):
            print(f"MISMATCH at random {w}")
            return 1
    print("random 200000 words (length <= 400): OK")
    print("boundary-pair characterization certified")

    print()
    print("=== opener diagnosis (q=1) ===")
    missing = []
    for L in range(1, 10):
        for tup in itertools.product((0, 1, 2), repeat=L):
            fa = first_arrival_at_1(tup)
            if fa and not opener1_lean(tup) and len(missing) < 5:
                missing.append(tup)
            if opener1_lean(tup) and not fa:
                print(f"  UNSOUND opener1_lean at {tup}")
                return 1
    if missing:
        print(f"  Lean opener1 INCOMPLETE; first missing words: {missing}")
    else:
        print("  Lean opener1 complete (unexpected)")

    for L in range(0, 14):
        for tup in itertools.product((0, 1, 2), repeat=L):
            if first_arrival_at_1(tup) != opener_pair_char(tup):
                print(f"  OPENER MISMATCH at {tup}: "
                      f"fa={first_arrival_at_1(tup)} "
                      f"char={opener_pair_char(tup)}")
                return 1
    for _ in range(100000):
        ln = rnd.randint(14, 400)
        w = tuple(rnd.choice((0, 1, 2)) for _ in range(ln))
        if first_arrival_at_1(w) != opener_pair_char(w):
            print(f"  OPENER MISMATCH at random {w}")
            return 1
    print("  opener boundary-pair characterization certified "
          "(exhaustive <= 13 + random 100000)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
