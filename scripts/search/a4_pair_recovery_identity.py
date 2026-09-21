#!/usr/bin/env python3
"""Check the GF(2) recovery identity for single-pair counts N[g,p] of a MOVER g.

Context: obligation N-A4-FULL-033.  The feature family available from
height-one cut expressions is

  A_q(w) = # { i : w_i = g, phase(w[1..i]) = q, (i = 1 or w_{i-1} != g) }
  B_q(w) = A_q(reverse w)
  |w|_g  = number of occurrences of g

(each A_q is Z_q minus a pattern-conditioned cut count, hence a GF(2)
combination of parity features of height <= 1; see RESULTS.md 5.5).

Unknowns are x_p = N[g,p] (occurrences of g at *entry* phase p) and
n_q = # { i >= 2 : w_{i-1} = w_i = g, phase(w[1..i]) = q }.

Claimed solution, all mod 2, with P = phaseSum(w) mod 3 and eps = phase(g):

  nTot = |w|_g + A_0 + A_1 + A_2
  n_p  = A_{p+eps} + B_{P-p} + nTot
  x_p  = A_{p+eps} + n_{p+eps}
       = A_{p+eps} + A_{p+2eps} + B_{P-p-eps} + nTot

This script checks the identity exhaustively on short words and on random
long words, for both eps in {1,2}, over an alphabet with two movers of each
nonzero phase and two fillers (fully general: the quantities only depend on
each letter's phase and on whether it equals g).
"""
import itertools
import random
import sys


def build_alphabet(eps):
    other = 3 - eps
    # (name, phase); 'g' is the distinguished mover
    return [('g', eps), ('u', eps), ('d1', other), ('d2', other),
            ('f1', 0), ('f2', 0)]


def phases(word, alpha):
    ph = dict(alpha)
    return [ph[c] for c in word]


def features(word, alpha, eps):
    ph = dict(alpha)
    n = len(word)
    # entry phase of position i (0-based) = sum of phases before i
    entry = [0] * (n + 1)
    for i, c in enumerate(word):
        entry[i + 1] = (entry[i] + ph[c]) % 3
    P = entry[n]
    x = [0, 0, 0]
    nn = [0, 0, 0]
    A = [0, 0, 0]
    cnt_g = 0
    for i, c in enumerate(word):
        if c != 'g':
            continue
        cnt_g += 1
        x[entry[i]] += 1                      # entry phase
        land = entry[i + 1]                   # phase after reading w_i
        if i == 0 or word[i - 1] != 'g':
            A[land] += 1
        else:
            nn[land] += 1
    return P, x, nn, A, cnt_g


def check(word, alpha, eps):
    P, x, nn, A, cnt_g = features(word, alpha, eps)
    Prev, _, _, B, cnt_g_rev = features(word[::-1], alpha, eps)
    assert cnt_g == cnt_g_rev and Prev == P
    nTot = (cnt_g + A[0] + A[1] + A[2]) % 2
    # n_p reconstruction
    for p in range(3):
        pred = (A[(p + eps) % 3] + B[(P - p) % 3] + nTot) % 2
        if pred != nn[p] % 2:
            return ('n', p, word)
    # x_p reconstruction
    for p in range(3):
        pred = (A[(p + eps) % 3] + A[(p + 2 * eps) % 3]
                + B[(P - p - eps) % 3] + nTot) % 2
        if pred != x[p] % 2:
            return ('x', p, word)
    return None


def check_pfree(word, alpha, eps):
    """The *phase-free* recovery actually formalised in `A4MoverCut`:

        occ p  =  |w|_g + occL (p + 2 eps) + occR (p + eps)      (mod 2)

    where `occ p` counts occurrences of `g` at entry phase `p`, `occL p` those
    of them not preceded by `g`, and `occR p` those not followed by `g`.  It
    follows from counting the `gg` digrams twice -- once by the entry phase of
    the first letter, once by that of the second -- and, unlike `check`, it
    does not mention the total phase `P`.
    """
    ph = dict(alpha)
    n = len(word)
    entry = [0] * (n + 1)
    for i, c in enumerate(word):
        entry[i + 1] = (entry[i] + ph[c]) % 3
    occ = [0, 0, 0]
    occL = [0, 0, 0]
    occR = [0, 0, 0]
    cnt_g = 0
    for i, c in enumerate(word):
        if c != 'g':
            continue
        cnt_g += 1
        p = entry[i]
        occ[p] += 1
        if i == 0 or word[i - 1] != 'g':
            occL[p] += 1
        if i == n - 1 or word[i + 1] != 'g':
            occR[p] += 1
    for p in range(3):
        pred = (cnt_g + occL[(p + 2 * eps) % 3] + occR[(p + eps) % 3]) % 2
        if pred != occ[p] % 2:
            return ('pfree', p, word)
    return None


def main():
    random.seed(20260728)
    total = 0
    for eps in (1, 2):
        alpha = build_alphabet(eps)
        letters = [c for c, _ in alpha]
        # exhaustive up to length 8
        for L in range(0, 9):
            for tup in itertools.product(letters, repeat=L):
                total += 1
                bad = check(list(tup), alpha, eps) or check_pfree(list(tup), alpha, eps)
                if bad:
                    print('FAIL', eps, bad)
                    return 1
        # random long words
        for _ in range(20000):
            L = random.randint(0, 400)
            w = [random.choice(letters) for _ in range(L)]
            total += 1
            bad = check(w, alpha, eps) or check_pfree(w, alpha, eps)
            if bad:
                print('FAIL', eps, bad)
                return 1
    print(f'PASS: both recovery identities (P-dependent and P-free) hold on {total} words '
          f'(exhaustive length <= 8 over 6 letters, both eps, '
          f'plus 40000 random words of length <= 400)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
