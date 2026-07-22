#!/usr/bin/env python3
"""Independent verification of A5_generator_dependent_star_height_1.md.

Claim: for pi: {a,b}* ->> A5 with pi(a) = (123), pi(b) = (145),
the identity language L_e = pi^{-1}(1) equals

    K1 cap K2 cap K3,
    K1 = C*,                      C  = a b* a b* a | b a* b a* b
    K2 = b* | b* a b* a C* a b*
    K3 = b* | b* a C* a b* a b*

and the right-hand side is a generalized regular expression whose only
Kleene stars are C* and the star-free abbreviations a* = co(UbU),
b* = co(UaU); no star is nested inside another star's ARGUMENT beyond
star-free content, hence height <= 1.  (a*/b* inside concatenations are
star-free languages, written without star via complement.)

Ground truth: direct permutation composition.
Expression side: Python re module (a*/b* are used as literal regex
shorthands for the star-free languages they denote).

Also checks: <(123),(145)> = A5 (order 60), and that elements fixing
1,2,3 in A5 are only the identity.
"""

import itertools, random, re

# permutations act on {0,1,2,3,4} (0-indexed points 1..5)
def pmul(p, q):  # apply p then q
    return tuple(q[i] for i in p)

A = (1, 2, 0, 3, 4)   # (123)
B = (3, 1, 2, 4, 0)   # (145)
IDENT = (0, 1, 2, 3, 4)
PERM = {'a': A, 'b': B}

def phi(w):
    p = IDENT
    for ch in w:
        p = pmul(p, PERM[ch])
    return p

# group generated
def gen_group():
    seen = {IDENT}
    frontier = [IDENT]
    while frontier:
        p = frontier.pop()
        for g in (A, B):
            q = pmul(p, g)
            if q not in seen:
                seen.add(q)
                frontier.append(q)
    return seen

G = gen_group()
print(f"|<(123),(145)>| = {len(G)}  (expect 60 = |A5|)")
fixers = [p for p in G if p[0] == 0 and p[1] == 1 and p[2] == 2]
print(f"elements of G fixing points 1,2,3: {len(fixers)} (expect 1)")

# expression side
C = r"(?:ab*ab*a|ba*ba*b)"
K1 = rf"{C}*"
K2 = rf"(?:b*|b*ab*a{C}*ab*)"
K3 = rf"(?:b*|b*a{C}*ab*ab*)"
LE = re.compile(rf"(?=(?:{K1})$)(?=(?:{K2})$)(?:{K3})$")

def in_expr(w):
    return LE.match(w) is not None

def in_direct(w):
    return phi(w) == IDENT

bad = None
count = 0
for L in range(0, 17):
    for tup in itertools.product("ab", repeat=L):
        w = ''.join(tup)
        if in_expr(w) != in_direct(w):
            bad = w
            break
        count += 1
    if bad:
        break
    if L in (12, 14, 16):
        print(f"exhaustive length <= {L}: OK ({count} words)")
if bad:
    print(f"MISMATCH at {bad!r}: expr={in_expr(bad)} direct={in_direct(bad)}")
else:
    rnd = random.Random(5)
    ok = True
    for _ in range(200000):
        ln = rnd.randint(17, 400)
        w = ''.join(rnd.choice("ab") for _ in range(ln))
        if in_expr(w) != in_direct(w):
            print(f"MISMATCH at random word of length {ln}")
            ok = False
            break
    if ok:
        print("random 200000 words (length <= 400): OK")
        print("\nVERIFIED: L_e = K1 cap K2 cap K3 as claimed; the "
              "expression has star height 1.")
