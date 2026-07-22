#!/usr/bin/env python3
"""Where exactly does the A5 height-1 frontier lie?

CRITERION (assembly lemma, cf. section 5.6):
Let S be a set of generators of A5 acting on {1..5} and p an anchor
point.  Build the walk machine M with states
  START (at p, word start), interior points (all points except p),
  E (just returned to p), DEAD,
transitions x --g--> (E if x.g == p else x.g), E -> DEAD.
If the transition monoid of M is APERIODIC, then all of
  C   = first-return code to p        (START -> E)
  B_i = i -> first visit of p         (i -> E)
  D_i = p -> i, avoiding p afterwards (START -> i)
  A_i = i -> i avoiding p             (i -> i)
are star-free, K_p = C*, K_i = A_i cup B_i C* D_i, and since the
stabilizer of any 3 points of A5 is trivial,
  L_e = K_{i1} cap K_{i2} cap K_{i3}   (any 3 points incl. p)
has generalized star height <= 1 (single star C*, unique
factorization into first returns).

This file machine-checks the criterion for several generating sets and
for the full 60-element alphabet, plus structural obstructions:
  * full alphabet: every anchor fails (Stab(p) letters cycle interior);
  * (2,3,5)-generators (12)(34),(135): every anchor fails;
  * the 5-point action admits no nontrivial congruence (primitivity),
    so no quotient "phase" automaton exists to hang cut-features on.
"""

import itertools
from itertools import permutations

def pmul(p, q):  # apply p then q
    return tuple(q[i] for i in p)

IDENT = (0, 1, 2, 3, 4)

def parity(p):
    seen, par = set(), 0
    for i in range(5):
        if i in seen:
            continue
        j, ln = i, 0
        while j not in seen:
            seen.add(j)
            j = p[j]
            ln += 1
        par ^= (ln - 1) % 2
    return par

A5 = [p for p in permutations(range(5)) if parity(p) == 0]
assert len(A5) == 60

def cyc(*cycles):
    m = list(range(5))
    for c in cycles:
        for k in range(len(c)):
            m[c[k] - 1] = c[(k + 1) % len(c)] - 1
    return tuple(m)

def gen_group(gens):
    seen = {IDENT}
    frontier = [IDENT]
    while frontier:
        p = frontier.pop()
        for g in gens:
            q = pmul(p, g)
            if q not in seen:
                seen.add(q)
                frontier.append(q)
    return seen

def walk_machine(gens, anchor):
    """states: 'S'(start,at anchor), interior points, 'E', 'D'."""
    states = ['S'] + [x for x in range(5) if x != anchor] + ['E', 'D']
    def step(st, g):
        if st in ('E', 'D'):
            return 'D'
        x = anchor if st == 'S' else st
        y = g[x]
        return 'E' if y == anchor else y
    return states, step

def aperiodic(states, step, gens, cap=2_000_000):
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)
    gmaps = {tuple(idx[step(s, g)] for s in states) for g in gens}
    monoid = set(gmaps)
    frontier = list(gmaps)
    while frontier:
        f = frontier.pop()
        # early aperiodicity test on f
        seen_p, g, k = {}, f, 0
        while g not in seen_p:
            seen_p[g] = k
            g = tuple(f[g[i]] for i in range(n))
            k += 1
        if k - seen_p[g] != 1:
            return False, len(monoid)
        for h0 in gmaps:
            h = tuple(h0[f[i]] for i in range(n))
            if h not in monoid:
                monoid.add(h)
                frontier.append(h)
                if len(monoid) > cap:
                    return None, len(monoid)
    return True, len(monoid)

def check_criterion(name, gens):
    G = gen_group(gens)
    tag = f"|<gens>|={len(G)}"
    results = []
    for anchor in range(5):
        states, step = walk_machine(gens, anchor)
        ok, msize = aperiodic(states, step, gens)
        results.append((anchor, ok, msize))
    good = [a for a, ok, _ in results if ok is True]
    print(f"{name}: {tag}; anchors passing criterion: "
          f"{[a+1 for a in good] if good else 'NONE'}")
    for a, ok, m in results:
        print(f"    anchor {a+1}: aperiodic={ok} (monoid {m})")
    if good and len(G) == 60:
        print(f"    => word problem of A5 over these generators has "
              f"generalized star height <= 1 (anchor {good[0]+1}).")
    elif not good:
        print(f"    => forced-walk/anchor method FAILS for this set.")
    return bool(good)

def congruence_check():
    """no nontrivial congruence of the 5-point A5-action (primitivity)."""
    def partitions(coll):
        if len(coll) == 1:
            yield [coll]
            return
        first, rest = coll[0], coll[1:]
        for smaller in partitions(rest):
            for k in range(len(smaller)):
                yield smaller[:k] + [[first] + smaller[k]] + smaller[k+1:]
            yield [[first]] + smaller
    nontrivial = 0
    for part in partitions(list(range(5))):
        if len(part) in (1, 5):
            continue
        blk = {}
        for bi, b in enumerate(part):
            for x in b:
                blk[x] = bi
        if all(len({blk[g[x]] for x in b}) == 1 for g in A5 for b in part):
            nontrivial += 1
    print(f"nontrivial congruences of the 5-point action under full "
          f"alphabet: {nontrivial} (expect 0: primitive)")

def main():
    print("=== criterion checks ===")
    check_criterion("gens (123),(145)      ", [cyc((1,2,3)), cyc((1,4,5))])
    check_criterion("gens (12345),(123)    ", [cyc((1,2,3,4,5)), cyc((1,2,3))])
    check_criterion("gens (123),(124)      ", [cyc((1,2,3)), cyc((1,2,4))])
    check_criterion("gens (123),(345)      ", [cyc((1,2,3)), cyc((3,4,5))])
    check_criterion("gens (12)(34),(135)   ", [cyc((1,2),(3,4)), cyc((1,3,5))])
    check_criterion("FULL 60-letter alphabet", A5)

    print("\n=== structural obstructions for the full alphabet ===")
    # 1) any anchor p: letters in Stab(p) act on the interior as A4
    p = 0
    stab = [g for g in A5 if g[p] == p and g != IDENT]
    print(f"anchor 1: {len(stab)} nonidentity letters fix the anchor and "
          f"permute the interior without exit -> interior monoid contains "
          f"A4 (non-aperiodic).")
    # 2) regular action (60 points): coset cycling demo
    g = cyc((1,2,3))
    print("regular action: for letter g=(123) (order 3), any coset "
          "x<g> with x not in <g> is cycled by g without ever passing "
          "the identity -> first-return code to e is not star-free.")
    # 3) primitivity
    congruence_check()

if __name__ == "__main__":
    main()
