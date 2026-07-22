#!/usr/bin/env python3
"""The (2,3,5)-type generating set s=(12)(34), t=(135) of A5:
systematic study of why all current methods fail, machine-verified.

FACT 1 (involution obstruction, all actions).  In EVERY faithful
transitive action of A5, the involution s acts with at least two
2-cycles (a single transposition would be odd, and A5 actions
preserve parity... more robustly: we just compute).  The anchor
criterion needs an anchor point lying on EVERY nontrivial cycle of
EVERY generator; one point cannot lie on two disjoint 2-cycles, so
the forced-walk method fails at every anchor of every action.

FACT 2 (3-cycle sets without common support point).  Generating sets
like (123),(145),(245) have no involution, but no common point on all
three cycles; machine check: every anchor of every action fails too.

FACT 3 (tantalizing dead end).  The derived generators u1 = st,
u2 = st^2 are BOTH 5-cycles, and the derived word problem passes the
anchor criterion (height 1!).  But pulling back along u_c -> s t^{c+3k}
requires (ttt)* inside the star (height 2), and words with t-blocks
of length = 0 mod 3 reintroduce the bare involution s.  So this does
not resolve the original alphabet.

Also: 5-point action interior structure at anchor 5 in coordinates
(column, level): the noise is the mutual pair of counters
  E = #(t at level even)  mod 3   (column)
  G = #(s at column != gamma) mod 2 (level)
each conditioned on the other -- no letter-count homomorphism grounds
them (A5 is perfect: no nontrivial abelian quotient).
"""

from itertools import permutations

def pmul(p, q):
    return tuple(q[i] for i in p)

IDENT5 = (0, 1, 2, 3, 4)

def parity(p):
    seen, par = set(), 0
    for i in range(len(p)):
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

def cyc(*cycles, n=5):
    m = list(range(n))
    for c in cycles:
        for k in range(len(c)):
            m[c[k] - 1] = c[(k + 1) % len(c)] - 1
    return tuple(m)

S = cyc((1, 2), (3, 4))
T = cyc((1, 3, 5))

def subgroup(gens):
    seen = {IDENT5}
    frontier = [IDENT5]
    while frontier:
        p = frontier.pop()
        for g in gens:
            q = pmul(p, g)
            if q not in seen:
                seen.add(q)
                frontier.append(q)
    return seen

# representative subgroups of A5 (one per conjugacy class of order)
SUBGROUPS = {
    "A4 (idx 5)":  subgroup([cyc((1, 2, 3)), cyc((1, 2), (3, 4))]),
    "D5 (idx 6)":  subgroup([cyc((1, 2, 3, 4, 5)), cyc((2, 5), (3, 4))]),
    "S3 (idx 10)": subgroup([cyc((1, 2, 3)), cyc((1, 2), (4, 5))]),
    "Z5 (idx 12)": subgroup([cyc((1, 2, 3, 4, 5))]),
    "V4 (idx 15)": subgroup([cyc((1, 2), (3, 4)), cyc((1, 3), (2, 4))]),
    "Z3 (idx 20)": subgroup([cyc((1, 2, 3))]),
    "Z2 (idx 30)": subgroup([cyc((1, 2), (3, 4))]),
    "1  (idx 60)": {IDENT5},
}

def coset_action(H):
    """right cosets Hx, action x -> xg. Returns (n, act) with
    act[g] = tuple mapping coset index -> coset index."""
    H = frozenset(H)
    cosets = []
    seen = set()
    for x in A5:
        if x in seen:
            continue
        cos = frozenset(pmul(h, x) for h in H)
        seen |= cos
        cosets.append(cos)
    idx = {}
    for i, cos in enumerate(cosets):
        for x in cos:
            idx[x] = i
    def act(g):
        out = [None] * len(cosets)
        for i, cos in enumerate(cosets):
            x = next(iter(cos))
            out[i] = idx[pmul(x, g)]
        return tuple(out)
    return len(cosets), act

def cycles_of(p):
    seen, cyclist = set(), []
    for i in range(len(p)):
        if i in seen:
            continue
        c, j = [], i
        while j not in seen:
            seen.add(j)
            c.append(j)
            j = p[j]
        if len(c) > 1:
            cyclist.append(c)
    return cyclist

def anchor_exists(perms, n):
    """is there a point lying on every nontrivial cycle of every perm?"""
    ok_points = set(range(n))
    for p in perms:
        for c in cycles_of(p):
            pass
        # a point must lie on EVERY nontrivial cycle of p;
        # possible only if p has <= 1 nontrivial cycle
        cycs = cycles_of(p)
        if not cycs:
            continue
        pts = set(cycs[0])
        for c in cycs[1:]:
            pts &= set(c)
        ok_points &= pts
    return sorted(ok_points)

def survey(name, gens5):
    print(f"--- generating set {name} ---")
    for hname, H in SUBGROUPS.items():
        n, act = coset_action(H)
        perms = [act(g) for g in gens5]
        ct = ["+".join(str(len(c)) for c in cycles_of(p)) or "id"
              for p in perms]
        anch = anchor_exists(perms, n)
        print(f"  action on {n:2d} points ({hname}): cycle types "
              f"{ct}; anchors: {anch if anch else 'NONE'}")

def walk_machine(perms, n, anchor):
    states = ['S'] + [x for x in range(n) if x != anchor] + ['E', 'D']
    def step(st, gi):
        if st in ('E', 'D'):
            return 'D'
        x = anchor if st == 'S' else st
        y = perms[gi][x]
        return 'E' if y == anchor else y
    return states, step

def aperiodic(states, step, ngens, cap=1_000_000):
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)
    gmaps = {tuple(idx[step(s, gi)] for s in states) for gi in range(ngens)}
    monoid = set(gmaps)
    frontier = list(gmaps)
    while frontier:
        f = frontier.pop()
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

def main():
    print("=== FACT 1+2: anchor existence in ALL transitive actions ===")
    survey("{(12)(34),(135)} (2,3,5-type)", [S, T])
    survey("{(123),(145),(245)} (3-cycles, no common point)",
           [cyc((1, 2, 3)), cyc((1, 4, 5)), cyc((2, 4, 5))])
    survey("{(123),(145)} (control: common point 1)",
           [cyc((1, 2, 3)), cyc((1, 4, 5))])

    print("\n=== FACT 3: derived generators st, st^2 ===")
    U1 = pmul(S, T)
    U2 = pmul(S, pmul(T, T))
    print(f"  st   cycles: {cycles_of(U1)}  (5-cycle)")
    print(f"  st^2 cycles: {cycles_of(U2)}  (5-cycle)")
    print(f"  <st, st^2> order: {len(subgroup([U1, U2]))}")
    results = []
    for anchor in range(5):
        states, step = walk_machine([U1, U2], 5, anchor)
        ok, m = aperiodic(states, step, 2)
        results.append((anchor + 1, ok, m))
    good = [a for a, ok, _ in results if ok]
    print(f"  derived word problem anchor criterion: passing anchors "
          f"{good} -> height 1 over the DERIVED alphabet")
    print("  but pullback u_c -> s t^(c+3k) needs (ttt)* inside the "
          "star, and zero t-blocks reintroduce the involution s.")

    print("\n=== double check: aperiodicity fails at every anchor of the "
          "6-point action for {s,t} ===")
    n, act = coset_action(SUBGROUPS["D5 (idx 6)"])
    perms = [act(S), act(T)]
    for anchor in range(n):
        states, step = walk_machine(perms, n, anchor)
        ok, m = aperiodic(states, step, 2)
        print(f"  anchor {anchor+1}: aperiodic={ok} (monoid {m})")

if __name__ == "__main__":
    main()
