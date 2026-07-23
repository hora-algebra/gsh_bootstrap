#!/usr/bin/env python3
"""Weis's ACTUAL open language L2 vs the certified stage-2 feature family.

CONTEXT
  Weis (2011, UMass thesis, DOI 10.7275/2177022) leaves OPEN whether
      L2 := L( (a b* a  |  b a* b (a b* a)* b a* b)* )   over {a,b}
  has generalized star-height 2.  Its syntactic monoid is a GROUP of
  order 48 (= C2 x S4), non-nilpotent (sanity-checked below).

  RESULTS.md Sec. 5.9 / scripts/weis_l2_family.py prove (exact product
  automata, no sampling) that every Boolean combination of the certified
  stage-2 features has generalized star-height <= 1.  The certified base
  feature machines (weis_l2_family.py step [4]) are:
      LC(8,4)                    |w|_a mod 8, |w|_b mod 4
      Flags(2)                   seen-b flag, initial a-run length mod 2
      CodeTok({b,aa,ab}, mod 4)  flat token count of the finite prefix
                                 code X = {b, aa, ab} (+ partial-token
                                 alignment / tail flag)
      W(2,0,4), W(2,1,4)         cumulative W atoms N_r^(2) mod 4
                                 (b's at phase r; phase = #a mod 2)
  and every stage-2 atom (N_{p,q} mod 2/4, T' mod 4) was PROVEN to be a
  function of these states, hence height <= 1 (claim WEIS-L2-M2-01).

QUESTION ANSWERED HERE (exact, no sampling)
  Is membership in the ACTUAL L2 a function of the certified stage-2
  feature state?  If YES, L2 has height <= 1 by WEIS-L2-M2-01.  If NO,
  the certified family does not capture L2 -- and NOTHING is claimed
  about height >= 2 (a NOT-a-function verdict is only about this family).

METHOD
  Same product-automaton criterion as weis_l2_family.prove_function:
  BFS the reachable product (feature states) x (min DFA of L2); L2 is a
  function of the features iff acceptance is constant on each feature
  cell.  BFS additionally yields a SHORTEST witness pair on failure
  (two words with identical feature vectors, different L2 membership).

Run:  python3 scripts/weis_l2_actual.py     (seconds, stdlib only)
"""

import os
import re
import sys
from collections import Counter, deque
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import weis_l2_family as F

ALPHA = "ab"

L2_REGEX = re.compile(r"(?:ab*a|ba*b(?:ab*a)*ba*b)*")


# --------------------------------------------------------------- L2 DFA
def build_l2_min_dfa():
    """Minimal complete DFA of L2 from the printed regex, via
    eps-NFA -> subset construction -> partition-refinement minimization.
    Returns (trans[(q,ch)] -> q', start, finals:set, nstates)."""
    trans, eps = {}, {}

    def add(s, sym, t):
        trans.setdefault((s, sym), set()).add(t)

    def adde(s, t):
        eps.setdefault(s, set()).add(t)

    # 0 = start/accept of the outer star
    # A-branch  a b* a : 0-a->1, 1-b->1, 1-a->2, eps 2->0
    add(0, "a", 1); add(1, "b", 1); add(1, "a", 2); adde(2, 0)
    # B-branch  b a* b (a b* a)* b a* b :
    add(0, "b", 3); add(3, "a", 3); add(3, "b", 4)          # first ba*b
    add(4, "a", 5); add(5, "b", 5); add(5, "a", 6); adde(6, 4)  # (ab*a)*
    add(4, "b", 7); add(7, "a", 7); add(7, "b", 8); adde(8, 0)  # second ba*b

    def eclose(S):
        S = set(S)
        stack = list(S)
        while stack:
            s = stack.pop()
            for t in eps.get(s, ()):
                if t not in S:
                    S.add(t)
                    stack.append(t)
        return frozenset(S)

    start_set = eclose({0})
    dstates = {start_set: 0}
    dtrans = {}
    queue = deque([start_set])
    while queue:
        S = queue.popleft()
        for c in ALPHA:
            T = eclose({t for s in S for t in trans.get((s, c), ())})
            if T not in dstates:
                dstates[T] = len(dstates)
                queue.append(T)
            dtrans[(dstates[S], c)] = dstates[T]
    finals = {i for S, i in dstates.items() if 0 in S}
    n = len(dstates)

    # minimize (Moore partition refinement)
    part = {i: (i in finals) for i in range(n)}
    while True:
        sig = {i: (part[i], tuple(part[dtrans[(i, c)]] for c in ALPHA))
               for i in range(n)}
        classes = {}
        for i in range(n):
            classes.setdefault(sig[i], []).append(i)
        newpart = {}
        for k, members in enumerate(classes.values()):
            for m_ in members:
                newpart[m_] = k
        stable = len(set(newpart.values())) == len(set(part.values()))
        part = newpart
        if stable:
            break
    m = len(set(part.values()))
    mind = {}
    for i in range(n):
        for c in ALPHA:
            mind[(part[i], c)] = part[dtrans[(i, c)]]
    return mind, part[dstates[start_set]], {part[i] for i in finals}, m


def dfa_member(mind, start, finals, w):
    q = start
    for ch in w:
        q = mind[(q, ch)]
    return q in finals


# ------------------------------------------------- monoid sanity checks
def monoid_checks(mind, m):
    ident = tuple(range(m))

    def comp(f, g):        # apply f then g
        return tuple(g[f[q]] for q in range(m))

    ta = tuple(mind[(q, "a")] for q in range(m))
    tb = tuple(mind[(q, "b")] for q in range(m))
    monoid = {ident}
    queue = deque([ta, tb])
    monoid.update(queue)
    while queue:
        f = queue.popleft()
        for g in (ta, tb):
            h = comp(f, g)
            if h not in monoid:
                monoid.add(h)
                queue.append(h)
    G = monoid
    is_group = all(len(set(f)) == m for f in G)

    def inv(f):
        r = [0] * m
        for q in range(m):
            r[f[q]] = q
        return tuple(r)

    def comm(x, y):
        return comp(comp(comp(inv(x), inv(y)), x), y)

    def gen_subgroup(gens):
        S = {ident}
        queue = deque([ident])
        gens = set(gens)
        while queue:
            f = queue.popleft()
            for g in gens:
                h = comp(f, g)
                if h not in S:
                    S.add(h)
                    queue.append(h)
        return S

    # lower central series (nilpotency test)
    lcs, cur = [len(G)], G
    for _ in range(8):
        cur = gen_subgroup({comm(x, y) for x in cur for y in G})
        lcs.append(len(cur))
        if len(cur) == 1 or lcs[-1] == lcs[-2]:
            break
    # derived series (solvability)
    ds, cur = [len(G)], G
    for _ in range(8):
        cur = gen_subgroup({comm(x, y) for x in cur for y in cur})
        ds.append(len(cur))
        if len(cur) == 1 or ds[-1] == ds[-2]:
            break

    def order(f):
        k, g = 1, f
        while g != ident:
            g = comp(g, f)
            k += 1
        return k

    hist = Counter(order(f) for f in G)
    center = sum(1 for x in G if all(comp(x, y) == comp(y, x) for y in G))
    return {"order": len(G), "group": is_group, "lcs": lcs, "ds": ds,
            "orders": dict(sorted(hist.items())), "center": center}


# ---------------------------------- exact function-of-features product test
def tabulate(f):
    """Lazily tabulate one feature machine: reachable states + int trans."""
    states = [f.init]
    index = {f.init: 0}
    trans = []
    i = 0
    while i < len(states):
        row = []
        for ch in ALPHA:
            t = f.step(states[i], ch)
            j = index.get(t)
            if j is None:
                j = len(states)
                index[t] = j
                states.append(t)
            row.append(j)
        trans.append(row)
        i += 1
    return states, trans


def function_test(feats, mind, start, finals, ndfa, cap=15_000_000):
    """Exact: is DFA acceptance constant on each feature cell of the
    reachable product?  Returns (verdict, witness, explored):
    verdict True/False/None(cap); witness = (w1, w2) shortest conflicting
    pair on False."""
    tabs = [tabulate(f) for f in feats]
    ftrans = [t for _, t in tabs]
    nf = len(feats)
    radices = [len(s) for s, _ in tabs] + [ndfa]
    dfa_next = [[mind[(q, c)] for c in ALPHA] for q in range(ndfa)]
    fin = [q in finals for q in range(ndfa)]

    def pack(comp):
        x = 0
        for r, c in zip(radices, comp):
            x = x * r + c
        return x

    def unpack(x):
        comp = [0] * (nf + 1)
        for i in range(nf, -1, -1):
            x, comp[i] = divmod(x, radices[i])
        return comp

    start_comp = [0] * nf + [start]
    x0 = pack(start_comp)
    parent = {x0: None}
    cell = {x0 // ndfa: (fin[start], x0)}
    queue = deque([x0])

    def word_of(x):
        out = []
        while parent[x] is not None:
            x, ci = parent[x]
            out.append(ALPHA[ci])
        return "".join(reversed(out))

    while queue:
        x = queue.popleft()
        comp = unpack(x)
        for ci in range(2):
            ncomp = [ftrans[i][comp[i]][ci] for i in range(nf)]
            ncomp.append(dfa_next[comp[nf]][ci])
            nx = pack(ncomp)
            if nx in parent:
                continue
            if len(parent) >= cap:
                return None, None, len(parent)
            parent[nx] = (x, ci)
            v = fin[ncomp[nf]]
            fp = nx // ndfa
            got = cell.get(fp)
            if got is None:
                cell[fp] = (v, nx)
            elif got[0] != v:
                return False, (word_of(got[1]), word_of(nx)), len(parent)
            queue.append(nx)
    return True, None, len(parent)


# ------------------------------------------------------- feature families
X = ["b", "aa", "ab"]
X3 = ["b", "aaa", "ab", "aab"]
Z3 = ["b", "aaa", "aab", "aba", "abb"]


def base_feats():
    """EXACTLY the certified stage-2 feature machines of
    weis_l2_family.main() step [4] (claim WEIS-L2-M2-01)."""
    return [F.LC(8, 4), F.Flags(2), F.CodeTok(X, 4, "X"),
            F.WTargetFeature(2, 0, 4), F.WTargetFeature(2, 1, 4)]


BASE_DESC = ("LC(8,4) [|w|_a mod 8, |w|_b mod 4], Flags(2) [seen-b, initial "
             "a-run mod 2], CodeTok({b,aa,ab}) count mod 4 [+alignment], "
             "W(2,0,4), W(2,1,4) [b's at phase 0/1 mod 4, phase = #a mod 2]")


def verify_witness(feats, mind, start, finals, w1, w2, label):
    """Independent re-check of a witness pair: identical feature vectors
    (running the ORIGINAL feature objects, not the tabulated copies),
    different membership (DFA and independent `re` engine agree)."""
    v1 = tuple(run_feature(f, w1) for f in feats)
    v2 = tuple(run_feature(f, w2) for f in feats)
    assert v1 == v2, (label, "feature vectors differ!", v1, v2)
    m1 = dfa_member(mind, start, finals, w1)
    m2 = dfa_member(mind, start, finals, w2)
    assert m1 != m2, (label, "same membership?!")
    r1 = L2_REGEX.fullmatch(w1) is not None
    r2 = L2_REGEX.fullmatch(w2) is not None
    assert (r1, r2) == (m1, m2), (label, "re engine disagrees with DFA")
    return v1, m1, m2


def run_feature(f, w):
    s = f.init
    for ch in w:
        s = f.step(s, ch)
    return s


# ---------------------------------------------------------------- driver
def main():
    print("== Weis's actual L2 vs the certified stage-2 feature family ==\n")

    # [1] build + sanity-check the DFA / syntactic monoid
    mind, start, finals, m = build_l2_min_dfa()
    print(f"[1] minimal DFA of L2 = ((ab*a | ba*b(ab*a)*ba*b))*: "
          f"{m} states, start {start}, finals {sorted(finals)}")
    assert m == 6, m

    bad = None
    for L in range(15):
        for xbits in range(2 ** L):
            w = "".join(ALPHA[(xbits >> i) & 1] for i in range(L))
            if dfa_member(mind, start, finals, w) != \
                    (L2_REGEX.fullmatch(w) is not None):
                bad = w
                break
        if bad:
            break
    assert bad is None, bad
    print("    DFA == independent `re` engine on ALL 32767 words, len <= 14.")

    info = monoid_checks(mind, m)
    print(f"    syntactic monoid: order {info['order']}, "
          f"group = {info['group']}")
    print(f"    element-order histogram {info['orders']} "
          f"(matches C2 x S4)")
    print(f"    lower central series {info['lcs']} -> "
          f"non-nilpotent = {info['lcs'][-1] != 1}")
    print(f"    derived series {info['ds']} -> solvable = "
          f"{info['ds'][-1] == 1}; center size {info['center']}")
    assert info["order"] == 48 and info["group"]
    assert info["orders"] == {1: 1, 2: 19, 3: 8, 4: 12, 6: 8}  # C2 x S4
    assert info["lcs"][-1] != 1          # NON-nilpotent
    assert info["ds"][-1] == 1 and info["center"] == 2
    print()

    # [2] the main exact test: certified stage-2 base features
    print("[2] EXACT function-of-features test (product-automaton BFS,")
    print("    same criterion as weis_l2_family.prove_function):")
    print(f"    features = {BASE_DESC}")
    feats = base_feats()
    verdict, wit, explored = function_test(feats, mind, start, finals, m)
    print(f"    explored {explored} reachable product states.")
    if verdict is True:
        print("\nVERDICT: L2 IS a function of certified stage-2 features"
              " (=> height <= 1 by WEIS-L2-M2-01)")
        return
    assert verdict is False
    w1, w2 = wit
    _, m1, m2 = verify_witness(feats, mind, start, finals, w1, w2, "base")
    pairs1, t1, _ = F.brute_counts(w1)
    pairs2, t2, _ = F.brute_counts(w2)
    print("\nVERDICT: L2 is NOT a function of the certified stage-2 feature")
    print("vector.  Shortest witness pair (equal feature vectors, different")
    print("membership; verified independently with the `re` engine):")
    print(f"    w1 = {w1!r}  (len {len(w1)})  in L2: {m1}")
    print(f"    w2 = {w2!r}  (len {len(w2)})  in L2: {m2}")
    print(f"    shared certified-atom values: "
          f"N_pq mod 4 = {dict(pairs1)} == {dict(pairs2)}, "
          f"T' mod 4 = {t1 % 4} == {t2 % 4}")
    assert {k: v % 4 for k, v in pairs1.items()} == \
           {k: v % 4 for k, v in pairs2.items()} and t1 % 4 == t2 % 4
    print("    (NOTE: this verdict says NOTHING about height >= 2; only that")
    print("    the certified family does not capture L2.)\n")

    # [3] sharpen the failure: extensions
    print("[3] extensions tried (all exact; diagnostic only -- extension")
    print("    features beyond the certified set carry NO height certificate")
    print("    here, so even a YES would not certify height <= 1):")

    exts = [
        ("(a) + all certified stage-2 atoms as features "
         "(N_pq mod 4 x4, T' mod 4)",
         base_feats() + [F.PairTarget(2, p, q, 4)
                         for p, q in product((0, 1), repeat=2)]
         + [F.RunResidue(2, 1, 4)]),
        ("(b) doubled moduli: LC(16,8), Flags(2), CodeTok(X mod 8), "
         "W(2,r,8), Runs mod 8",
         [F.LC(16, 8), F.Flags(2), F.CodeTok(X, 8, "X8"),
          F.WTargetFeature(2, 0, 8), F.WTargetFeature(2, 1, 8),
          F.RunResidue(2, 1, 8)]),
        ("(c) full --m3 constructor set on top of the base: LC(72,8), "
         "Flags(2), Flags(3), CodeTok(X mod 4), CodeTok(X3 mod 6), "
         "CodeTok(Z3 mod 6), W(2,r,4), W(3,r,6)",
         [F.LC(72, 8), F.Flags(2), F.Flags(3), F.CodeTok(X, 4, "X"),
          F.CodeTok(X3, 6, "X3"), F.CodeTok(Z3, 6, "Z3"),
          F.WTargetFeature(2, 0, 4), F.WTargetFeature(2, 1, 4),
          F.WTargetFeature(3, 0, 6), F.WTargetFeature(3, 1, 6),
          F.WTargetFeature(3, 2, 6)]),
    ]
    for label, efeats in exts:
        v, wit, explored = function_test(efeats, mind, start, finals, m)
        if v is None:
            print(f"    {label}:\n        CAP EXCEEDED after {explored} "
                  f"states (verdict undecided)")
            continue
        if v is True:
            print(f"    {label}:\n        IS a function "
                  f"({explored} states) -- see NOTE above")
            continue
        ww1, ww2 = wit
        verify_witness(efeats, mind, start, finals, ww1, ww2, label)
        print(f"    {label}:\n        NOT a function ({explored} states); "
              f"shortest witness w1={ww1!r}, w2={ww2!r}")
    print("\nCONCLUSION: the actual Weis L2 (syntactic monoid C2 x S4,")
    print("order 48, non-nilpotent) is NOT captured by the certified")
    print("stage-2 family of WEIS-L2-M2-01, nor by the tested extensions.")
    print("Its generalized star height remains OPEN (1 or 2).")


if __name__ == "__main__":
    main()
