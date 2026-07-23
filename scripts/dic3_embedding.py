"""Machine verification of the Dic3 -> (C3 x C4) x| C2 embedding (RESULTS.md section 3).

Checks, by exhaustive finite computation (standard library only):

  [1] In H = (C3 x C4) x| C2 with tau(x, y) = (-x, y), the elements
      a = ((1,0),0), b = ((0,1),1) satisfy a^3 = b^4 = e and b^-1 a b = a^-1.
  [2] The subgroup <a, b> of H has exactly 12 elements, namely a^i b^j
      (0 <= i < 3, 0 <= j < 4), all distinct.
  [3] <a, b> is nonabelian with element-order profile {1:1, 2:1, 3:2, 4:6, 6:2},
      which among the five groups of order 12 identifies Dic3 uniquely
      (C12 and C6xC2 are abelian; D12 has 7 involutions; A4 has profile
      {1:1, 2:3, 3:8}).
  [4] A = C3 x C4 = {((x,y),0)} is an abelian normal subgroup of H with
      H/A of order 2, so H lies in the Pin-Straubing-Therien class
      "abelian group extended by an elementary abelian 2-group".
  [5] No subgroup of H of order 12 has the element-order profile of A4
      (bounded sanity companion to the general non-division argument).

Run: python3 scripts/dic3_embedding.py
"""

from collections import Counter
from itertools import product


def mul(u, v):
    (x1, y1), e1 = u
    (x2, y2), e2 = v
    s = -1 if e1 else 1
    return ((x1 + s * x2) % 3, (y1 + y2) % 4), (e1 + e2) % 2


E = ((0, 0), 0)


def inv(u):
    for v in H_ELEMENTS:
        if mul(u, v) == E:
            return v
    raise AssertionError("no inverse found")


def power(u, n):
    acc = E
    for _ in range(n):
        acc = mul(acc, u)
    return acc


H_ELEMENTS = [((x, y), e) for x in range(3) for y in range(4) for e in range(2)]


def closure(gens):
    seen = set(gens) | {E}
    frontier = list(seen)
    while frontier:
        nxt = []
        for u in frontier:
            for g in gens:
                for w in (mul(u, g), mul(g, u)):
                    if w not in seen:
                        seen.add(w)
                        nxt.append(w)
        frontier = nxt
    return seen


def order_of(u):
    acc, n = u, 1
    while acc != E:
        acc = mul(acc, u)
        n += 1
    return n


def order_profile(elements):
    return dict(Counter(order_of(u) for u in elements))


def all_subgroups_of_order(n):
    found = set()
    elems = H_ELEMENTS
    for i, g1 in enumerate(elems):
        for g2 in elems[i:]:
            sub = frozenset(closure([g1, g2]))
            if len(sub) == n:
                found.add(sub)
    return found


def main():
    a = ((1, 0), 0)
    b = ((0, 1), 1)

    assert power(a, 3) == E, "a^3 != e"
    assert power(b, 4) == E, "b^4 != e"
    assert mul(mul(inv(b), a), b) == inv(a), "b^-1 a b != a^-1"
    print("[1] PASS relations a^3 = b^4 = e and b^-1 a b = a^-1 hold in H")

    images = {}
    for i, j in product(range(3), range(4)):
        images[(i, j)] = mul(power(a, i), power(b, j))
    assert len(set(images.values())) == 12, "a^i b^j images are not distinct"
    sub = closure([a, b])
    assert sub == set(images.values()), "<a,b> != {a^i b^j}"
    assert len(sub) == 12, "<a,b> does not have order 12"
    print("[2] PASS <a,b> has exactly the 12 distinct elements a^i b^j")

    assert any(mul(u, v) != mul(v, u) for u in sub for v in sub), "abelian"
    profile = order_profile(sub)
    assert profile == {1: 1, 2: 1, 3: 2, 4: 6, 6: 2}, f"profile {profile}"
    print("[3] PASS nonabelian, order profile {1:1,2:1,3:2,4:6,6:2} = Dic3")

    A = {((x, y), 0) for x in range(3) for y in range(4)}
    assert all(mul(u, v) == mul(v, u) for u in A for v in A), "A not abelian"
    for h in H_ELEMENTS:
        hi = inv(h)
        assert all(mul(mul(h, u), hi) in A for u in A), "A not normal"
    assert len(H_ELEMENTS) // len(A) == 2, "H/A does not have order 2"
    print("[4] PASS A = C3 x C4 abelian normal in H, |H/A| = 2 (PST class)")

    a4_profile = {1: 1, 2: 3, 3: 8}
    subs12 = all_subgroups_of_order(12)
    assert subs12, "no order-12 subgroup found (expected at least <a,b>)"
    for sub12 in subs12:
        assert order_profile(sub12) != a4_profile, "A4-like subgroup found"
    print(f"[5] PASS none of the {len(subs12)} order-12 subgroups of H is A4")

    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
