"""Coverage audit for small non-abelian groups: which of them are covered by a
published (or repository-proved) height-one theorem, and which are not?

The question audited here is the *full solution* for a finite group G:

    for every finite alphabet, every monoid morphism phi : Sigma* -> G and every
    accepting subset P subseteq G, the language phi^{-1}(P) has generalized
    star-height at most one.

Reasons a group can be covered (statuses as recorded in CLAIMS_LEDGER.md):

  PST-GRP-01  G commutative                                (CITED, PST 1992)
  PST-GRP-02  G nilpotent of class <= 2                     (CITED, PST 1992)
  PST-GRP-03  G divides A |x| E, A abelian, E elem. ab. 2-group
                                                            (CITED, PST 1992)
  DIC3-RED-01 explicit embedding into the PST-GRP-03 class  (PROVED, this repo)
  A4-ALLLANG-01  A_4                                        (COMPUTED, this repo)

This script decides PST-GRP-01/02 exactly, decides the *direct* semidirect
decomposition of PST-GRP-03 exactly (search over all subgroups), and runs a
bounded search for the *divisor* form of PST-GRP-03 (embeddings into hosts
A |x| C_2^k inside an explicitly reported bound).  A negative divisor search is
a search result, never a lower bound (research rule 1 of README.md).

Everything is exact: constructed groups are validated (closure, associativity,
identity, inverses), the list of non-abelian groups of each order <= 24 is
checked to be pairwise non-isomorphic, and its length is compared against the
standard classification counts (CITED, see NONABELIAN_COUNTS below).

Run:  python3 scripts/research/small_group_pst_coverage.py
      python3 scripts/research/small_group_pst_coverage.py --max-order 24
"""

from __future__ import annotations

import argparse
import itertools
import math
from typing import Callable, Dict, FrozenSet, List, Optional, Sequence, Tuple

# Number of non-abelian groups of order n, for n <= 24.
# CITED: standard classification of groups of small order (number of groups of
# order n is OEIS A000001; the abelian count is the number of multiplicative
# partitions into prime powers).  Used only as a completeness cross-check of the
# hand-built list below.
NONABELIAN_COUNTS: Dict[int, int] = {
    1: 0, 2: 0, 3: 0, 4: 0, 5: 0, 6: 1, 7: 0, 8: 2, 9: 0, 10: 1,
    11: 0, 12: 3, 13: 0, 14: 1, 15: 0, 16: 9, 17: 0, 18: 3, 19: 0, 20: 3,
    21: 1, 22: 1, 23: 0, 24: 12, 25: 0, 26: 1, 27: 2, 28: 2, 29: 0,
    30: 3, 31: 0,
}


class Grp:
    """A finite group given by an explicit element list and a product."""

    def __init__(self, name: str, els: Sequence, mul: Callable) -> None:
        self.name = name
        self.els = list(els)
        self.mul = mul
        self.eset = set(self.els)
        assert len(self.eset) == len(self.els), f"{name}: duplicate elements"
        ids = [e for e in self.els
               if all(mul(e, x) == x and mul(x, e) == x for x in self.els)]
        assert len(ids) == 1, f"{name}: {len(ids)} identities"
        self.e = ids[0]
        self._ord: Dict = {}
        self._gens: Optional[List] = None

    @property
    def order(self) -> int:
        return len(self.els)

    def validate(self) -> None:
        for x in self.els:
            assert self.mul(x, self.e) == x
            for y in self.els:
                assert self.mul(x, y) in self.eset, f"{self.name}: not closed"
        for x in self.els:
            assert any(self.mul(x, y) == self.e for y in self.els), \
                f"{self.name}: missing inverse"
        for x in self.els:
            for y in self.els:
                xy = self.mul(x, y)
                for z in self.els:
                    assert self.mul(xy, z) == self.mul(x, self.mul(y, z)), \
                        f"{self.name}: not associative"

    def order_of(self, g) -> int:
        if g in self._ord:
            return self._ord[g]
        n, x = 1, g
        while x != self.e:
            x = self.mul(x, g)
            n += 1
        self._ord[g] = n
        return n

    def inv(self, g):
        for x in self.els:
            if self.mul(g, x) == self.e:
                return x
        raise AssertionError

    def is_abelian(self) -> bool:
        return all(self.mul(x, y) == self.mul(y, x)
                   for x in self.els for y in self.els)

    def closure(self, gens) -> FrozenSet:
        S = {self.e}
        frontier = [self.e]
        gens = list(gens)
        while frontier:
            x = frontier.pop()
            for g in gens:
                y = self.mul(x, g)
                if y not in S:
                    S.add(y)
                    frontier.append(y)
        return frozenset(S)

    def commutator(self, x, y):
        return self.mul(self.mul(self.inv(x), self.inv(y)), self.mul(x, y))

    def centre(self) -> FrozenSet:
        return frozenset(g for g in self.els
                         if all(self.mul(g, x) == self.mul(x, g)
                                for x in self.els))

    def derived(self) -> FrozenSet:
        return self.closure(self.commutator(x, y)
                            for x in self.els for y in self.els)

    def nilpotency_class(self) -> Optional[int]:
        """Least c with Z_c = G in the upper central series, else None."""
        Z: FrozenSet = frozenset({self.e})
        c = 0
        while len(Z) < self.order:
            nxt = frozenset(g for g in self.els
                            if all(self.commutator(g, x) in Z
                                   for x in self.els))
            if nxt == Z:
                return None  # not nilpotent
            Z, c = nxt, c + 1
        return c

    def all_subgroups(self) -> List[FrozenSet]:
        subs = {frozenset({self.e})}
        frontier = list(subs)
        while frontier:
            new = []
            for S in frontier:
                for g in self.els:
                    if g in S:
                        continue
                    T = self.closure(set(S) | {g})
                    if T not in subs:
                        subs.add(T)
                        new.append(T)
            frontier = new
        return sorted(subs, key=len)

    def is_normal(self, S: FrozenSet) -> bool:
        return all(self.mul(self.mul(g, s), self.inv(g)) in S
                   for g in self.els for s in S)

    def abelian_subset(self, S: FrozenSet) -> bool:
        return all(self.mul(x, y) == self.mul(y, x) for x in S for y in S)

    def elem_abelian_2(self, S: FrozenSet) -> bool:
        return (self.abelian_subset(S)
                and all(self.mul(x, x) == self.e for x in S))

    def generating_set(self) -> List:
        """A small generating set (greedy: largest new closure first)."""
        if self._gens is not None:
            return self._gens
        gens: List = []
        cur = frozenset({self.e})
        while len(cur) < self.order:
            best, bestlen = None, len(cur)
            for g in self.els:
                if g in cur:
                    continue
                c = self.closure(gens + [g])
                if len(c) > bestlen:
                    best, bestlen = g, len(c)
            assert best is not None
            gens.append(best)
            cur = self.closure(gens)
        self._gens = gens
        return gens

    def words(self, gens: Sequence) -> Dict:
        """One straight-line word per element, as an index list into gens."""
        out = {self.e: ()}
        frontier = [self.e]
        while frontier:
            x = frontier.pop(0)
            for i, g in enumerate(gens):
                y = self.mul(x, g)
                if y not in out:
                    out[y] = out[x] + (i,)
                    frontier.append(y)
        assert len(out) == self.order
        return out

    def order_profile(self) -> Tuple[Tuple[int, int], ...]:
        prof: Dict[int, int] = {}
        for g in self.els:
            k = self.order_of(g)
            prof[k] = prof.get(k, 0) + 1
        return tuple(sorted(prof.items()))

    def invariants(self):
        """Isomorphism invariants used to separate groups cheaply."""
        cls_sizes: List[int] = []
        seen = set()
        for g in self.els:
            if g in seen:
                continue
            cl = {self.mul(self.mul(x, g), self.inv(x)) for x in self.els}
            seen |= cl
            cls_sizes.append(len(cl))
        return (self.order, self.order_profile(), len(self.centre()),
                len(self.derived()), tuple(sorted(cls_sizes)))


# ---------------------------------------------------------------- constructors

def cyclic(n: int) -> Grp:
    return Grp(f"C{n}", list(range(n)), lambda x, y: (x + y) % n)


def direct(G: Grp, H: Grp, name: Optional[str] = None) -> Grp:
    return Grp(name or f"{G.name}x{H.name}",
               [(x, y) for x in G.els for y in H.els],
               lambda p, q: (G.mul(p[0], q[0]), H.mul(p[1], q[1])))


def metacyclic(m: int, k: int, r: int, name: Optional[str] = None) -> Grp:
    """C_m |x|_r C_k with b a b^{-1} = a^r; requires r^k = 1 mod m."""
    assert math.gcd(r, m) == 1 and pow(r, k, m) == 1
    els = [(i, j) for i in range(m) for j in range(k)]

    def mul(p, q):
        return ((p[0] + pow(r, p[1], m) * q[0]) % m, (p[1] + q[1]) % k)

    return Grp(name or f"C{m}:{r}C{k}", els, mul)


def dicyclic(n: int) -> Grp:
    """Dic_n = <a, b | a^{2n} = 1, b^2 = a^n, b^{-1} a b = a^{-1}>, order 4n."""
    m = 2 * n
    els = [(i, e) for i in range(m) for e in (0, 1)]

    def mul(p, q):
        i, e = p
        j, f = q
        if e == 0:
            return ((i + j) % m, f)
        if f == 0:
            return ((i - j) % m, 1)
        return ((i - j + n) % m, 0)

    return Grp(f"Dic{n}", els, mul)


def abelian(invs: Sequence[int]) -> Grp:
    els = [tuple(t) for t in itertools.product(*[range(n) for n in invs])]
    return Grp("x".join(f"C{n}" for n in invs), els,
               lambda p, q: tuple((p[i] + q[i]) % invs[i]
                                  for i in range(len(invs))))


def _abelian_endos(invs: Sequence[int]):
    """All endomorphisms of prod C_{invs[i]} as tuples of generator images."""
    A = abelian(invs)
    cands = []
    for i, n in enumerate(invs):
        ok = [v for v in A.els
              if all((n * v[j]) % invs[j] == 0 for j in range(len(invs)))]
        cands.append(ok)
    for imgs in itertools.product(*cands):
        yield imgs


def _apply(invs, imgs, a):
    out = [0] * len(invs)
    for i, c in enumerate(a):
        for j in range(len(invs)):
            out[j] = (out[j] + c * imgs[i][j]) % invs[j]
    return tuple(out)


def abelian_involutions(invs: Sequence[int]):
    """Automorphisms phi of prod C_{invs[i]} with phi^2 = id (id included)."""
    A = abelian(invs)
    out = []
    for imgs in _abelian_endos(invs):
        img = {_apply(invs, imgs, a) for a in A.els}
        if len(img) != A.order:
            continue
        if all(_apply(invs, imgs, _apply(invs, imgs, a)) == a for a in A.els):
            out.append(imgs)
    return out


def abelian_semidirect_2group(invs: Sequence[int], phis: Sequence,
                              name: Optional[str] = None) -> Grp:
    """A |x| C_2^k where the i-th C_2 acts by the involution phis[i]."""
    A = abelian(invs)
    k = len(phis)
    els = [(a, t) for a in A.els
           for t in itertools.product(*[(0, 1)] * k)]

    def act(t, a):
        for i in range(k):
            if t[i]:
                a = _apply(invs, phis[i], a)
        return a

    def mul(p, q):
        a, t = p
        b, u = q
        return (A.mul(a, act(t, b)), tuple((t[i] + u[i]) % 2 for i in range(k)))

    G = Grp(name or f"({A.name}):C2^{k}", els, mul)
    return G


def semidirect_cyclic(invs: Sequence[int], imgs, k: int,
                      name: Optional[str] = None) -> Grp:
    """A |x| C_k where the generator of C_k acts by the automorphism imgs."""
    A = abelian(invs)
    els = [(a, j) for a in A.els for j in range(k)]

    def actj(j, a):
        for _ in range(j):
            a = _apply(invs, imgs, a)
        return a

    def mul(p, q):
        a, i = p
        b, j = q
        return (A.mul(a, actj(i, b)), (i + j) % k)

    return Grp(name or f"({A.name}):C{k}", els, mul)


def quotient(G: Grp, N: FrozenSet, name: Optional[str] = None) -> Grp:
    assert G.is_normal(N)
    cos = []
    seen = set()
    for g in G.els:
        c = frozenset(G.mul(g, n) for n in N)
        if c not in seen:
            seen.add(c)
            cos.append(c)
    rep = {c: next(iter(c)) for c in cos}
    index = {}
    for c in cos:
        for x in c:
            index[x] = c

    def mul(c, d):
        return index[G.mul(rep[c], rep[d])]

    return Grp(name or f"{G.name}/N", cos, mul)


def perm_closure(gens: Sequence[Tuple[int, ...]], name: str) -> Grp:
    def comp(p, q):
        return tuple(q[p[i]] for i in range(len(p)))

    n = len(gens[0])
    ident = tuple(range(n))
    els = {ident}
    frontier = [ident]
    while frontier:
        x = frontier.pop()
        for g in gens:
            y = comp(x, g)
            if y not in els:
                els.add(y)
                frontier.append(y)
    return Grp(name, sorted(els), comp)


def heisenberg(p: int) -> Grp:
    """Extraspecial group of order p^3 and exponent p (unipotent 3x3 over F_p)."""
    els = [(a, b, c) for a in range(p) for b in range(p) for c in range(p)]

    def mul(x, y):
        return ((x[0] + y[0]) % p, (x[1] + y[1]) % p,
                (x[2] + y[2] + x[0] * y[1]) % p)

    return Grp(f"Heis({p})", els, mul)


def sl23() -> Grp:
    def mul(p, q):
        (a, b, c, d), (e, f, g, h) = p, q
        return ((a * e + b * g) % 3, (a * f + b * h) % 3,
                (c * e + d * g) % 3, (c * f + d * h) % 3)

    gens = [(1, 1, 0, 1), (0, 2, 1, 0)]
    els = {(1, 0, 0, 1)}
    frontier = [(1, 0, 0, 1)]
    while frontier:
        x = frontier.pop()
        for g in gens:
            y = mul(x, g)
            if y not in els:
                els.add(y)
                frontier.append(y)
    return Grp("SL(2,3)", sorted(els), mul)


# --------------------------------------------------------------- isomorphism

def isomorphic(G: Grp, H: Grp) -> bool:
    if G.invariants() != H.invariants():
        return False
    gens = G.generating_set()
    words = G.words(gens)
    orders = [G.order_of(g) for g in gens]
    buckets = [[h for h in H.els if H.order_of(h) == o] for o in orders]
    for imgs in itertools.product(*buckets):
        def f(x):
            y = H.e
            for i in words[x]:
                y = H.mul(y, imgs[i])
            return y

        vals = {x: f(x) for x in G.els}
        if len({*vals.values()}) != G.order:
            continue
        if all(vals[G.mul(x, y)] == H.mul(vals[x], vals[y])
               for x in G.els for y in G.els):
            return True
    return False


def embeds(G: Grp, H: Grp) -> bool:
    """Is there an injective homomorphism G -> H?"""
    if H.order % G.order:
        return False
    gens = G.generating_set()
    words = G.words(gens)
    orders = [G.order_of(g) for g in gens]
    buckets = [[h for h in H.els if H.order_of(h) == o] for o in orders]
    if any(not b for b in buckets):
        return False
    for imgs in itertools.product(*buckets):
        def f(x):
            y = H.e
            for i in words[x]:
                y = H.mul(y, imgs[i])
            return y

        vals = {x: f(x) for x in G.els}
        if len({*vals.values()}) != G.order:
            continue
        if all(vals[G.mul(x, y)] == H.mul(vals[x], vals[y])
               for x in G.els for y in G.els):
            return True
    return False


# ------------------------------------------------------------------ coverage

def pst_necessary_criterion(G: Grp):
    """Exact test of the necessary condition of PST-DIV-CRIT-01.

    Lemma.  If G divides A |x| E with A abelian and E elementary abelian 2,
    then G has an abelian normal subgroup B with G/B elementary abelian 2.

    Proof.  Let G = K/N with K <= A |x| E and N normal in K.  Put B0 = K cap A;
    it is abelian and normal in K, and K/B0 embeds into E, so it is elementary
    abelian 2.  Then B = B0 N / N is abelian (a quotient of B0), normal in K/N,
    and (K/N)/B is a quotient of K/B0, hence elementary abelian 2.  QED

    Returns a witness B, or None when the criterion fails (which *proves* that
    G is not a divisor of any such semidirect product, for any size of A and E).
    """
    for B in G.all_subgroups():
        if not G.abelian_subset(B) or not G.is_normal(B):
            continue
        # G/B elementary abelian 2  <=>  x^2 in B and [x,y] in B for all x, y
        if all(G.mul(x, x) in B for x in G.els) and \
           all(G.commutator(x, y) in B for x in G.els for y in G.els):
            return B
    return None


def pst_direct_decomposition(G: Grp):
    """Find abelian normal A and elementary abelian 2-subgroup E with G = A |x| E."""
    subs = G.all_subgroups()
    normals = [S for S in subs if G.abelian_subset(S) and G.is_normal(S)]
    twos = [S for S in subs if G.elem_abelian_2(S)]
    for A in sorted(normals, key=len, reverse=True):
        for E in twos:
            if len(A) * len(E) != G.order:
                continue
            if len(A & E) != 1:
                continue
            prod = {G.mul(a, x) for a in A for x in E}
            if len(prod) == G.order:
                return A, E
    return None


def abelian_invariant_lists(maxorder: int, maxfactors: int = 3):
    """Invariant-factor lists (n1 | n2 | ...) with product <= maxorder."""
    out = []

    def rec(prefix, prod):
        if prefix:
            out.append(tuple(prefix))
        start = prefix[-1] if prefix else 2
        for n in range(start, maxorder + 1):
            if prefix and n % prefix[-1]:
                continue
            if prod * n > maxorder or len(prefix) + 1 > maxfactors:
                continue
            rec(prefix + [n], prod * n)

    rec([], 1)
    return out


_HOST_CACHE: Dict[Tuple[int, int], List[Grp]] = {}


def pst_hosts(maxorder: int, maxrank: int = 2):
    """Groups A |x| C_2^k with A abelian, k <= maxrank, order <= maxorder."""
    key = (maxorder, maxrank)
    if key in _HOST_CACHE:
        return _HOST_CACHE[key]
    hosts = []
    for invs in abelian_invariant_lists(maxorder // 2):
        base = math.prod(invs)
        if base * 2 > maxorder:
            continue
        invols = abelian_involutions(invs)
        for k in range(1, maxrank + 1):
            if base * 2 ** k > maxorder:
                continue
            for phis in itertools.combinations_with_replacement(invols, k):
                # the action must be a homomorphism C_2^k -> Aut(A):
                # the chosen involutions must pairwise commute.
                ok = True
                A = abelian(invs)
                for p, q in itertools.combinations(phis, 2):
                    for a in A.els:
                        if _apply(invs, p, _apply(invs, q, a)) != \
                           _apply(invs, q, _apply(invs, p, a)):
                            ok = False
                            break
                    if not ok:
                        break
                if not ok:
                    continue
                nm = ("x".join(f"C{n}" for n in invs)
                      + f") x| C2^{k}")
                hosts.append(abelian_semidirect_2group(invs, phis, "(" + nm))
    hosts.sort(key=lambda H: H.order)
    _HOST_CACHE[key] = hosts
    return hosts


def dicyclic_host(n: int) -> Grp:
    """H_n = (C_2 x C_2n) x| C_2 with u |-> u v^n, v |-> v^{-1}.

    Writing A = <u> x <v> with |u| = 2, |v| = 2n, the map phi(u) = u v^n,
    phi(v) = v^{-1} is an automorphism of A with phi^2 = id, so H_n is a
    semidirect product of an abelian group by C_2: it lies in the PST-GRP-03
    class.  See dicyclic_embedding for the point of this particular action.
    """
    return abelian_semidirect_2group(
        (2, 2 * n), [((1, n % (2 * n)), (0, (2 * n - 1) % (2 * n)))],
        f"(C2xC{2 * n}) x| C2")


def dicyclic_embedding(n: int) -> bool:
    """Certify Dic_n <= H_n via x |-> v, y |-> u t (DICM-EMB-01).

    Dic_n = <x, y | x^{2n} = 1, y^2 = x^n, y^{-1} x y = x^{-1}>.  In H_n put
    x |-> v and y |-> u t.  Then
        (u t)^2 = u phi(u) = u . u v^n = v^n,      so y^2 |-> x^n,
        (u t)^{-1} v (u t) = phi(v) = v^{-1},      so y^{-1} x y |-> x^{-1},
    and the 4n elements v^i, v^i u t are pairwise distinct in H_n, so the
    induced homomorphism is injective.  This function checks all of that
    mechanically on the constructed groups.
    """
    G = dicyclic(n)
    H = dicyclic_host(n)
    x_img = ((0, 1), (0,))          # v
    y_img = ((1, 0), (1,))          # u t
    gens = [(1, 0), (0, 1)]         # x, y in the dicyclic coordinates
    assert G.order_of(gens[0]) == 2 * n and G.order_of(gens[1]) == 4
    words = G.words(gens)
    imgs = [x_img, y_img]

    def f(g):
        y = H.e
        for i in words[g]:
            y = H.mul(y, imgs[i])
        return y

    vals = {g: f(g) for g in G.els}
    if len(set(vals.values())) != G.order:
        return False
    return all(vals[G.mul(p, q)] == H.mul(vals[p], vals[q])
               for p in G.els for q in G.els)


def divisor_search(G: Grp, maxorder: int, maxrank: int = 2):
    """Bounded search for an embedding of G into some A |x| C_2^k."""
    tried = 0
    for H in pst_hosts(maxorder, maxrank):
        if H.order % G.order:
            continue
        tried += 1
        if embeds(G, H):
            return H, tried
    return None, tried


# ------------------------------------------------------------------- catalogue

def catalogue() -> List[Tuple[int, str, Grp]]:
    C2, C3, C4 = cyclic(2), cyclic(3), cyclic(4)
    D4 = metacyclic(4, 2, 3, "D_4")
    Q8 = dicyclic(2)
    S3 = metacyclic(3, 2, 2, "S_3")
    A4 = perm_closure([(1, 2, 0, 3), (1, 0, 3, 2)], "A_4")
    S4 = perm_closure([(1, 2, 3, 0), (1, 0, 2, 3)], "S_4")
    Dic3 = dicyclic(3)
    swap22 = ((0, 1), (1, 0))          # automorphism of C2 x C2: swap
    inv33 = ((2, 0), (0, 2))           # inversion on C3 x C3
    c4_on_v4 = swap22
    # (C_6 x C_2) |x| C_2 : invert C_3, swap the two C_2 factors
    a24_8 = abelian_semidirect_2group((3, 2, 2), [((2, 0, 0), (0, 0, 1),
                                                   (0, 1, 0))],
                                      "(C6xC2):C2")
    pauli = quotient(direct(C4, D4),
                     frozenset({(0, (0, 0)), (2, (2, 0))}),
                     "C4oD4 (central product)")
    out: List[Tuple[int, str, Grp]] = [
        (6, "S_3 = D_3 = C_3 x| C_2", S3),
        (8, "D_4", D4),
        (8, "Q_8", Q8),
        (10, "D_5 = C_5 x| C_2", metacyclic(5, 2, 4, "D_5")),
        (12, "D_6 = C_6 x| C_2", metacyclic(6, 2, 5, "D_6")),
        (12, "Dic_3 = C_3 x| C_4", Dic3),
        (12, "A_4", A4),
        (14, "D_7", metacyclic(7, 2, 6, "D_7")),
        (16, "D_8 (order 16)", metacyclic(8, 2, 7, "D_8")),
        (16, "SD_16 (semidihedral)", metacyclic(8, 2, 3, "SD_16")),
        (16, "M_4(2) = C_8 x|_5 C_2 (modular)", metacyclic(8, 2, 5, "M_16")),
        (16, "Q_16", dicyclic(4)),
        (16, "D_4 x C_2", direct(D4, C2, "D_4xC_2")),
        (16, "Q_8 x C_2", direct(Q8, C2, "Q_8xC_2")),
        (16, "C_4 x| C_4", metacyclic(4, 4, 3, "C4:C4")),
        (16, "(C_2 x C_2) x| C_4",
         semidirect_cyclic((2, 2), c4_on_v4, 4, "(C2xC2):C4")),
        (16, "C_4 o D_4 (central product)", pauli),
        (18, "D_9", metacyclic(9, 2, 8, "D_9")),
        (18, "C_3 x S_3", direct(C3, S3, "C_3xS_3")),
        (18, "(C_3 x C_3) x| C_2 (generalized dihedral)",
         abelian_semidirect_2group((3, 3), [inv33], "(C3xC3):C2")),
        (20, "D_10", metacyclic(10, 2, 9, "D_10")),
        (20, "Dic_5 = C_5 x| C_4", dicyclic(5)),
        (20, "F_20 = C_5 x| C_4 (faithful)", metacyclic(5, 4, 2, "F_20")),
        (21, "C_7 x| C_3", metacyclic(7, 3, 2, "C7:C3")),
        (22, "D_11", metacyclic(11, 2, 10, "D_11")),
        (24, "C_3 x| C_8", metacyclic(3, 8, 2, "C3:C8")),
        (24, "SL(2,3)", sl23()),
        (24, "Dic_6 = C_3 x| Q_8", dicyclic(6)),
        (24, "C_4 x S_3", direct(C4, S3, "C_4xS_3")),
        (24, "D_12 (order 24)", metacyclic(12, 2, 11, "D_12")),
        (24, "C_2 x Dic_3", direct(C2, Dic3, "C_2xDic_3")),
        (24, "(C_6 x C_2) x| C_2", a24_8),
        (24, "C_3 x D_4", direct(C3, D4, "C_3xD_4")),
        (24, "C_3 x Q_8", direct(C3, Q8, "C_3xQ_8")),
        (24, "S_4", S4),
        (24, "C_2 x A_4", direct(C2, A4, "C_2xA_4")),
        (24, "C_2 x C_2 x S_3", direct(direct(C2, C2), S3, "C_2xC_2xS_3")),
        (26, "D_13", metacyclic(13, 2, 12, "D_13")),
        (27, "Heisenberg over F_3 (exponent 3)", heisenberg(3)),
        (27, "C_9 x| C_3", metacyclic(9, 3, 4, "C9:C3")),
        (28, "D_14", metacyclic(14, 2, 13, "D_14")),
        (28, "Dic_7 = C_7 x| C_4", dicyclic(7)),
        (30, "D_15", metacyclic(15, 2, 14, "D_15")),
        (30, "C_5 x S_3", direct(cyclic(5), S3, "C_5xS_3")),
        (30, "C_3 x D_5", direct(C3, metacyclic(5, 2, 4, "D_5"), "C_3xD_5")),
    ]
    return out


def is_solvable(G: Grp) -> bool:
    cur = frozenset(G.els)
    while len(cur) > 1:
        nxt = G.closure(G.commutator(x, y) for x in cur for y in cur)
        nxt = frozenset(z for z in nxt)
        if nxt == cur:
            return False
        cur = nxt
    return True


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-order", type=int, default=31)
    ap.add_argument("--host-order", type=int, default=96,
                    help="bound on |A x| C_2^k| in the divisor search")
    ap.add_argument("--host-rank", type=int, default=2,
                    help="bound on k in the divisor search")
    args = ap.parse_args()

    cat = [(n, label, G) for (n, label, G) in catalogue()
           if n <= args.max_order]

    print("[1] validating constructions (closure, associativity, "
          "identity, inverses)")
    for n, label, G in cat:
        G.validate()
        assert G.order == n, f"{label}: order {G.order} != {n}"
        assert not G.is_abelian(), f"{label}: abelian"
    print(f"    {len(cat)} groups validated, all non-abelian, orders correct")

    print("[2] completeness cross-check against the classification counts")
    for n in sorted({n for n, _, _ in cat}):
        fam = [(label, G) for (m, label, G) in cat if m == n]
        for (l1, G1), (l2, G2) in itertools.combinations(fam, 2):
            assert not isomorphic(G1, G2), f"{l1} == {l2}"
        want = NONABELIAN_COUNTS[n]
        flag = "OK" if len(fam) == want else "MISMATCH"
        print(f"    order {n:2d}: {len(fam):2d} pairwise non-isomorphic, "
              f"classification says {want:2d}  [{flag}]")
        assert len(fam) == want, f"order {n}: incomplete list"

    print("[3] coverage by the audited height-one theorems")
    rows = []
    for n, label, G in cat:
        cls = G.nilpotency_class()
        if cls is not None and cls <= 2:
            rows.append((n, label, "PST-GRP-02",
                         f"nilpotent of class {cls}"))
            continue
        dec = pst_direct_decomposition(G)
        if dec is not None:
            A, E = dec
            k = len(E).bit_length() - 1
            rows.append((n, label, "PST-GRP-03",
                         f"G = A x| E with |A| = {len(A)} abelian normal, "
                         f"E = C_2^{k}"))
            continue
        if pst_necessary_criterion(G) is None:
            rows.append((n, label, "NOT IN PST CLASS",
                         "no abelian normal B with G/B elementary abelian 2, "
                         "so G divides no A x| E at all (PST-DIV-CRIT-01); "
                         f"nilpotency class "
                         f"{'non-nilpotent' if cls is None else cls}"))
            continue
        H, tried = divisor_search(G, args.host_order, args.host_rank)
        if H is not None:
            rows.append((n, label, "PST-GRP-03 (divisor)",
                         f"embeds into {H.name} of order {H.order}"))
        else:
            rows.append((n, label, "NOT FOUND",
                         f"passes the necessary criterion but no embedding "
                         f"into any A x| C_2^k with order <= "
                         f"{args.host_order}, rank <= {args.host_rank} "
                         f"({tried} hosts tested)"))
    width = max(len(l) for _, l, _, _ in rows)
    for n, label, why, detail in rows:
        print(f"    {n:2d}  {label:<{width}}  {why:<21}  {detail}")

    print("[4] summary")
    outside = [(n, label) for n, label, why, _ in rows
               if why == "NOT IN PST CLASS"]
    unknown = [(n, label) for n, label, why, _ in rows if why == "NOT FOUND"]
    by_label = {label: G for _, label, G in cat}
    if outside:
        print(f"    {len(outside)} group(s) provably outside the PST-GRP-03 "
              f"class (exact, PST-DIV-CRIT-01):")
        for n, label in outside:
            solv = "solvable" if is_solvable(by_label[label]) else "non-solvable"
            print(f"      order {n:2d}: {label}  ({solv})")
    if unknown:
        print("    inconclusive (criterion passed, no embedding found in the "
              "searched family):")
        for n, label in unknown:
            print(f"      order {n:2d}: {label}")
    print("    Outside the PST class is NOT a star-height lower bound: it only "
          "says these groups need a new mechanism.")
    print("    Not audited here: PST 1992's wreath-product / pseudovariety "
          "results (docs/SURVEY.md §3 item 6).")

    print("[5] the uniform dicyclic embedding (DICM-EMB-01, generalizing "
          "DIC3-RED-01)")
    for k in range(2, 13):
        H = dicyclic_host(k)
        ok = dicyclic_embedding(k)
        print(f"    Dic_{k:2d} (order {4 * k:3d})  x |-> v, y |-> u t  into  "
              f"(C_2 x C_{2 * k}) x| C_2 (order {H.order:3d}):  {ok}")
        assert ok, f"Dic_{k} embedding failed"
    print("    => every dicyclic group Dic_n (n >= 2), in particular every "
          "generalized quaternion group Q_{2^k},")
    print("       lies in the PST-GRP-03 class; the witness is the fixed "
          "formula above, checked for n = 2..12")

    print("[6] consistency with Bourne 2017 (SMALL-12-01, docs/SURVEY.md §5)")
    small = [(n, label) for n, label, why, _ in rows
             if n < 12 and why in ("NOT IN PST CLASS", "NOT FOUND")]
    print(f"    every non-abelian group of order < 12 covered: "
          f"{not small} (Bourne: yes)")
    assert not small
    twelve = {label: why for n, label, why, _ in rows if n == 12}
    a4 = [w for l, w in twelve.items() if l == "A_4"][0]
    dic3 = [w for l, w in twelve.items() if l.startswith("Dic_3")][0]
    print(f"    A_4 outside the PST class: {a4 == 'NOT IN PST CLASS'} "
          f"(Bourne: left open)")
    print(f"    Dic_3 inside via a divisor embedding: "
          f"{dic3.startswith('PST-GRP-03')} (Bourne: left open; "
          f"DIC3-RED-01 closes it)")
    assert a4 == "NOT IN PST CLASS" and dic3.startswith("PST-GRP-03")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
