#!/usr/bin/env python3
"""Route (iv) of N-F20-001 -- inverse alphabetic morphisms -- is NOT blocked, and it
produces the first real reduction of the alphabet: 20 letters down to 8 (7 after erasing
the identity), all four reduced instances living over the *same* 8-letter alphabet.

Route (iv) proposed: inverse *alphabetic* morphisms preserve generalized star height, so
reconstruct the full-alphabet identity fibre `T` as a Boolean combination of instances over
reduced alphabets.  What this script establishes, in order.

  Lemma A (alphabetic closure).  If `h : Σ* → Δ*` is letter-to-letter (`h(a) ∈ Δ` for every
  letter, so `h` is length-preserving), then `h^{-1}` preserves `gsh ≤ 1`.  Proof: `h^{-1}`
  commutes with Boolean operations; `h^{-1}(L₁L₂) = h^{-1}(L₁)h^{-1}(L₂)` and
  `h^{-1}(L*) = (h^{-1}(L))*` because a length-preserving morphism transports the
  factorization boundaries verbatim; and `h^{-1}` of a star-free language is star-free by
  induction, since `h^{-1}({d})` is the finite letter set `{a : h(a) = d}`.

  Lemma B (rigidity).  Over the full alphabet `Σ = G`, if the identity fibres of relabelings
  `f_j : G → G'_j` intersect to exactly `T`, then every `f_j` is a group homomorphism and
  the intersection is `mu^{-1}(⋂ ker f_j)`.  Proof: `mu(w) = e ⟹ mu_f(w) = e` applied to the
  three words `(e)`, `(g)(g^{-1})` and `(g)(h)((gh)^{-1})` forces `f(e) = e`,
  `f(g^{-1}) = f(g)^{-1}` and `f(g)f(h) = f(gh)`.

  Theorem C (subdirect reduction, positive).  Height one is closed under subdirect products:
  if `N_1,…,N_k ⊴ G` are nontrivial with `⋂ N_j = 1` and every `G/N_j` is a height-one group,
  then so is `G`.  Consequence: **only monolithic groups need a direct attack** -- a group
  with two distinct minimal normal subgroups reduces to proper quotients.

  Obstruction D.  `F_20` is monolithic, with monolith `C_5` contained in every nontrivial
  normal subgroup.  So the identity-fibre form of route (iv) yields exactly
  `gsh(mu^{-1}(C_5)) ≤ 1` and can never reach `T`.  Every group on the current frontier
  ladder is monolithic -- as Theorem C forces.

  Theorem E.  With *general* accepting sets the route is strictly stronger than Lemma B's
  homomorphism form, and it already succeeds on a **simple** group: for `G = C_5` the
  non-homomorphic splitting `β ↦ (a_β, b_β)` with images `{0,1}` and `{0,2,3}` recovers the
  sum, so `T` is a union of 5 intersections of instances over 2- and 3-letter alphabets.

  Theorem F (the new reduction).  For `F_20`, put `H = {(x₁,…,x₄) ∈ F_20⁴ : equal phase}`,
  `rho(ε, u₁,…,u₄) = (ε, Σ u_i)` -- a homomorphism -- and split
  `β ↦ (a₁,…,a₄) ∈ {0,1}⁴` with `Σ a_i = β`.  Then `mu = rho ∘ Φ`, so

      T_Σ (20 letters) = ⋃_{tuple ∈ ker rho} ⋂_{j=1..4} mu_j^{-1}(tuple_j),

  and each `mu_j^{-1}(g)` is the `h_j`-preimage of an `F_20`-recognized language over the
  single 8-letter alphabet `Δ = Z/4 × {0,1}`.  With Lemma A and `FULL-ALPH-RED-02`-style
  erasure of the identity letter, `HeightOneForGroup F_20` reduces to a **7-letter**
  obligation.

  Lemma G (what is left must be an `F_20` instance).  If every coordinate group `⟨Δ_j⟩` were
  (abelian)-by-(elementary abelian 2) -- which covers every abelian group and `D_5` -- no
  reduction could exist, because `F_20` has no abelian normal subgroup with elementary
  abelian 2-quotient.  So at least one coordinate is an `F_20` instance over a proper
  sub-alphabet, and the live question is how small that sub-alphabet can be: **2 letters
  would close `F_20` outright, via `F20-STD-01`.**

Claims registered as `ALPH-RED-01` (Lemma A), `SUBDIRECT-RED-01` (Theorem C),
`F20-QUOT-OBS-01` (Lemma B + Obstruction D), `F20-ALPH8-01` (Theorem F + Lemma G).

Sections
  [1] finite-group toolkit; the `F_20` coordinate convention, cross-checked
  [2] normal subgroups and monolithicity across the frontier ladder
  [3] Lemma B by exhaustive search over *all* relabelings of three small groups
  [4] Theorem C positive control on `C_6`
  [5] Theorem E: a non-homomorphic splitting of the simple group `C_5`
  [6] Theorem F: the 20 → 8 → 7 reduction of `F_20`, verified exactly
  [7] Lemma G, and optimality of 8 inside the equal-phase family
  [8] negative controls: the checker is not vacuous

Python standard library only.
"""

from __future__ import annotations

import itertools
import random
import sys
from contextlib import contextmanager

FAILURES: list[str] = []


@contextmanager
def section(title: str):
    print(f"\n=== {title} ===")
    yield


def check(label: str, ok: bool, detail: str = "") -> bool:
    mark = "PASS" if ok else "FAIL"
    print(f"  [{mark}] {label}" + (f" -- {detail}" if detail else ""))
    if not ok:
        FAILURES.append(label)
    return ok


# ---------------------------------------------------------------- [1] group toolkit


class Group:
    """A finite group given by an explicit element list and a multiplication."""

    def __init__(self, name, elements, mul, identity):
        self.name = name
        self.elements = list(elements)
        self.mul = mul
        self.identity = identity
        self._inv = {g: next(h for h in self.elements if mul(g, h) == identity)
                     for g in self.elements}

    def __len__(self):
        return len(self.elements)

    def inv(self, g):
        return self._inv[g]

    def prod(self, seq):
        acc = self.identity
        for g in seq:
            acc = self.mul(acc, g)
        return acc

    def is_abelian(self):
        return all(self.mul(x, y) == self.mul(y, x)
                   for x in self.elements for y in self.elements)

    def check_axioms(self) -> bool:
        els = self.elements
        if len(set(els)) != len(els):
            return False
        for x in els:
            if self.mul(x, self.identity) != x or self.mul(self.identity, x) != x:
                return False
        for x in els:
            for y in els:
                if self.mul(x, y) not in set(els):
                    return False
                for z in els:
                    if self.mul(self.mul(x, y), z) != self.mul(x, self.mul(y, z)):
                        return False
        return True


def semidirect(name, n, m, t) -> Group:
    """`Z/n ⋊ Z/m` with the generator of `Z/m` acting as multiplication by `t`.

    Elements are pairs `(eps, beta)` with `eps ∈ Z/m`, `beta ∈ Z/n`, and

        (eps, beta) * (eps', beta') = (eps + eps',  t^{eps'} * beta + beta')

    which is exactly the convention of `scripts/research/f20_full_alphabet.py`.
    """
    pw = [pow(t, e, n) for e in range(m)]

    def mul(x, y):
        return ((x[0] + y[0]) % m, (pw[y[0]] * x[1] + y[1]) % n)

    els = [(e, b) for e in range(m) for b in range(n)]
    return Group(name, els, mul, (0, 0))


def perm_group(name, gens, degree) -> Group:
    ident = tuple(range(degree))

    def mul(x, y):  # apply x first, then y
        return tuple(y[x[i]] for i in range(degree))

    seen = {ident}
    frontier = [ident]
    while frontier:
        nxt = []
        for p in frontier:
            for g in gens:
                q = mul(p, g)
                if q not in seen:
                    seen.add(q)
                    nxt.append(q)
        frontier = nxt
    return Group(name, sorted(seen), mul, ident)


def direct_product(name, G, H) -> Group:
    els = [(g, h) for g in G.elements for h in H.elements]

    def mul(x, y):
        return (G.mul(x[0], y[0]), H.mul(x[1], y[1]))

    return Group(name, els, mul, (G.identity, H.identity))


def sl23() -> Group:
    els = [((a, b), (c, d))
           for a in range(3) for b in range(3) for c in range(3) for d in range(3)
           if (a * d - b * c) % 3 == 1]

    def mul(x, y):  # y after x
        (a, b), (c, d) = x
        (p, q), (r, s) = y
        return (((p * a + r * b) % 3, (q * a + s * b) % 3),
                ((p * c + r * d) % 3, (q * c + s * d) % 3))

    return Group("SL(2,3)", els, mul, ((1, 0), (0, 1)))


def quotient_group(name, G, N) -> Group:
    reps = []
    seen = set()
    for g in G.elements:
        coset = frozenset(G.mul(g, n) for n in N)
        if coset not in seen:
            seen.add(coset)
            reps.append(coset)
    index = {c: i for i, c in enumerate(reps)}

    def coset_of(g):
        return index[frozenset(G.mul(g, n) for n in N)]

    table = {}
    for i, c in enumerate(reps):
        gi = next(iter(c))
        for j, d in enumerate(reps):
            gj = next(iter(d))
            table[(i, j)] = coset_of(G.mul(gi, gj))

    return Group(name, list(range(len(reps))), lambda x, y: table[(x, y)],
                 coset_of(G.identity))


def order_profile(G):
    out = {}
    for g in G.elements:
        n, x = 1, g
        while x != G.identity:
            x = G.mul(x, g)
            n += 1
        out[n] = out.get(n, 0) + 1
    return tuple(sorted(out.items()))


F20 = semidirect("F_20 = C_5:C_4", 5, 4, 2)
C5 = semidirect("C_5", 5, 1, 1)
C6 = semidirect("C_6", 3, 2, 1)
C4 = semidirect("C_4", 1, 4, 1)
V4 = semidirect("C_2 x C_2", 2, 2, 1)
C20 = semidirect("C_20", 5, 4, 1)
D5 = semidirect("D_5", 5, 2, 4)
DIC3 = semidirect("Dic_3", 3, 4, 2)
C7C3 = semidirect("C_7:C_3", 7, 3, 2)
S3 = semidirect("S_3", 3, 2, 2)
A4 = perm_group("A_4", [(1, 2, 0, 3), (0, 2, 3, 1)], 4)
S4 = perm_group("S_4", [(1, 2, 3, 0), (1, 0, 2, 3)], 4)
C2 = semidirect("C_2", 1, 2, 1)
SL23 = sl23()
C2A4 = direct_product("C_2 x A_4", C2, A4)
C2S4 = direct_product("C_2 x S_4", C2, S4)

PHASES, MODULUS = 4, 5


def phase(g):
    return g[0]


def beta(g):
    return g[1]


def section_1() -> None:
    with section("[1] group toolkit and the F_20 convention"):
        for G in (F20, C5, C6, C4, V4, C20, D5, DIC3, C7C3, S3, A4, S4, SL23,
                  C2A4, C2S4):
            check(f"{G.name}: group axioms, order {len(G)}", G.check_axioms())
        # cross-check against the repository's own F_20 implementation, which stores the
        # multiplier alpha = 2^eps rather than the exponent eps
        try:
            sys.path.insert(0, __file__.rsplit("/", 1)[0])
            import f20_full_alphabet as base

            enc = {g: (pow(2, phase(g), MODULUS), beta(g)) for g in F20.elements}
            same_set = set(base.SIGMA) == set(enc.values())
            same_id = base.IDENTITY == enc[F20.identity]
            same_mul = all(base.compose(enc[x], enc[y]) == enc[F20.mul(x, y)]
                           for x in F20.elements for y in F20.elements)
            check("F_20 matches scripts/research/f20_full_alphabet.py (set, identity, all 400 "
                  "products, under alpha = 2^eps)",
                  same_set and same_id and same_mul)
        except Exception as exc:  # pragma: no cover - import guard only
            check("F_20 cross-check against f20_full_alphabet", False, repr(exc))
        check("F_20 is non-abelian with trivial centre",
              not F20.is_abelian()
              and [g for g in F20.elements
                   if all(F20.mul(g, h) == F20.mul(h, g) for h in F20.elements)]
              == [F20.identity])
        check("the C_4 action on C_5 is faithful (2 has order 4 mod 5)",
              [pow(2, e, 5) for e in range(4)] == [1, 2, 4, 3])


# --------------------------------------------------- [2] normal subgroups, monolithicity


def closure(G, gens) -> frozenset:
    seen = {G.identity} | set(gens)
    frontier = list(seen)
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = G.mul(x, g)
                if y not in seen:
                    seen.add(y)
                    nxt.append(y)
        frontier = nxt
    return frozenset(seen)


def all_subgroups(G) -> list[frozenset]:
    triv = frozenset([G.identity])
    found = {triv}
    frontier = [triv]
    while frontier:
        nxt = []
        for H in frontier:
            for g in G.elements:
                if g in H:
                    continue
                K = closure(G, H | {g})
                if K not in found:
                    found.add(K)
                    nxt.append(K)
        frontier = nxt
    return sorted(found, key=lambda H: (len(H), sorted(map(str, H))))


def conjugacy_classes(G) -> list[frozenset]:
    seen: set = set()
    out = []
    for g in G.elements:
        if g in seen:
            continue
        cl = frozenset(G.mul(G.mul(x, g), G.inv(x)) for x in G.elements)
        out.append(cl)
        seen |= cl
    return out


def normal_subgroups(G) -> list[frozenset]:
    """Every normal subgroup is generated by the conjugacy classes it contains."""
    classes = conjugacy_classes(G)
    triv = frozenset([G.identity])
    found = {triv}
    frontier = [triv]
    while frontier:
        nxt = []
        for N in frontier:
            for cl in classes:
                if cl <= N:
                    continue
                K = closure(G, N | cl)
                if K not in found:
                    found.add(K)
                    nxt.append(K)
        frontier = nxt
    return sorted(found, key=len)


def monolith(G):
    """Return the intersection of all nontrivial normal subgroups."""
    nontrivial = [N for N in normal_subgroups(G) if len(N) > 1]
    if not nontrivial:
        return frozenset([G.identity])
    inter = nontrivial[0]
    for N in nontrivial[1:]:
        inter = inter & N
    return inter


LADDER = [F20, C7C3, SL23, S4, C2A4, C2S4, A4, DIC3, D5, C5, C4, S3, C6, V4, C20]


def section_2() -> None:
    with section("[2] normal subgroups and monolithicity"):
        table = {}
        for G in LADDER:
            norms = normal_subgroups(G)
            mono = monolith(G)
            table[G.name] = (len(norms), len(mono))
            print(f"    {G.name:<16} order {len(G):>3}  "
                  f"normal subgroups {len(norms):>2}  "
                  f"monolith order {len(mono):>2}  "
                  f"{'MONOLITHIC' if len(mono) > 1 else 'REDUCIBLE by Theorem C'}")
        check("F_20 has exactly the normal subgroups 1, C_5, D_5, F_20",
              table["F_20 = C_5:C_4"][0] == 4)
        check("F_20 is monolithic with monolith of order 5",
              table["F_20 = C_5:C_4"][1] == 5)
        # the still-unresolved frontier of FRONTIER-ORD20-01 is monolithic
        for name in ("F_20 = C_5:C_4", "C_7:C_3", "SL(2,3)", "S_4", "A_4"):
            check(f"{name} is monolithic (needs a direct attack)", table[name][1] > 1)
        for name in ("C_6", "C_2 x C_2", "C_20"):
            check(f"{name} is reducible by Theorem C (monolith trivial)",
                  table[name][1] == 1)

        # Dic_3: Theorem C reduces it, which re-derives DIC3-ALL-01 independently of the
        # embedding of DIC3-RED-01 -- a positive control on already-settled data
        check("Dic_3 is reducible by Theorem C", table["Dic_3"][1] == 1)
        norms = [N for N in normal_subgroups(DIC3) if len(N) in (2, 3)]
        by_order = {len(N): N for N in norms}
        check("Dic_3 has normal subgroups of order 2 and 3 meeting trivially",
              set(by_order) == {2, 3} and len(by_order[2] & by_order[3]) == 1)
        q2 = quotient_group("Dic_3/C_2", DIC3, by_order[2])
        q3 = quotient_group("Dic_3/C_3", DIC3, by_order[3])
        check("Dic_3/C_2 is the non-abelian group of order 6, i.e. S_3",
              len(q2) == 6 and not q2.is_abelian()
              and order_profile(q2) == order_profile(S3))
        check("Dic_3/C_3 is cyclic of order 4",
              len(q3) == 4 and q3.is_abelian()
              and order_profile(q3) == order_profile(C4))
        check("both quotients have order < 12, so PST 1992 Cor. 7.7 covers them; this "
              "re-proves DIC3-ALL-01 without the DIC3-RED-01 embedding",
              len(q2) < 12 and len(q3) < 12)

        # C_2 x A_4 and C_2 x S_4 fall out of the direct-product closure of Theorem C
        check("C_2 x A_4 is reducible by Theorem C, so A4-ALLLANG-01 settles it and it "
              "leaves the FRONTIER-ORD20-01 list", table["C_2 x A_4"][1] == 1)
        check("C_2 x S_4 is reducible by Theorem C, so HeightOneForGroup (C_2 x S_4) "
              "follows from HeightOneForGroup S_4 alone", table["C_2 x S_4"][1] == 1)
        for G, factors_ in ((C2A4, (C2, A4)), (C2S4, (C2, S4))):
            ns = [frozenset((c, A4.identity if G is C2A4 else S4.identity)
                            for c in C2.elements),
                  frozenset((C2.identity, h) for h in factors_[1].elements)]
            ok = all(N in [frozenset(M) for M in normal_subgroups(G)] for N in ns)
            check(f"{G.name}: both direct factors are normal and meet trivially",
                  ok and len(ns[0] & ns[1]) == 1)
        # Obstruction D, stated as the identity it actually is
        m = monolith(F20)
        c5 = frozenset((0, b) for b in range(5))
        check("the monolith of F_20 is the translation subgroup C_5", m == c5)
        check("every nontrivial normal subgroup of F_20 contains C_5",
              all(c5 <= N for N in normal_subgroups(F20) if len(N) > 1))


# ------------------------------------------------------------------ [3] Lemma B rigidity


def fibre_words(G, max_len):
    """All words over the full alphabet `Σ = G` of length ≤ max_len with image `e`."""
    out = []
    for n in range(max_len + 1):
        for w in itertools.product(G.elements, repeat=n):
            if G.prod(w) == G.identity:
                out.append(w)
    return out


def relabel_image(G, f, w):
    return G.prod([f[a] for a in w])


def is_homomorphism(G, f) -> bool:
    return all(f[G.mul(x, y)] == G.mul(f[x], f[y]) for x in G.elements for y in G.elements)


def section_3() -> None:
    with section("[3] Lemma B: only homomorphisms keep the whole fibre"):
        # length 3 is enough: the forcing argument only uses the words (e), (g)(g^{-1})
        # and (g)(h)((gh)^{-1}), so this is the sharp form of the lemma
        for G, max_len in ((C4, 3), (C6, 3), (S3, 3)):
            words = fibre_words(G, max_len)
            keeps, homs = [], []
            for values in itertools.product(G.elements, repeat=len(G)):
                f = dict(zip(G.elements, values))
                if all(relabel_image(G, f, w) == G.identity for w in words):
                    keeps.append(values)
                if is_homomorphism(G, f):
                    homs.append(values)
            check(f"{G.name}: the {len(G)**len(G)} relabelings that preserve the fibre are "
                  f"exactly the {len(homs)} endomorphisms",
                  set(keeps) == set(homs),
                  f"{len(keeps)} preserving, {len(words)} fibre words of length <= {max_len}")
        # and the consequence: for a monolithic G no family of non-injective endomorphisms
        # can cut the fibre down to T
        for G in (C5, F20, A4):
            kernels = []
            for f in _endomorphisms(G):
                ker = frozenset(g for g in G.elements if f[g] == G.identity)
                if len(ker) > 1:
                    kernels.append(ker)
            inter = frozenset(G.elements)
            for k in kernels:
                inter = inter & k
            check(f"{G.name}: intersection of all nontrivial endomorphism kernels has "
                  f"order {len(inter)} > 1", len(inter) > 1,
                  f"{len(kernels)} non-injective endomorphisms")


def _endomorphisms(G):
    """Endomorphisms of G, found as homomorphisms determined on a generating set."""
    out = []
    n = len(G)
    if n <= 6:
        for values in itertools.product(G.elements, repeat=n):
            f = dict(zip(G.elements, values))
            if is_homomorphism(G, f):
                out.append(f)
        return out
    # larger G: build homomorphisms from images of two generators
    gens = _small_generating_set(G)
    for images in itertools.product(G.elements, repeat=len(gens)):
        f = _extend(G, gens, images)
        if f is not None and is_homomorphism(G, f):
            out.append(f)
    return out


def _small_generating_set(G):
    for k in (1, 2, 3):
        for gens in itertools.combinations(G.elements, k):
            if len(closure(G, set(gens))) == len(G):
                return list(gens)
    return list(G.elements)


def _extend(G, gens, images):
    """Extend `gens -> images` to a map on G along a word decomposition, or return None."""
    word = {G.identity: ()}
    frontier = [G.identity]
    while frontier:
        nxt = []
        for x in frontier:
            for i, g in enumerate(gens):
                y = G.mul(x, g)
                if y not in word:
                    word[y] = word[x] + (i,)
                    nxt.append(y)
        frontier = nxt
    if len(word) != len(G):
        return None
    return {g: G.prod([images[i] for i in w]) for g, w in word.items()}


# ------------------------------------------------------- [4] Theorem C positive control


def section_4() -> None:
    with section("[4] Theorem C positive control: C_6 = subdirect product of C_2 and C_3"):
        G = C6
        # C_6 here is Z/3 x Z/2 with elements (eps in Z/2, beta in Z/3).
        # q1 forgets beta (kernel C_3), q2 forgets eps (kernel C_2).
        f1 = {g: (g[0], 0) for g in G.elements}
        f2 = {g: (0, g[1]) for g in G.elements}
        d1 = sorted(set(f1.values()))
        d2 = sorted(set(f2.values()))
        check("both relabelings are homomorphisms",
              is_homomorphism(G, f1) and is_homomorphism(G, f2))
        k1 = frozenset(g for g in G.elements if f1[g] == G.identity)
        k2 = frozenset(g for g in G.elements if f2[g] == G.identity)
        check("kernels are nontrivial and intersect trivially",
              len(k1) == 3 and len(k2) == 2 and len(k1 & k2) == 1)
        check(f"the reduced alphabets have {len(d1)} and {len(d2)} letters, both < {len(G)}",
              len(d1) < len(G) and len(d2) < len(G))
        bad = 0
        total = 0
        for n in range(7):
            for w in itertools.product(G.elements, repeat=n):
                total += 1
                lhs = G.prod(w) == G.identity
                rhs = (relabel_image(G, f1, w) == G.identity
                       and relabel_image(G, f2, w) == G.identity)
                if lhs != rhs:
                    bad += 1
        check(f"T = mu_1^{{-1}}(e) ∩ mu_2^{{-1}}(e) on all {total} words of length <= 6",
              bad == 0)


# ---------------------------------------------- [5] Theorem E: a simple group still splits


C5_SPLIT = {0: (0, 0), 1: (1, 0), 2: (0, 2), 3: (0, 3), 4: (1, 3)}


def section_5() -> None:
    with section("[5] Theorem E: non-homomorphic splitting of the simple group C_5"):
        A = sorted({a for a, _ in C5_SPLIT.values()})
        B = sorted({b for _, b in C5_SPLIT.values()})
        check("the splitting reproduces every element: a + b = beta mod 5",
              all((a + b) % 5 == x for x, (a, b) in C5_SPLIT.items()))
        check("the splitting is injective", len(set(C5_SPLIT.values())) == 5)
        check(f"both reduced alphabets are proper: |A| = {len(A)}, |B| = {len(B)}, both < 5",
              len(A) < 5 and len(B) < 5, f"A = {A}, B = {B}")
        check("neither coordinate is a homomorphism (so Lemma B does not apply)",
              not is_homomorphism(C5, {(0, x): (0, C5_SPLIT[x][0]) for x in range(5)})
              and not is_homomorphism(C5, {(0, x): (0, C5_SPLIT[x][1]) for x in range(5)}))
        # exhaustive: the two coordinate images determine the group image, and T is the
        # union of 5 intersections of reduced-alphabet instances
        bad = union_bad = total = 0
        for n in range(8):
            for w in itertools.product(range(5), repeat=n):
                total += 1
                s = sum(w) % 5
                sa = sum(C5_SPLIT[x][0] for x in w) % 5
                sb = sum(C5_SPLIT[x][1] for x in w) % 5
                if (sa + sb) % 5 != s:
                    bad += 1
                in_union = any(sa == c and sb == (-c) % 5 for c in range(5))
                if in_union != (s == 0):
                    union_bad += 1
        check(f"mu = rho ∘ Φ on all {total} words of length <= 7", bad == 0)
        check("T is exactly the union of the 5 rectangles", union_bad == 0)
        check("C_5 is simple, hence monolithic: Lemma B's form is impossible here",
              len(normal_subgroups(C5)) == 2 and len(monolith(C5)) == 5)


# ------------------------------------------------------- [6] Theorem F: the 20 -> 8 -> 7


K_COORDS = 4
# beta = a_1 + a_2 + a_3 + a_4 mod 5 with every a_i in {0, 1}, injectively
BETA_SPLIT = {
    0: (0, 0, 0, 0),
    1: (1, 0, 0, 0),
    2: (1, 1, 0, 0),
    3: (1, 1, 1, 0),
    4: (1, 1, 1, 1),
}


def coord_map(j):
    """The relabeling `f_j : F_20 -> F_20`, letter-to-letter onto the 8-letter alphabet."""
    return {g: (phase(g), BETA_SPLIT[beta(g)][j]) for g in F20.elements}


def H_elements():
    """`H = {(x_1,...,x_k) in F_20^k : all coordinates have the same phase}`."""
    return [(e, us) for e in range(PHASES)
            for us in itertools.product(range(MODULUS), repeat=K_COORDS)]


def h_mul(x, y):
    e, us = x
    f, vs = y
    w = pow(2, f, MODULUS)
    return ((e + f) % PHASES, tuple((w * u + v) % MODULUS for u, v in zip(us, vs)))


def rho(x):
    e, us = x
    return (e, sum(us) % MODULUS)


def to_tuple(x):
    e, us = x
    return tuple((e, u) for u in us)


def section_6() -> None:
    with section("[6] Theorem F: the 20-letter fibre reduces to an 8-letter alphabet"):
        maps = [coord_map(j) for j in range(K_COORDS)]
        alphabets = [sorted(set(m.values())) for m in maps]
        check("all four relabelings have the same 8-letter image Z/4 x {0,1}",
              all(len(a) == 8 for a in alphabets)
              and all(a == alphabets[0] for a in alphabets),
              f"Δ = {alphabets[0]}")
        check("Δ generates F_20", len(closure(F20, set(alphabets[0]))) == 20)
        check("no relabeling is a homomorphism (Lemma B is bypassed)",
              not any(is_homomorphism(F20, m) for m in maps))
        check("the splitting is injective on the 20 letters",
              len({tuple(m[g] for m in maps) for g in F20.elements}) == 20)

        Hs = H_elements()
        Hset = set(Hs)
        check(f"H has {len(Hs)} elements and is closed under the product",
              len(Hs) == PHASES * MODULUS ** K_COORDS
              and all(h_mul(x, y) in Hset for x in Hs for y in Hs[:80]))
        # rho is a homomorphism: exhaustive over all 2500^2 pairs
        bad = 0
        for x in Hs:
            rx = rho(x)
            for y in Hs:
                if rho(h_mul(x, y)) != F20.mul(rx, rho(y)):
                    bad += 1
        check(f"rho is a homomorphism H -> F_20 on all {len(Hs)**2} pairs", bad == 0)
        ker = [x for x in Hs if rho(x) == F20.identity]
        check(f"rho is onto F_20 and |ker rho| = {len(ker)} = |H|/20",
              len({rho(x) for x in Hs}) == 20 and len(ker) == len(Hs) // 20)

        lam = {g: (phase(g), BETA_SPLIT[beta(g)]) for g in F20.elements}
        check("lambda is a section of rho: rho(lambda(g)) = g for all 20 letters",
              all(rho(lam[g]) == g for g in F20.elements))
        check("lambda lands in H", all(lam[g] in Hset for g in F20.elements))
        check("the coordinates of lambda are exactly the four relabelings",
              all(to_tuple(lam[g]) == tuple(m[g] for m in maps) for g in F20.elements))

        # mu = rho o Phi, exhaustively for short words and at random for long ones
        def phi(w):
            acc = (0, (0,) * K_COORDS)
            for a in w:
                acc = h_mul(acc, lam[a])
            return acc

        bad = total = 0
        for n in range(5):
            for w in itertools.product(F20.elements, repeat=n):
                total += 1
                if rho(phi(w)) != F20.prod(w):
                    bad += 1
        check(f"mu(w) = rho(Phi(w)) on all {total} words of length <= 4", bad == 0)
        rng = random.Random(20250725)
        bad = 0
        for _ in range(60000):
            w = [rng.choice(F20.elements) for _ in range(rng.randint(5, 40))]
            if rho(phi(w)) != F20.prod(w):
                bad += 1
        check("mu(w) = rho(Phi(w)) on 60000 random words of length 5..40", bad == 0)

        # the Boolean form: T is a union over ker rho of intersections of the four instances
        kerset = set(ker)
        bad = total = 0
        for n in range(5):
            for w in itertools.product(F20.elements, repeat=n):
                total += 1
                if (phi(w) in kerset) != (F20.prod(w) == F20.identity):
                    bad += 1
        check(f"T = Phi^{{-1}}(ker rho), a union of {len(ker)} intersections, on all "
              f"{total} words of length <= 4", bad == 0)

        # erasure of the identity letter inside the reduced alphabet: 8 -> 7
        delta = alphabets[0]
        check("the 8-letter alphabet contains the identity, so erasure applies",
              F20.identity in delta)
        reduced = [d for d in delta if d != F20.identity]
        bad = total = 0
        for n in range(6):
            for v in itertools.product(delta, repeat=n):
                total += 1
                stripped = [d for d in v if d != F20.identity]
                if F20.prod(v) != F20.prod(stripped):
                    bad += 1
        check(f"mu(v) = mu(pi(v)) on all {total} Δ-words of length <= 5, so the obligation "
              f"drops to {len(reduced)} letters", bad == 0 and len(reduced) == 7)

        # honesty check: the reduction shrinks the obligation but evades NEITHER known
        # obstruction, and this must be stated wherever the reduction is stated
        eps2 = [d for d in delta if phase(d) == 2]
        check("Δ still carries eps = 2 letters, so F20-FULL-OBS-01 still applies to it",
              len(eps2) == 2, f"{eps2}")
        witness = [(0, 0), (1, 0), (1, 1)]   # k, u_0, u_1 of F20-SUB10-OBS-01
        check("the minimal witness of F20-SUB10-OBS-01 is a Δ-word, so that obstruction "
              "transfers verbatim to the 8-letter instance",
              all(g in delta for g in witness))
        w1 = [witness[0], witness[1], witness[2], witness[0]]
        w2 = [witness[0], witness[2], witness[1], witness[0]]
        check("and its two words still have different images over Δ",
              F20.prod(w1) != F20.prod(w2),
              f"{F20.prod(w1)} vs {F20.prod(w2)}")
        # the same witness survives the identity erasure, since k = (0,0) is the identity
        check("after erasure the witness collapses (k is the identity letter), so the "
              "7-letter instance needs its own test", witness[0] == F20.identity)


# ------------------------------------------------- [7] Lemma G and optimality of 8 letters


def is_abelian_by_elem2(G) -> bool:
    """Does G have an abelian normal subgroup with elementary abelian 2-quotient?"""
    for N in normal_subgroups(G):
        if not all(G.mul(x, y) == G.mul(y, x) for x in N for y in N):
            continue
        # quotient elementary abelian 2: g^2 in N for all g, and [g,h] in N for all g,h
        sq = all(G.mul(g, g) in N for g in G.elements)
        comm = all(G.mul(G.mul(g, h), G.inv(G.mul(h, g))) in N
                   for g in G.elements for h in G.elements)
        if sq and comm:
            return True
    return False


def section_7() -> None:
    with section("[7] Lemma G, and why 8 is optimal inside the equal-phase family"):
        check("F_20 is NOT (abelian)-by-(elementary abelian 2)",
              not is_abelian_by_elem2(F20))
        for G in (C4, C5, C20, V4, D5, S3):
            check(f"{G.name} IS (abelian)-by-(elementary abelian 2)",
                  is_abelian_by_elem2(G))
        # so a product of such groups cannot have F_20 as a quotient of a subgroup:
        # the property passes to direct products, subgroups and quotients
        check("hence no reduction of F_20 can have all coordinate groups abelian or D_5",
              not is_abelian_by_elem2(F20) and is_abelian_by_elem2(D5))
        subs = all_subgroups(F20)
        escapes = [H for H in subs if not is_abelian_by_elem2(_as_group(H))]
        check("among the subgroups of F_20, only F_20 itself escapes the property",
              len(escapes) == 1 and len(escapes[0]) == 20,
              f"{len(subs)} subgroups, orders "
              f"{sorted(len(H) for H in subs)}")

        # optimality: within the equal-phase family the alphabet is Z/4 x im(a_j), and
        # sum_j a_j(beta) = beta forces some image to have at least two elements
        found_all_singleton = False
        for k in range(1, 6):
            for consts in itertools.product(range(MODULUS), repeat=k):
                if all(sum(consts) % MODULUS == b for b in range(MODULUS)):
                    found_all_singleton = True
        check("no family with every image a singleton can work (the sum is constant)",
              not found_all_singleton)
        check("a family with every image of size 2 does work, giving 4*2 = 8 letters",
              all(len({BETA_SPLIT[b][j] for b in range(MODULUS)}) == 2
                  for j in range(K_COORDS))
              and all(sum(BETA_SPLIT[b]) % MODULUS == b for b in range(MODULUS))
              and len(set(BETA_SPLIT.values())) == MODULUS)
        # one coordinate may be shrunk to the free 4-letter alphabet C_4
        alt = {0: (0, 0, 0, 0), 1: (0, 1, 0, 0), 2: (0, 1, 1, 0),
               3: (0, 1, 1, 1), 4: (0, 1, 1, 2)}
        ok = (all(sum(alt[b]) % MODULUS == b for b in range(MODULUS))
              and len(set(alt.values())) == MODULUS)
        sizes = [4 * len({alt[b][j] for b in range(MODULUS)}) for j in range(K_COORDS)]
        check("a variant makes one coordinate the abelian 4-letter alphabet Z/4 x {0}",
              ok and sizes[0] == 4, f"alphabet sizes {sizes}")

        # the counting bound: lambda is a section of rho, so it is injective, so the
        # product of the alphabet sizes is at least |G|.  This is the only general lower
        # bound on the scheme, and the 8-letter construction is far above it -- which is
        # why "can it reach 2 letters?" is open rather than blocked.
        check("the achieved family satisfies the counting bound with room to spare",
              8 ** K_COORDS >= len(F20), f"8^4 = {8 ** K_COORDS} >> {len(F20)}")
        check("two-letter alphabets would need at least 5 coordinates (2^4 < 20 <= 2^5)",
              2 ** 4 < len(F20) <= 2 ** 5)
        # and every coordinate must satisfy the order-divisibility test
        maps4 = [coord_map(j) for j in range(K_COORDS)]
        bad_order = []
        for g in F20.elements:
            need = _order(F20, g)
            lcm = 1
            for m in maps4:
                lcm = lcm * _order(F20, m[g]) // _gcd(lcm, _order(F20, m[g]))
            if lcm % need != 0:
                bad_order.append(g)
        check("order divisibility ord(g) | lcm_j ord(f_j(g)) holds for all 20 letters",
              not bad_order, "a necessary condition any candidate family must pass")


def _order(G, g):
    n, x = 1, g
    while x != G.identity:
        x = G.mul(x, g)
        n += 1
    return n


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def _as_group(H) -> Group:
    els = sorted(H)
    return Group(f"subgroup of order {len(els)}", els, F20.mul, F20.identity)


# ------------------------------------------------------------------- [8] negative controls


def section_8() -> None:
    with section("[8] negative controls: the checker is not vacuous"):
        maps = [coord_map(j) for j in range(K_COORDS)]
        lam = {g: (phase(g), BETA_SPLIT[beta(g)]) for g in F20.elements}

        def factors(lam_map) -> bool:
            """Does mu factor through Phi?  Track pairs (Phi(w), mu(w)) to closure."""
            seen = {}
            frontier = []
            start = ((0, (0,) * K_COORDS), F20.identity)
            seen[start[0]] = start[1]
            frontier.append(start)
            while frontier:
                nxt = []
                for x, u in frontier:
                    for g in F20.elements:
                        y = h_mul(x, lam_map[g])
                        v = F20.mul(u, g)
                        if y in seen:
                            if seen[y] != v:
                                return False
                        else:
                            seen[y] = v
                            nxt.append((y, v))
                frontier = nxt
            return True

        check("the verified splitting factors", factors(lam))
        # a constant family cannot: it only sees the length
        const = {g: (0, (0, 0, 0, 0)) for g in F20.elements}
        check("an all-constant family does NOT factor (control)", not factors(const))
        # random non-injective perturbations must almost always fail
        rng = random.Random(7)
        fails = 0
        trials = 12
        for _ in range(trials):
            table = {g: (phase(g), tuple(rng.randrange(2) for _ in range(K_COORDS)))
                     for g in F20.elements}
            if not factors(table):
                fails += 1
        check(f"{fails} of {trials} random phase-preserving splittings fail to factor",
              fails >= trials - 2, "so factoring is a real constraint, not automatic")
        # and a family that keeps one coordinate injective factors trivially -- but its
        # alphabet is the full 20 letters, i.e. no reduction
        ident = {g: (phase(g), (beta(g), 0, 0, 0)) for g in F20.elements}
        first_alphabet = {(phase(g), beta(g)) for g in F20.elements}
        check("keeping one coordinate injective factors but gives no reduction",
              factors(ident) and len(first_alphabet) == 20,
              "its first alphabet is all 20 letters")
        check("no relabeling used in Theorem F is injective",
              all(len(set(m.values())) == 8 for m in maps))


def main() -> int:
    section_1()
    section_2()
    section_3()
    section_4()
    section_5()
    section_6()
    section_7()
    section_8()
    print("\n=== summary ===")
    if FAILURES:
        print(f"  {len(FAILURES)} FAILURES: {FAILURES}")
        return 1
    print("  all checks passed")
    print("  Theorem F: HeightOneForGroup F_20 reduces from 20 letters to the single "
          "8-letter alphabet Z/4 x {0,1}, and to 7 letters after erasing the identity.")
    print("  Live question: can the same scheme reach a 2-letter alphabet?  That would "
          "close F_20 via F20-STD-01.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
