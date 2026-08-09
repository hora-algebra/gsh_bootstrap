# The residual over-counts by one: index two does not need to split

**Status.** One row of `COVER-LE60-RESIDUAL-01` is settled by a theorem the
ledger already carries. Nothing here is a new theorem; it is a gap between what
`PST-GRP-03` says and what `scripts/gap/coverage_le60.g` tests.

## The gap

`PST-GRP-03` speaks of **divisors** of `A ⋊ E` with `A` commutative and `E`
elementary abelian 2. The C3 criterion in `coverage_le60.g` implements the
*split* special case: it looks for a commutative normal `A ◁ G` with `G/A`
elementary abelian 2 **and** a complement,

```gap
complements := ComplementClassesRepresentatives(G, N);
```

so a group whose only such `A` has no complement is reported `UNRESOLVED`.

For index two the split hypothesis is not needed. If `A ≤ G` is commutative of
index two, the Krasner--Kaloujnine embedding gives an injection

```
G ↪ A ≀ C₂ = (A × A) ⋊ C₂
```

and the right-hand side is commutative-by-elementary-abelian-2 **and split**, so
`G` divides a C3-class group and `PST-GRP-03` applies. Whether `G` itself splits
over `A` is irrelevant: the wreath product does the splitting.

Concretely, for `t ∉ A` write `g = a(g) · t^{φ(g)}` with `φ : G → C₂` the
membership phase, which is a homomorphism because `A` has index two. Send `g` to
the pair of coordinates `(a(g), a(t⁻¹ g t))` together with `φ(g)`. Injectivity
is immediate from the first coordinate and the phase. This is the classical
index-two case of Krasner--Kaloujnine, not a new construction; the same
embedding is formalized in Lean in `GSH/Groups/IndexTwoEmbedding.lean`
(`embedding_injective`, `exists_embedding`) on the branch of PR #56, which is
where the machine-checked version lives.

## What it settles

`scripts/gap/index_two_krasner_kaloujnine.g` scans all 32 residual rows through
order 60. Exactly one has a commutative subgroup of index two:

```
SmallGroup(32, 15) = C4 . D8 = C4 . (C4 x C2)
  commutative subgroup of index two: C8 x C2, order 16
  nilpotency class of G: 3        -- so PST-GRP-02 (class <= 2) misses it
  split: false                    -- so C3 as implemented misses it
```

It falls in the crack exactly: class three excludes it from `PST-GRP-02`, and
non-splitness excludes it from the implemented C3, while the theorem C3 is a
special case of covers it.

The two controls in the script fire as they should — `D_8` is found (cyclic
subgroup of index two) and `A_4` is not (it has no subgroup of order six at
all).

## Consequences, stated exactly

- The residual of `COVER-LE60-RESIDUAL-01` is 32 rows and should be **31**.
- Restricted to order at most 59 it is 29 and should be **28**.
- Order 60 is unaffected: none of `A_5`, `C_3 × (C_5 ⋊ C_4)`, `C_15 ⋊ C_4` has a
  commutative subgroup of index two.
- `FAMILY-PHASE-01` counts `SmallGroup(32, 15)` among its monolithic groups, so
  that partition shifts by one as well.

This is **not** a lower bound and not a statement about any group's actual
generalized star height; it moves one group from "the current search did not
reach it" to "a cited theorem covers it". The other 31 residual rows are
untouched — the scan found no other hit.

## What has not been done

The committed table is not regenerated here, because widening C3 changes a
mechanism column that `tests/test_coverage_le60.py` pins, and the honest fix is
to widen the criterion in `coverage_le60.g` itself rather than to special-case
one row. `N-KK-INDEX2-001` carries that.
