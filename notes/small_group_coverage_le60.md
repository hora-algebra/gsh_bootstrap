# Coverage of the finite groups of order at most 60, and the shape of what is left

Ledger rows: `COVER-LE60-POS-01` (`COMPUTED`),
`COVER-LE60-RESIDUAL-01` and `FAMILY-PHASE-01` (both `UNREVIEWED`), and
`FAMILY-A-PRED-01` (`CONJECTURAL`).

**Status caveat, stated before the results rather than after them.** The
positive criteria below are first searched inside GAP, but all 281 positive
rows are then independently re-decided from emitted multiplication tables and
structural witnesses by `scripts/ci/verify_small_group_witnesses.py`.  It checks
the group laws and C1--C6/R1 directly, so the positive finite classification is
`COMPUTED`.  The asymmetry is essential: failing to emit a witness is not a
proof that none exists.  Therefore the exact 31-row residual and its 23
monolithic flags remain generated `UNREVIEWED` claims.  SmallGroups catalogue
completeness and `(order,id)` identification remain external `CITED` inputs.

Program: `scripts/gap/coverage_le60.g`. Certificate:
`data/experiments/coverage_le60.tsv`. Positive witnesses:
`data/experiments/coverage_le60_witnesses.jsonl`. Positive checker:
`scripts/ci/verify_small_group_witnesses.py`. Residual/table checker:
`tests/test_coverage_le60.py`.
Manifest: `data/experiments/small_group_coverage_le60.md`.

## 1. The question, and what a negative answer means

For a finite group `G`, "covered" means the full solution for `G`: for every
finite alphabet, every morphism `phi : Sigma* -> G` and every accepting subset
`P`, the language `phi^{-1}(P)` has generalized star height at most one — the
predicate `HeightOneForGroup G` of `AGENTS.md`.

`scripts/research/small_group_pst_coverage.py` answered this through order 31
by hand-building every group in Python. This note extends the range through 60
using GAP's SmallGroups library and includes `A_5`, the first non-solvable
simple group.

**A group appearing as `UNRESOLVED` below is not a group of height `>= 2`.** No
lower-bound tool exists (`N-LOWER-001`), so the list means exactly "not reached
by the criteria in §2", and nothing more. Every criterion is sufficient, and
C3 is tested in a narrower form than the divisor theorem it comes from, so the
unresolved set is an upper bound on the true one.

## 2. The criteria

| | Criterion | Ledger row | Status |
|---|---|---|---|
| C1 | `G` abelian | `PST-GRP-01` | CITED |
| C2 | `G` nilpotent of class `<= 2` | `PST-GRP-02` | CITED |
| C3 | `G = A : E` split, `A` abelian, `E` elementary abelian 2-group | `PST-GRP-03` | CITED |
| C4 | `G` dicyclic (hence every generalized quaternion group) | `DICM-EMB-01` | PROVED |
| C5 | `G = A_4` | `A4-ALLLANG-01` | PROVED |
| C6 | `A <= G` abelian of index two, split or not | `PST-GRP-03` | CITED |
| R1 | `G` non-monolithic and two quotients through distinct minimal normal subgroups are covered | `SUBDIRECT-RED-01` + `L-TRANS-001` | PROVED |

R1 is applied to a fixpoint. Distinct minimal normal subgroups intersect
trivially: their intersection is normal and properly contained in each, hence
trivial by minimality. Thus `G` embeds subdirectly in the product of the two
proper quotients. `SUBDIRECT-RED-01` closes the height-one class under finite
direct products and `L-TRANS-001` under injective morphisms.

C3 tests the split form, while `PST-GRP-03` speaks of divisors and is wider.
That narrowing can only move a group from covered to unresolved, never the
reverse.

C6 closes the one measured instance of that gap through order 60.  For index
two the split hypothesis is unnecessary: if `A <= G` is abelian of index two,
the Krasner--Kaloujnine embedding sends `G` into `A wr C_2 = (A x A) : C_2`,
which is split abelian-by-elementary-abelian-2, so `G` divides a C3-class group
whether or not `G` splits over `A`.  The scan
`scripts/gap/index_two_krasner_kaloujnine.g` found exactly one residual row
with such a subgroup — `SmallGroup(32,15) = C_4 . D_8`, nilpotent of class
three (so C2 misses it) and non-split over its `C_8 x C_2` (so C3 misses it).
C6 is applied as a separate sweep after C1--C5 and the first R1 fixpoint so
that no previously covered row changes verdict; dicyclic and several
R1-covered groups also have abelian index-two subgroups, and running C6
earlier would relabel them.  The same embedding is formalized in Lean in
`GSH/Groups/IndexTwoEmbedding.lean` on the branch of PR #56.

### The dicyclic correction found at order 60

The old C4 predicate used "a cyclic subgroup of index two and a unique
involution". At order 60 this labels three non-isomorphic groups as dicyclic:
`SmallGroup(60,1) = C_5 x Dic_3`, `SmallGroup(60,2) = C_3 x Dic_5`, and
`SmallGroup(60,3) = Dic_15`. The first two are not `Dic_15`.

The repaired predicate searches for a cyclic subgroup `<x>` of order `2n` and
an element `y` outside it satisfying the defining relations

    y^2 = x^n,       y^-1 x y = x^-1.

Only `SmallGroup(60,3)` passes at order 60. The other two remain covered, but
by R1 from their direct-product quotients. This changes the mechanism counts,
not the total covered count. The exact 13 C4 rows are pinned by a negative
control in `tests/test_coverage_le60.py`.

## 3. Result

There are 312 groups in the range. The generated verdicts are:

| Verdict | Groups |
|---|---:|
| C1 abelian | 102 |
| C2 nilpotent class `<= 2` | 50 |
| C3 split `A : E` | 76 |
| C4 dicyclic | 13 |
| C5 `A_4` | 1 |
| C6 index two (Krasner--Kaloujnine) | 1 |
| R1 subdirect fixpoint | 38 |
| **UNRESOLVED** | **31** |

Thus the range contains 210 non-abelian groups.  The 179 positive rows are
independently witness-checked (`COVER-LE60-POS-01`, `COMPUTED`); 138 of them are
the new order-32--60 increment.  GAP reports 31 residual rows, but that exact
negative side remains `COVER-LE60-RESIDUAL-01` (`UNREVIEWED`).  Of those 31,
GAP marks eight non-monolithic and 23 monolithic.  The latter are the generated
direct-attack list, not a proven exhaustive frontier and not a height lower
bound.

Before adding C5, the same criterion ladder left 40 groups. C5 and the R1
fixpoint recover exactly eight:

    A4; C2 x A4; (C2 x C2) : C9; C3 x A4; C4 x A4;
    C2 x C2 x A4; (C2)^4 : C3; C5 x A4.

### Positive control through order 31

The independent pure-Python audit gives the six PST exceptions

    A4, F20, C7 : C3, SL(2,3), S4, C2 x A4.

The new computation then applies the independently PROVED `A4-ALLLANG-01` to
`A4`, and R1 to `C2 x A4`, leaving exactly

    F20, C7 : C3, SL(2,3), S4.

The checker pins both stages, rather than claiming that the pure-Python program
itself outputs the four-group list.

## 4. The 23 direct problems split into three families

The split is by the **phase group**: for `G = A : C` with `A` abelian normal
and `C` cyclic, `C` is the phase group of the multi-mover mechanism of
`RESULTS.md` §5.5.

### Family A — prime phase group (6 groups)

| Group | Order | `A` | phase |
|---|---:|---|---:|
| `C_7 : C_3` | 21 | `C_7` | 3 |
| `C_13 : C_3` | 39 | `C_13` | 3 |
| `(C_4 x C_4) : C_3` | 48 | `C_4 x C_4` | 3 |
| `C_11 : C_5` | 55 | `C_11` | 5 |
| `(C_2)^3 : C_7` | 56 | `(C_2)^3` | 7 |
| `C_19 : C_3` | 57 | `C_19` | 3 |

`A_4` has left this problem family because `A4-ALLLANG-01` is PROVED. It is
still positive evidence for the prime-phase prediction. `C7C3-FULL-01` is
EMPIRICAL; the other five are unrun. A pass on them would remain evidence for
the mechanism, not a theorem for the family.

### Family B — composite phase group (7 groups)

`F_20 = C_5 : C_4` (20), `(C_2)^3 : C_4` (32),
`(C_3 x C_3) : C_4` (36), `C_7 : C_6` (42), `C_13 : C_4` (52),
`(C_3 x C_3) : C_6` (54), `C_9 : C_6` (54).

These meet the obstruction `F20-FULL-OBS-01` records for the existing
multi-mover mechanism. That is an obstruction to one mechanism, not a
star-height lower bound.

### Family C — no split `abelian : cyclic` decomposition (10 groups)

`SL(2,3)` (24), `S_4` (24), `C_2 . S_4` (48), `GL(2,3)` (48),
`((C_4 x C_2) : C_2) : C_3` (48),
`((C_3 x C_3) : C_3) : C_2` (54), `A_5` (60), and three 2-groups of order 32:
`(C_8 : C_2) : C_2`, `(C_2 x C_2) . (C_4 x C_2)`,
`(C_2 x Q_8) : C_2`.

The three order-32 groups are nilpotent of class exactly three, so they miss
`PST-GRP-02` by one step. A fourth, `C_4 . D_8 = SmallGroup(32,15)`, was in
this family until C6 settled it: it is class three and non-split, but its
`C_8 x C_2` of index two puts it in the divisor class of `PST-GRP-03` through
the Krasner--Kaloujnine embedding. `A_5` is the new non-solvable simple
endpoint of the extended range.

## 5. The eight dependent unresolved groups

- `SmallGroup(40,3)`, `SmallGroup(40,12)`, `SmallGroup(60,6)`, and
  `SmallGroup(60,7)` reduce to the `F_20` problem.
- `SmallGroup(42,2)` reduces to `C_7 : C_3`.
- `SmallGroup(48,30)` and `SmallGroup(48,48)` reduce to `S_4`.
- `SmallGroup(48,32)` reduces to `SL(2,3)`.

These are still unresolved groups, but they are not independent research
targets. The README retains all of them because its unit is a group isomorphism
class, not an obligation.
