# Coverage of the finite groups of order at most 59, and the shape of what is left

Ledger rows: `COVER-LE59-01` and `FAMILY-PHASE-01`, both `UNREVIEWED`, and
`FAMILY-A-PRED-01` (`CONJECTURAL`).

**Status caveat, stated before the results rather than after them.** The
criteria below are searched inside GAP and nothing in this repository
re-decides them, so the verdicts are generated rather than re-derived and the
rows sit at `UNREVIEWED`. `tests/test_coverage_le59.py` checks the table's
completeness, recomputes its abelian counts from the integer partition
function, and checks agreement with the repository's own GAP-free
implementation below order 32 — real checks, but not the criteria themselves.
`M-COVER59-001` is the migration to witness verification.
Program: `scripts/gap/coverage_le59.g`. Certificate:
`data/experiments/coverage_le59.tsv`. Checker: `tests/test_coverage_le59.py`.
Manifest: `data/experiments/small_group_coverage_le59.md`.

## 1. The question, and what a negative answer means

For a finite group `G`, "covered" means the full solution for `G`: for every
finite alphabet, every morphism `phi : Sigma* -> G` and every accepting subset
`P`, the language `phi^{-1}(P)` has generalized star height at most one — the
predicate `HeightOneForGroup G` of `AGENTS.md`.

`scripts/research/small_group_pst_coverage.py` answered this for order `<= 31`
by hand-building every group in Python. This note extends the range to 59 using
GAP's SmallGroups library. Order 59 is chosen because `A_5` has order 60: the
range stops one step below the first non-solvable simple case.

**A group appearing as `UNRESOLVED` below is not a group of height `>= 2`.** No
lower-bound tool exists (`N-LOWER-001`), so the list is exactly "not reached by
the criteria named in §2", and nothing more. Every criterion is *sufficient*,
and two of them (C3, C4) are tested in a narrower form than the theorem they
come from, so the unresolved list is an **upper bound** on the true one.

## 2. The criteria

| | Criterion | Ledger row | Status |
|---|---|---|---|
| C1 | `G` abelian | `PST-GRP-01` | CITED |
| C2 | `G` nilpotent of class `<= 2` | `PST-GRP-02` | CITED |
| C3 | `G = A : E` split, `A` abelian, `E` elementary abelian 2-group | `PST-GRP-03` | CITED |
| C4 | `G` dicyclic (hence every generalized quaternion group) | `DICM-EMB-01` | PROVED |
| R1 | `G` non-monolithic and two quotients through distinct minimal normal subgroups are covered | `SUBDIRECT-RED-01` + `L-TRANS-001` | PROVED |

R1 needs an argument. Distinct minimal normal subgroups intersect trivially:
`N_1 cap N_2` is normal and properly contained in each, so it is trivial by
minimality. Hence a non-monolithic `G` embeds subdirectly in `G/N_1 x G/N_2`
with both quotients proper. `SUBDIRECT-RED-01` closes the height-one class
under finite direct products, `L-TRANS-001` under injective morphisms, so `G`
is covered as soon as both quotients are. R1 is applied to a fixpoint; it
closed after 2 rounds.

C3 tests the split form, while `PST-GRP-03` speaks of divisors and is wider.
C4 tests `G` itself rather than its divisors. Both narrowings can only move a
group from covered to unresolved, never the reverse.

## 3. Result

299 groups, of which 263 are covered:

| Verdict | Groups |
|---|---|
| C1 abelian | 100 |
| C3 split `A : E` | 72 |
| C2 nilpotent class `<= 2` | 50 |
| R1 subdirect fixpoint | 24 |
| C4 dicyclic | 17 |
| **UNRESOLVED** | **36** |

Of the 36, twelve are non-monolithic and reduce to smaller unresolved
quotients — `C_2 x A_4` to `A_4`, `C_4 x A_4` and `A_4 : C_4` to `A_4`, and so
on. **24 are monolithic and need a direct attack.**

### Positive control

Restricted to order `<= 31` the unresolved set is exactly

    A_4 (12), F_20 = C_5 : C_4 (20), C_7 : C_3 (21), SL(2,3) (24), S_4 (24), C_2 x A_4 (24)

which is the six groups of `FRONTIER-ORD20-01`. That value was obtained by a
different program, in pure Python, without GAP. Two independent
implementations agreeing on the overlap is why the extension to 59 is
trusted; `tests/test_coverage_le59.py` locks the agreement in place.

## 4. The 24 remaining problems split into three families

The split is by the **phase group**: for `G = A : C` with `A` abelian normal
and `C` cyclic, `C` is the phase group of the multi-mover mechanism of
`RESULTS.md` §5.5. `F20-FULL-OBS-01` (COMPUTED, negative) localized the failure
of that mechanism on `F_20` to the phase group `Z/4` being **composite**: the
`eps = 2` letters have phase orbit `{0, 2}`, a proper subgroup, so they bounce
between the odd phases forever without meeting the cut phase. `C7C3-FULL-01`
then confirmed the prediction on a **prime** phase group `Z/3`, where every
non-zero `eps` generates.

### Family A — prime phase group (7 groups)

| Group | Order | `A` | phase |
|---|---|---|---|
| `A_4` | 12 | `C_2 x C_2` | 3 |
| `C_7 : C_3` | 21 | `C_7` | 3 |
| `C_13 : C_3` | 39 | `C_13` | 3 |
| `(C_4 x C_4) : C_3` | 48 | `C_4 x C_4` | 3 |
| `C_11 : C_5` | 55 | `C_11` | 5 |
| `(C_2)^3 : C_7` | 56 | `(C_2)^3` | 7 |
| `C_19 : C_3` | 57 | `C_19` | 3 |

Two of the seven already have evidence: `A4-FULL-01` and `C7C3-FULL-01`. The
five others have never been run. This is the family where the existing
mechanism is *predicted* to work, and the prediction is the falsifiable
content of `FAMILY-PHASE-01`.

### Family B — composite phase group (7 groups)

`F_20 = C_5 : C_4` (20), `(C_2)^3 : C_4` (32), `(C_3 x C_3) : C_4` (36),
`C_7 : C_6` (42), `C_13 : C_4` (52), `(C_3 x C_3) : C_6` (54), `C_9 : C_6` (54).

These meet the obstruction `F20-FULL-OBS-01` proves. Attacking them with the
same mechanism is predicted to fail, and `F_20` is the case where that
prediction is already `COMPUTED`.

### Family C — no split `abelian : cyclic` decomposition (10 groups)

`SL(2,3)` (24), `S_4` (24), `C_2 . S_4` (48), `GL(2,3)` (48),
`((C_4 x C_2) : C_2) : C_3` (48), `((C_3 x C_3) : C_3) : C_2` (54), and four
2-groups of order 32: `(C_8 : C_2) : C_2`, `(C_2 x C_2) . (C_4 x C_2)`,
`C_4 . D_8`, `(C_2 x Q_8) : C_2`.

The four order-32 groups are a genuinely new phenomenon in this range: they are
**nilpotent of class exactly 3**, so they sit just outside `PST-GRP-02`, which
stops at class 2. They are the smallest groups here whose obstruction is
nilpotency class rather than a phase group, and nothing in the repository
addresses them.

## 5. What this changes

The frontier is unchanged at order 12 as of this branch's base — `A_4` is still
the smallest unresolved group and `FRONTIER-ORD20-01` stands. That may not last:
the unmerged branch `codex/order12-height-one-lean` raises `A4-FULL-01` to
`PROVED`, and an independent audit run while this note was written did not break
it. If that lands, Family A loses its flagship instance to the *solved* column
and `FAMILY-A-PRED-01` gets its first non-sampled support; the 24-problem list
itself is unaffected, since `A_4` is one of the 24 either way. What is new is the *shape* of the
remaining work in the wider range: 24 problems, not an unstructured list, and
7 of them share the exact form on which the repository's one working mechanism
has already succeeded once.

Obligations opened: `N-FAMILY-A-001` (run the mechanism on the five untested
Family A groups), `N-NILP3-001` (the class-3 obstruction of the order-32
groups).
