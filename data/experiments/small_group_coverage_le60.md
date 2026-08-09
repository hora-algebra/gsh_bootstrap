# Run manifest: coverage of every finite group of order at most 60

Claims: `COVER-LE60-POS-01` (`COMPUTED`),
`COVER-LE60-RESIDUAL-01` and `FAMILY-PHASE-01` (both `UNREVIEWED`).  GAP emits
candidate multiplication tables and structural witnesses; the Python checker
independently re-decides every positive group law and C1--C6/R1 witness without
importing GAP.  The exact residual remains a GAP search result: absence of an
emitted witness is not an independently checked non-membership theorem.
Completeness and ID association of the enumeration are `CITED` inputs from
GAP's SmallGroups library.  `FAMILY-A-PRED-01` is `CONJECTURAL` and is not part
of the positive finite classification.

Derivation and problem list: `notes/small_group_coverage_le60.md`.
Human-facing continuation: `README.md`, "位数60以下の非可換有限群".
Coverage-table base commit: `ff1d985`; independent-witness-audit base commit:
`31fe32a`.

## Commands

```bash
gap -q -b scripts/gap/coverage_le60.g > data/experiments/coverage_le60.tsv
python3 scripts/ci/verify_small_group_witnesses.py
python3 -m unittest tests.test_small_group_witnesses
python3 -m unittest tests.test_coverage_le60
```

The positive Python checker runs without GAP.  For all 281 positive rows it
checks element 0 as identity, all multiplication-table entries, associativity,
two-sided inverses, and then the full criterion: C1 commutativity; C2 central
commutators; every subgroup/normality/exponent/intersection/product condition
of C3; the defining dicyclic relations and normal forms of C4; an explicit
isomorphism to the twelve even permutations for C5; the subgroup closure,
commutativity, and exact index of the C6 abelian index-two subgroup (the
Krasner--Kaloujnine divisor form of `PST-GRP-03`); and the two explicit R1
surjections, their previously verified smaller targets, and trivial kernel
intersection.  Ten claim-level mutations are all rejected.  The table checker
separately checks row and ID completeness,
recomputes the abelian counts from the integer partition function, pins the
unresolved, monolithic, phase, dicyclic, and `A_4`-closure sets, and compares
every non-abelian `SmallGroup(n,i)` of order 32 through 60 with the README.
Its mutation tests verify that each check can reject relevant corruptions.  It
pins residual drift but does not re-run the negative search, which is why the
residual ledger status remains `UNREVIEWED`.

## Environment

- GAP 4.15.1 with the SmallGroups library, macOS 26.5.2 arm64.
- Python 3.14.6 for the checker; standard library only.
- Wall clock on this machine: 7.5 s for GAP, about 2.1 s for one clean witness
  audit, and about 24 s for the verdict run including ten full mutation
  controls; exact test time is reported by the test runner.
- Single process, no network.

## Result

312 groups total.  281 have a positive generated verdict: 102 abelian, 50
nilpotent of class at most two, 76 split `A : E`, 13 dicyclic, 1 `A_4`,
1 abelian-index-two (C6, the Krasner--Kaloujnine divisor form of `PST-GRP-03`,
added 2026-08-09 and settling exactly `SmallGroup(32,15)`), and 38 from the
subdirect fixpoint.  The fixpoint closed after 2 rounds, plus 1 round of the
post-C6 re-run that found nothing new.  The Python checker accepts all 281
after traversing 22,822,197 finite obligations.  Among the 210 non-abelian
groups, 179 are therefore positive, including exactly 138 of orders 32 through
60.  GAP reports the remaining 31 as residual relative to this criterion list
and 23 as monolithic; those two negative counts remain
`UNREVIEWED` rather than being promoted by the positive witness audit.

Before the `A_4` seed, the same ladder leaves 40 groups.  `A4-ALLLANG-01` and
the subdirect fixpoint recover exactly 8.  Through order 31, the independent
pure-Python audit first gives the old six-group PST frontier; the `A_4` seed and
its `C_2 x A_4` subdirect consequence leave exactly 4, providing a two-stage
positive control.

The order-60 extension also exposed a false C4 shortcut.  A cyclic subgroup of
index two plus a unique involution does not characterize a dicyclic group:
`C_5 x Dic_3` and `C_3 x Dic_5` were false positives.  The generator now checks
the defining square and inversion relations.  Only `Dic_15` remains C4; the
two direct products remain positively covered through R1.  Thus the mechanism
counts change while the total positive count does not.

## Hashes

| Artifact | sha256 |
|---|---|
| `scripts/gap/coverage_le60.g` | `6400e64e8ee207f458fd69878525ce8a7f9fbcdf18cee90208e7c61e6bc9280d` |
| `data/experiments/coverage_le60.tsv` | `c84aa083d2f04e44011cfa204f04d3b858a15cfd79ed1dc457fa23ddb328950e` |
| `data/experiments/coverage_le60_witnesses.jsonl` | `e5ae5f26737d2bead75ae9c673b44b1aa2eb02afeed11ae758b68ac4fbcf5aef` |
| `scripts/ci/verify_small_group_witnesses.py` | `657dfb6968f69695c3fa7d235a164bd40917614d86746360e0c253239e4f769c` |
| `tests/test_small_group_witnesses.py` | `c5e27cd79cedff711a00d98345c051c2777715f17922c81813e48fff91874c9f` |
| `tests/test_coverage_le60.py` | `566ad370c2b224c0bf5b1796446be1234822e1aa82dc8b5fa3f70a5c550cd5ee` |
| `data/verdicts/small_group_coverage_le60.json` | `f373c3877dc44f19e9bf3b68ac364354268f172b159adf6874d14a804e245e1c` |
