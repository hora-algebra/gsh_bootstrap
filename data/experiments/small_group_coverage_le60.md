# Run manifest: coverage of every finite group of order at most 60

Claims: `COVER-LE60-POS-01` (`COMPUTED`),
`COVER-LE60-RESIDUAL-01` and `FAMILY-PHASE-01` (both `UNREVIEWED`).  GAP emits
candidate multiplication tables and structural witnesses; the Python checker
independently re-decides every positive group law and C1--C5/R1 witness without
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

The positive Python checker runs without GAP.  For all 280 positive rows it
checks element 0 as identity, all multiplication-table entries, associativity,
two-sided inverses, and then the full criterion: C1 commutativity; C2 central
commutators; every subgroup/normality/exponent/intersection/product condition
of C3; the defining dicyclic relations and normal forms of C4; an explicit
isomorphism to the twelve even permutations for C5; and the two explicit R1
surjections, their previously verified smaller targets, and trivial kernel
intersection.  Nine claim-level mutations are all rejected.  The table checker
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
  audit, and about 24 s for the verdict run including nine full mutation
  controls; exact test time is reported by the test runner.
- Single process, no network.

## Result

312 groups total.  280 have a positive generated verdict: 102 abelian, 50
nilpotent of class at most two, 76 split `A : E`, 13 dicyclic, 1 `A_4`, and 38
from the subdirect fixpoint.  The fixpoint closed after 2 rounds.  The Python
checker accepts all 280 after traversing 22,786,789 finite obligations.  Among
the 210 non-abelian groups, 178 are therefore positive, including exactly 137
of orders 32 through 60.  GAP reports the remaining 32 as residual relative to
this criterion list and 24 as monolithic; those two negative counts remain
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
| `scripts/gap/coverage_le60.g` | `8d781ec29119f753fa750bd8121c22dd36edbfd3aea9c03639200da9593efffd` |
| `data/experiments/coverage_le60.tsv` | `8fa8d5ecfce11a2c77bef300290996f84b566725b10ad38e01932ef04d51e41e` |
| `data/experiments/coverage_le60_witnesses.jsonl` | `0d93a2f3fc784758344f53eaf62d26f07bbb0b2386013fab283b85de07abddac` |
| `scripts/ci/verify_small_group_witnesses.py` | `82eadcc6f02131fe506102229c1dbe9adbca8a9473590e5e3d0ee24523d9aec1` |
| `tests/test_small_group_witnesses.py` | `83d32f6d0ffb31a1802fbf431d59ea06c178d954b1b348f0ac89d65677f0bcc5` |
| `tests/test_coverage_le60.py` | `141376cd65a9977a9b1c91fde99fe645e06b54bee1c1c2e0bd3e7bdd64beb0b9` |
| `data/verdicts/small_group_coverage_le60.json` | `148f37ad4f87926b145c5b4c625cd20158d9e27ad0c9b1e756540cc5ad957b0c` |
