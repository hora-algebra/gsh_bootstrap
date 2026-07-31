# Run manifest: coverage of every finite group of order at most 60

Claims: `COVER-LE60-01` and `FAMILY-PHASE-01`, both `UNREVIEWED`.  GAP
searches the criteria, but no independent checker in this repository yet
re-decides the positive verdicts.  `M-COVER60-001` records the witness-based
migration needed for that upgrade.  Completeness of the enumeration is a
`CITED` input from GAP's SmallGroups library.  `FAMILY-A-PRED-01` is
`CONJECTURAL` and is not part of this finite partition claim.

Derivation and problem list: `notes/small_group_coverage_le60.md`.
Human-facing continuation: `README.md`, "位数60以下の非可換有限群".
Base commit: `ff1d985`.

## Commands

```bash
gap -q -b scripts/gap/coverage_le60.g > data/experiments/coverage_le60.tsv
python3 -m unittest tests.test_coverage_le60
```

The Python checker runs without GAP.  It checks row and ID completeness,
recomputes the abelian counts from the integer partition function, pins the
unresolved, monolithic, phase, dicyclic, and `A_4`-closure sets, and compares
every non-abelian `SmallGroup(n,i)` of order 32 through 60 with the README.
Mutation tests verify that each check can reject relevant corruptions.  It does
not independently re-decide C2, C3, C4, or R1; that is why the ledger status is
still `UNREVIEWED`.

## Environment

- GAP 4.15.1 with the SmallGroups library, macOS 26.5.2 arm64.
- Python 3.14.6 for the checker; standard library only.
- Wall clock on this machine: 5.91 s for GAP; the Python test time is reported
  by the test runner.
- Single process, no network.

## Result

312 groups total.  280 have a positive generated verdict: 102 abelian, 50
nilpotent of class at most two, 76 split `A : E`, 13 dicyclic, 1 `A_4`, and 38
from the subdirect fixpoint.  The fixpoint closed after 2 rounds.  The remaining
32 are unresolved relative to this criterion list; 24 of those are monolithic
and therefore the independent direct-attack list.  Among the 210 non-abelian
groups, the corresponding counts are 178 positive candidates and 32
unresolved.

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
| `scripts/gap/coverage_le60.g` | `cbbe177a864ff61f5a76967404d35a4b9b0f40f91fa604832845e38b1d34d2d5` |
| `data/experiments/coverage_le60.tsv` | `8fa8d5ecfce11a2c77bef300290996f84b566725b10ad38e01932ef04d51e41e` |
| `tests/test_coverage_le60.py` | `df2cc293d3eeae533f540619daae562a95881a8bdb5d2033bf688041fbc02a50` |
