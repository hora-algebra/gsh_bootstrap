# Run manifest: coverage of every finite group of order at most 59

Claims: `COVER-LE59-01` and `FAMILY-PHASE-01`, both `UNREVIEWED` — the criteria
are searched inside GAP and nothing in this repository re-decides them, which is
what `M-COVER59-001` migrates. The enumeration itself is `CITED` (GAP's
SmallGroups library). `FAMILY-A-PRED-01` (`CONJECTURAL`) is the prediction
attached to the partition, not part of it.

Derivation and the resulting problem list: `notes/small_group_coverage_le59.md`.
Base commit: `dd8d4ef`.

## Commands

```bash
gap -q -b scripts/gap/coverage_le59.g > data/experiments/coverage_le59.tsv
python3 -m unittest tests.test_coverage_le59            # runs without GAP
```

The second command is what CI runs. GAP is not available on the CI runner, so
the audit is produced offline and its output is committed; `tests/` re-derives
the parts that can be re-derived without GAP, including a partition-function
computation of the abelian counts and agreement with the repository's own
GAP-free implementation on orders <= 31.

## Environment

- GAP 4.15.1 with the SmallGroups library, macOS (darwin 25.5.0).
- Python 3.14.6 for the checker; standard library only.
- Wall clock: about 55 s for the GAP run, 0.01 s for the checker.
- Single process, no network.

## Result

299 groups. 263 covered (100 abelian, 50 nilpotent of class <= 2, 72 split
`A : E`, 17 dicyclic, 24 by the subdirect fixpoint), 36 unresolved, of which 24
are monolithic and therefore need a direct attack. The fixpoint closed after 2
rounds.

Restricted to order <= 31 the unresolved set is exactly the six groups of
`FRONTIER-ORD20-01`, which is the positive control: that value was obtained
independently, in pure Python, by `scripts/research/small_group_pst_coverage.py`.

## Hashes

| Artifact | sha256 |
|---|---|
| `scripts/gap/coverage_le59.g` | `ad43c132921878fa5e4e2dd33fbd9f9d7b78ab404c9f6117ef096ae30b052e66` |
| `data/experiments/coverage_le59.tsv` | `802f634060b958cc5ba0afbb461debc317ac5db406c9378ac2e9421cb74c038d` |
| `tests/test_coverage_le59.py` | `cbc576458a46dda6e1c6de3989efbe00ea1d993eb002c163f53bf3466a561da5` |
