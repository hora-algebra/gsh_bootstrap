# Run manifest: F_20 phase rigidity and generating-pair audit

Claims:

- `F20-PHASE-RIGID-01` (`PROVED`): the general theorem is the Maschke
  argument in `notes/f20_alphabetic_reduction.md` §10.  The finite checks here
  only audit its concrete action formula and a negative control; they do not
  establish the universally quantified theorem.
- `F20-GENPAIR-AUDIT-01` (`COMPUTED`): exact enumeration of the two-element
  generating subsets and the automorphism orbit of the standard alphabet.

## Commands

```bash
python3 -m unittest -v tests.test_f20_phase_rigidity
python3 scripts/ci/f20_phase_rigidity.py
```

Python standard library and repository-local modules only; no network and no
word sampling.

## Exact finite universes

| Check | Universe | Result |
|---|---:|---|
| conjugation action on `C_5` | all `20 × 5 = 100` pairs | `u -> 2^(-phase)u` |
| phase-only negative control | all 256 additivity cases and four phases | two binary images suffice for `C_4` alone |
| generating subsets | all `binom(20,2) = 190` | 120 generate `F_20` |
| possible standard-generator images | all `4 × 10 = 40` order-compatible pairs | 20 automorphisms |

The 120 generating subsets split into 40 each of order profiles `(4,5)`,
`(4,4)`, and `(2,4)`.  The standard alphabet has an automorphism orbit of
size 20, leaving 100 generating pairs not covered by `F20-STD-01` through a
group automorphism alone.

Machine-readable verdict for the finite claim:
`data/verdicts/f20_phase_rigidity.json`.
