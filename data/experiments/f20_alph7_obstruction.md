# Run manifest: F_20 seven-letter old-cut obstruction

Claim: `F20-ALPH7-OBS-01` (`COMPUTED`).

This run decides only whether the base/single/pair cut family of
`F20-FULL-OBS-01` works after the alphabet reduction and identity erasure of
`F20-ALPH8-01`. It does not decide `HeightOneForGroup F_20` and gives no
generalized-star-height lower bound.

## Commands

```bash
python3 -m unittest -v tests.test_f20_alph7_obstruction
python3 scripts/ci/f20_alph7_obstruction.py
```

Python standard library and repository-local modules only; no network and no
word sampling.

## Complete finite universes

| Check | Exhausted universe | Result |
|---|---:|---|
| cut-pattern aperiodicity | 17 base/single/pair signatures | all have nontrivial period |
| explicit collision | all 36 forward/backward feature fields and both images | fields equal; images `(2,1)` and `(2,2)` differ |
| minimality | all 400 words of length at most three | no earlier collision |

The witness is

```text
k (1,0) (1,1) k   versus   k (1,1) (1,0) k,   k=(0,1).
```

All three controls fired: replace the alphabet by the known positive
two-generator case; identify the witness words; delete the letter-count
coordinates.

Machine-readable verdict: `data/verdicts/f20_alph7_obstruction.json`.
