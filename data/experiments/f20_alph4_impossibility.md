# Run manifest: support for the `F_20` four-letter impossibility theorem

Claim: `F20-ALPH4-RIGID-01` (`PROVED`).  The universal proof, valid for an
arbitrary number of coordinates, is in
`notes/f20_alphabetic_reduction.md` §12.  The program below checks the concrete
`F_20` inputs only and does not carry a `COMPUTED` verdict for that theorem.

## Acceptance test

```bash
python3 -m unittest -v tests.test_f20_alph4_impossibility
python3 scripts/ci/f20_alph4_impossibility.py
```

Python standard library and repository-local modules only.  There is no word
sampling and no bounded search for factorizations.

| Finite support check | Universe | Result |
|---|---:|---|
| nontrivial same-phase differences | all 80 ordered pairs | every difference has order 5 and nonidentity fourth power |
| four-image phase-preserving maps | all 625 phase sections × 80 pairs | all 50,000 fibre pairs collapse |
| nontrivial character images in `F_5^×` | orders 2 and 4 | both root sums vanish |

Two load-bearing controls delimit the theorem.  Replacing the fourth power by
the fifth kills every target difference, and allowing five images admits a
phase-preserving map which separates a same-phase pair.  Thus the proof
does not extend to a bound of six; this is not an existence certificate for a
five-letter factorization.

The universal part not delegated to the program is the projector argument:
for arbitrary `k` and `P≤C_4^k`, the equivariant map `L:U→C_5` sees only the
coordinates whose character equals the target character.  This is proved
directly in the note.

## Evidence classification

- `PROVED`: the `F_20` multiplication law and the projector/equivariance setup
  of `F20-PHASE-RIGID-01`; the new arbitrary-`k` deduction in §12.
- exact finite support, not load-bearing for the universal quantifier: the
  three traversals in the table above.
- no `CITED`, `COMPUTED`, `EMPIRICAL`, `CONJECTURAL`, or `SPECULATIVE` input is
  used to establish `F20-ALPH4-RIGID-01`.
