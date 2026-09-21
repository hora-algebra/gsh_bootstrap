# Run manifest: sharp five-letter reduction of the `F_20` obligation

Claim: `F20-ALPH5-01` (`PROVED`).  The arbitrary-word proof is in
`notes/f20_alphabetic_reduction.md` §13.  The program below checks the finite
construction data only; it is not a bounded-word substitute for that proof.

## Acceptance test

```bash
python3 -m unittest -v tests.test_f20_alph5_reduction
python3 scripts/ci/f20_alph5_reduction.py
```

Python standard library and repository-local modules only.  No words are
sampled.

| Exact support check | Universe | Result |
|---|---:|---|
| coordinate images | all 16 maps on all 20 letters | every image is the prescribed five-element `Delta_r` |
| section identity | all 20 letters | `rho(lambda(g)) = g` |
| homomorphism formula | all 400 phase/sum pairs | the scalar summary of the arbitrary-vector calculation agrees with `F_20` multiplication |
| identity erasure | all four distinct `Delta_r` | four letters remain and generate all 20 elements of `F_20` |

The load-bearing controls reject three false weakenings: deleting the fourth
threshold loses `beta=4`; using a threshold in every phase recreates the old
eight-letter alphabet; and changing one section value breaks recovery on an
explicit letter.

The universal step not delegated to the program is short.  All sixteen
coordinates have equal phase.  On that equal-phase subgroup, summing the
sixteen translation coordinates commutes with the common `C_4` action, so
`rho` is a homomorphism.  Its equality with the canonical evaluation on the
twenty generators therefore holds on every word.

## Evidence classification

- `PROVED`: the multiplication law, the explicit homomorphism and section,
  `ALPH-RED-01`, `FULL-ALPH-RED-02`, and the quotient/finite-Boolean closure
  already used in `F20-ALPH8-01`.  The ledger classifies
  `FULL-ALPH-RED-02` as `PROVED`; its separate independent-audit obligation
  `N-ERASE-AUDIT-001` remains `OPEN` and this construction does not close it.
- exact finite support, not load-bearing for the arbitrary-word quantifier:
  the three traversals in the table.
- no `CITED`, `COMPUTED`, `EMPIRICAL`, `CONJECTURAL`, or `SPECULATIVE` input is
  used to establish `F20-ALPH5-01`.

This reduces the remaining problem to four specified four-letter identity
fibres.  It proves none of those fibres has generalized star-height at most
one, and it does not prove `HeightOneForGroup F_20`.
