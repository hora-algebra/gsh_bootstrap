# Run manifest: `F_20` four-letter full-phase classification

Claim: `F20-ALPH4-CLASS-01` (`PROVED`).  The proof is
`notes/f20_alphabetic_reduction.md` §11.  This exact finite audit checks every
object used in that proof; it is support, not a replacement for the proof.

## Acceptance test

```bash
python3 -m unittest -v tests.test_f20_alph4_classification
python3 scripts/ci/f20_alph4_classification.py
```

Python standard library and repository-local modules only; no network, random
choice, or bounded word sample.

| Finite universe | Traversal | Result |
|---|---:|---|
| phase sections | all `5^4 = 625` | 620 generate `F_20`; 5 generate order 4 |
| phase-one generators | all 5 | 5 distinct `C_4` complements |
| order-compatible standard-generator images | all `4 × 10 = 40` | 20 automorphisms; the 20 quotient-inverting candidates fail |
| automorphism action on sections | all `20 × 625` images | one orbit `(size 5, order 4)` and 31 orbits `(size 20, order 20)` |
| projective invariant | all 625 sections and all orbit images | 31 nonzero normalized keys, constant and complete on generating orbits |

The exceptional five sections agree exactly with the five complements.  Four
negative controls reject: making every section generating; collapsing all
generating sections into one orbit; confusing the five exceptions with the 125
identity-containing sections; and doubling the automorphism count by allowing
the forbidden quotient inversion.

## Scope

This does **not** construct a route-(iv) factorization with four-letter
coordinates and proves no generalized-star-height statement.  It classifies
only the coordinate forced by `F20-PHASE-RIGID-01` when that coordinate itself
generates `F_20`.  A minimum-size factorization could instead have its
phase-preserving coordinate equal to a complement and obtain generation from a
different coordinate.
