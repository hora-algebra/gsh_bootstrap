# Run manifest: C_7⋊C_3 height-one finite core

Claim: `C7C3-H1-FINITE-CORE-01` (`COMPUTED`).
Target theorem: `C7C3-FULL-H1-01` / `C7C3-ALLLANG-01` (`PROVED`).

This run decides only the finite token and factorization obligations.  The
Schützenberger theorem and the closure/reversal/full-alphabet composition are
separate cited/proved inputs in `notes/c7c3_height_one.md`.

## Commands

```bash
python3 -m unittest -v tests.test_c7c3_height_one
python3 scripts/ci/c7c3_height_one.py
```

Python standard library plus repository-local `tools.regex_cert` and
`tools.verdict`; single process; no network; no sampled-word branch.

## Complete finite universes

| Check | Exhausted universe | Result |
|---|---:|---|
| first/post-cut token aperiodicity | 102 minimal DFA; 4,638 transition-monoid elements | PASS |
| mod-seven residue factorization | 357 formula/counter pairs; 9,555 reachable product states | PASS |
| arithmetic atom coverage | 57 atoms; 171 checked fields | PASS |

The 57 atoms are forward `set` 9, forward `anti` 24, and backward `anti` 24.
The last family is transported by reversal.

## Negative controls

All 5 fired:

1. omit all initial first-token automata;
2. insert a same-letter repeat pattern with period three;
3. replace the loop block `X^7` by `X^6`;
4. delete the zero-cut `V0` case at residue zero;
5. omit the backward/reversal atoms.

Machine-readable verdict: `data/verdicts/c7c3_height_one.json`.
