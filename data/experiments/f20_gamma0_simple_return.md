# Run manifest: `Gamma_0` simple-first-return token

Candidate claim (intended ID `F20-GAMMA0-SIMPLE-RETURN-01`): over

```text
Gamma_0 = {a=(0,1), b=(1,0), c=(2,0), d=(3,0)},
```

let `R_0` contain the one-letter token `a` and every token whose mover skeleton
first returns from phase zero to phase zero without repeating a nonzero phase,
with arbitrary `a*` gaps between consecutive movers.  Then `R_0` is star-free,
restricts on `{a,b}` to the `F20-STD-01` token
`a union b a* b a* b a* b`.

This is a token-language result only.  It does **not** prove
`gsh(T_{Gamma_0}) <= 1`, reconstruct the identity fibre, or prove
`HeightOneForGroup F_20`.

## Follow-up acceptance test: bounded-visit hierarchy

Intended claim ID: `F20-GAMMA0-VISIT-HIER-01`.  Erase every `a` before
counting visits, and count only the nonzero partial sums after mover letters.
The input `F20-GAMMA0-SIMPLE-RETURN-01` is `PROVED` within this stacked
proposal by the all-word argument recorded in the accompanying note; it
remains outside the canonical integration chain until review and integration.
For every `k >= 1`, let `R^(k)` consist of `a` and the unrestricted
first-return tokens in which each nonzero phase occurs at most `k` times in
that mover walk.  The proof is accepted only if it establishes, for every
`k` and without a word-length sample:

1. `R^(k)` is star-free and `R^(1) = R_simp`;
2. `b c^(2k) d` lies in `R^(k+1) minus R^(k)` and cannot lie in
   `(R^(k))*`;
3. the increasing union of the `R^(k)` is the unrestricted first-return
   language, but no finite family of star-free sublanguages of `R_all` has
   union exactly equal to `R_all`.

Falsifiers are respectively a mover skeleton longer than `3k+1`, a failure
of the displayed phase-count formula, or a star-free expression for the
unrestricted first-return language.  Passing this test records a negative
artifact only: it closes the bounded-visit finite-hierarchy route and does not
close or shrink the height-one obligation for `T_{Gamma_0}`.  No further
`R^(k)` layer may be added after this obstruction is proved.

## Acceptance test

```bash
python3 -m unittest -v tests.test_f20_gamma0_simple_return
python3 scripts/ci/f20_gamma0_simple_return.py
```

Python standard library and repository-local modules only.  Language equality
and aperiodicity use no word-length cutoff.

## Exact construction

The fifteen mover skeletons are

```text
bbbb bbc bcb bcdc bd
cbb cbcd cc cdcb cdd
db dcbc dcd ddc dddd
```

Thus `R_0` is the finite union of `{a}` and the languages

```text
m_1 a* m_2 a* ... a* m_k
```

for the displayed skeletons.  The language `a*` is star-free over `Gamma_0`:
putting `TOP = not empty`, it is
`not (TOP (b union c union d) TOP)`, with no Kleene star in the expression.
Finite union and concatenation
therefore give a direct star-free construction of `R_0`; the computation is an
independent exact audit, not the sole reason for the star-free assertion.

| Exact check | Complete universe | Result |
|---|---:|---|
| simple first-return skeletons | all nonrepeating walks on the three nonzero phases | exactly 15 |
| candidate minimization | all reachable DFA states and all refinement blocks | 15 reachable, 15 minimal |
| candidate transition monoid | all generated transformations | 50 elements; maximum period 1; maximum stabilization index 5 |
| old cut comparison | all reachable states in 14 minimized-DFA products | 14/14 inequivalent; 331 product states total, 19--26 per product |
| positive two-letter restriction | full product of the two minimized DFAs | both 6 states; product has 6 reachable states and no mismatch |
| two-letter transition monoid | all generated transformations | 16 elements; maximum period 1 |

The candidate monoid's stabilization-index distribution is
`{1:3, 2:36, 3:5, 4:4, 5:2}`.

## Fixed witnesses and negative control

The shortest product-automaton witnesses against the old languages, ordered as
base, single, then `(left,right)` for right mover `b,c,d`, are

```text
bbdd a
dab cbb bcb db
cac bbc cc ddc
bad bd dcd cdd
```

These bounded words are used only to refute equality; equality itself is always
decided by complete reachable-product traversal.

Deleting the visited-phase hierarchy gives the unrestricted first-return
language.  Its minimized DFA has 6 states and transition monoid 62; the single
letter `c` has period 2.  The word `bbdd` is accepted by unrestricted
first-return and rejected by `R_0`: its phase walk is `1,2,1,0`, so it repeats
the nonzero phase 1.  This control makes the no-repeat condition load-bearing.

## Evidence classification

- `PROVED`: the explicit finite star-free construction above.
- exact finite support: minimization, the full transition monoids, the fourteen
  product comparisons, and the two-letter product comparison.  The fourteen
  comparisons are non-load-bearing diagnostics, not part of the ledger claim.
- no bounded-word pass is used as positive evidence.
- no verdict JSON is generated here because this scoped change does not add a
  `COMPUTED` row to `CLAIMS_LEDGER.md`.  If the result is later recorded as
  `COMPUTED` rather than from the explicit proof, a `tools/verdict.py` verdict
  must be added at that time.
