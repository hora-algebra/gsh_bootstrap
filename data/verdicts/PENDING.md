# COMPUTED rows not yet backed by a verdict

`tools/verdict.py` computes what a row's evidence can support, from what the
program did, and `scripts/ci/lint_claims.py` refuses a `COMPUTED` row whose
verdict does not reach `COMPUTED`. Every row here predates that machinery and is
still backed only by prose, so each is grandfathered — once.

**The list may shrink and never grow.** A row added to `CLAIMS_LEDGER.md` as
`COMPUTED` from now on must be backed by a verdict; migrating a row here means
deleting its line, which is a diff a reviewer can see. `lint_claims.py` fails if
a line here no longer corresponds to an unbacked `COMPUTED` row, so the list
cannot rot into a permanent excuse.

Each entry names **the specific step that a program has not decided**, with the
code location, so that migrating the row is a defined task rather than a
judgement call. The findings come from the 2026-07-25 audit; the ones marked
*(verified here)* were re-checked directly against the code while writing this
file.

## Ranked by what the audit found

- `THOMAS-D2-02` — **repaired, awaiting re-attribution.** Its 2026-07-25
  certification traversed a machine on `(parse, d)` in which `d` was defined to
  be `-1` exactly when `parse == 1` and the acceptance test asked whether
  `d == -1` when `parse == 1`. None of `|w|_a`, `|w|_b`, `#tok`, `#ab` appeared,
  so all four coefficients of the identity could change without the program
  noticing, and its one negative control perturbed the acceptance constant
  rather than the claim *(verified here: all four coefficient perturbations are
  invisible to that machine)*. The identity itself is true. It is now decided by
  `scripts/ci/completeness_upgrade.py` `check_thomas`, with ten coefficient
  perturbations all rejected — but that check names the step id
  `THOMAS-D2-02/identity`, because the row also claims a star height for the
  segment-counting languages and that half is elsewhere. **To migrate:** decide
  the height half, then join the two with `tools.verdict.conjunction`.

- `LAAB-04-01` — the composite identity is decided (`check_laab`, six
  coefficient perturbations rejected), but the row claims a *height*, and the
  height of the feature languages is asserted in the docstring of
  `scripts/research/a4_attempt.py` with no certificate behind it. **To migrate:**
  compute the star height of the feature expressions, as
  `WATOM-45-01/height` now does for its atoms.

- `WEIS-L2-M2-01` — same shape: the cell-constancy results are exact product BFS
  (`scripts/research/weis_l2_family.py` `prove_function`), but the row asserts
  that a Boolean combination of the features has height at most one, and no
  program measures that height. `main()` also runs no control that must fire.

- `FRONTIER-ORD20-01` — **names no backing script at all.** Its evidence says the
  correction is "bookkeeping over this ledger's own statuses". The group theory
  it rests on is `SMALL-NONAB-31-01`, which is genuinely computed; the frontier
  half depends on the *absence* of a proof for `A_4`, and an absence is not
  something a traversal establishes. `PROOF_OBLIGATIONS.md` `N-A4FULL-002`
  describes the same situation as `EMPIRICAL`, so the two registers disagree.
  **To migrate:** attribute the mathematical half to `SMALL-NONAB-31-01`'s
  verdict and state the bookkeeping half as what it is.

- `F20-COH-SEP-01` — the claim quantifies over **every** `n >= 1`; the program
  checks `for n in range(1, 5)` *(verified here:
  `scripts/research/f20_fibration_geometry.py` `section_2`)*, then prints
  "H^n = 0 for every n >= 1". The universal statement is true and standard —
  `|C_4|` and `5` are coprime, so the cohomology vanishes — but that is a
  citation, not this computation. **To migrate:** split the row, or cite the
  coprimality theorem for the universal half.

- `TRANSD-LADDER-01` — a composite of five rungs of which only (d) is an
  exhaustive traversal; (a) is an elementary argument, (b) and (c) are `CITED`,
  (e) is a definition. `COMPUTED` describes one fifth of the row.

- `F20-FULL-OBS-01` — the 291-pattern table is exact and its judge has a positive
  control, but the causal clause ("the mechanism fails *because* …") is inferred
  from seven hand-picked sub-alphabets, and the table's verdict is printed rather
  than asserted, so the script exits 0 either way.

- `SFA-L2-MEASURE-01` — the cycle rank and the language equalities are exact; the
  concluding Boolean-closure step is printed and not checked in this script.

- `F20-BASECODE-01` — non-star-freeness is exact via an explicit period-5 element.
  Its premises (biunitarity, base = first-return code) are checked on words of
  length `<= 4`. Both are provable in a line, but the line is not written down.

- `SMALL-NONAB-31-01` — every per-group decision is exact; "these 45 are all of
  them" is a hard-coded table marked `CITED` in the source. Consistent, but the
  row's status covers both halves.

- `A4-STD-01` — the row's own evidence concedes that its named script samples,
  and points at `A4-STD-02` as the operative proof. **To migrate:** make the
  dependency the evidence, or merge the rows.

- `WEIS-L2-NOTFN-01` — the mathematics is sound (a witness refutes a "is a
  function of" claim outright, so no full traversal is needed), but the evidence
  says "114 reachable product states" when 114 is how far the search had got when
  it found the witness *(verified here: `explored` is a counter, not the product
  size)*. A factual correction to the evidence cell, not a demotion.

- `WEIS-L2-M3-01` — the positive half asserts; the twelve negative verdicts are
  printed only, and a `None` from exceeding the search cap is not distinguished
  from a decided negative.

- `WEIS-L2-RSH-01` — the `2^12` subset sweep is complete, but the assertion
  checks only that the set of accepting subsets is non-empty, while the claim is
  that there is **exactly one**.

- `F20-MONO-FRONT-01` — the representation-theoretic half is exact over all 400
  products; the cohomological-period half is a note plus a citation.

- `A4-STD-02`, `F20-STD-01`, `SEARCH-CAL-01`, `SEARCH-CAL-02`, `WEIS-L2-GSH-01` —
  no defect found. Each has a genuine decision procedure, asserts its verdict,
  and exits non-zero on failure. `WEIS-L2-GSH-01` is the sturdiest row in the
  ledger: ground truth recompiled from the printed regular expression, exact
  equivalence, and the star height asserted rather than printed. These are
  pending only because their scripts do not yet report through `tools.verdict`.

## Not on this list

`A5-GEN145-01` and `WATOM-45-01` migrated on 2026-07-25 and are backed by
`data/verdicts/completeness_upgrade.json`. `A5-GEN145-01` gained the lower bound
it had been missing: an equivalence check can only ever give `height <= 1`, and
the row claims `= 1`, so the non-aperiodicity of the transition monoid is now
computed too.
