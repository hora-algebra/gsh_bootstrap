# AGENTS.md

## Mission

Advance the generalized star-height project by producing small, checkable mathematical or Lean artifacts. Optimize for correctness, reproducibility, and preservation of failed ideas—not persuasive prose.

## Read first

1. `README.md`
2. `CLAIMS_LEDGER.md`
3. `PROOF_OBLIGATIONS.md`
4. the single prompt or issue assigned to you
5. only the source files named by that issue

Do not ingest the entire repository unless the task genuinely requires it.

## Mathematical vocabulary

- “star-height” means **generalized** star-height unless prefixed by “restricted”.
- `HeightOneForGroup G` means: for every finite alphabet, every monoid morphism from the free monoid to `G`, and every accepting subset of `G`, the recognized language has generalized star-height at most one.
- “recognized by” is not “syntactic monoid equal to”.
- `A_5` is an ambitious test case; `A_4` and `Dic_3` are the first unresolved order-12 cases in the surveyed finite-group ladder.
- Cohomology is a proposed search language, not an established invariant of generalized star-height.

## Required workflow

1. Restate the exact claim and its quantifiers.
2. Classify every input fact as `PROVED`, `CITED`, `COMPUTED`, `CONJECTURAL`, or `SPECULATIVE`.
3. Explore before editing. Name the smallest files that need changes.
4. Write an acceptance test before substantial code or proof text.
5. Work on one branch/worktree per approach.
6. Run `./scripts/check.sh` after Lean changes. If toolchain setup is unavailable, state that explicitly and perform only static checks.
7. Update `CLAIMS_LEDGER.md` and `PROOF_OBLIGATIONS.md` with exact locations.
8. Return a concise result packet: claim, artifact paths, tests run, remaining gap, and one recommended next action.

## Forbidden shortcuts

- No `axiom` declarations.
- No silent use of `Classical.choice`, excluded middle, or quotient choice when a constructive theorem is claimed.
- No replacement of a language by a finite sample without a certificate explaining soundness.
- No appeal to a named theorem without a precise statement and citation or a Lean declaration path.
- No “routine”, “clearly”, or “standard” for a step that carries the main burden.
- No changing theorem statements merely to make Lean accept them without recording the change.
- No deleting failed approaches from the registry; mark them `BLOCKED` with the exact obstruction.

## Lean conventions

- Prefer semantic definitions over syntax-directed shortcuts.
- Use explicit namespaces and minimal imports once the API stabilizes.
- Keep executable definitions separate from theorem interfaces.
- Mark provisional theorem statements with `-- BLUEPRINT:` and register every `sorry` in `PROOF_OBLIGATIONS.md`.
- Add `[simp]` only when the rewrite is terminating and unsurprising.
- Prove word/list lemmas before quotient constructions.
- Certificates must have a checker with a theorem of soundness; do not trust generated expressions directly.

## Agent parallelism

Parallelize read-heavy work (literature, API reconnaissance, independent proof search, counterexample testing). Be conservative with simultaneous edits. Preserve early independence: do not tell every agent the currently favored proof idea. The orchestrator may cross-pollinate only after each route has returned its strongest lemma and its sharpest failure.

## Stop conditions

Stop and return `BLOCKED` when:

- the missing lemma is equivalent in strength to the original target;
- three materially identical repairs have failed;
- the task requires an undefined notion or an unverified citation;
- the branch no longer has an executable acceptance test;
- the token/time budget is below the amount needed for one full verify-and-repair cycle.
