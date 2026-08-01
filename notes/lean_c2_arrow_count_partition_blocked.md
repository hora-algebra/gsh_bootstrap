# C2 arrow-count partition: bounded Lean failure

## Intended theorem

For every type `α` with decidable equality, phase map `phase : α → ZMod 2`,
starting state, letter, and word, the occurrences of that letter partition by
the source state of the two-state run:

```lean
theorem c2ArrowCount_sum_sources [DecidableEq α] (phase : α → ZMod 2)
    (start : ZMod 2) (label : α) (word : Word α) :
    arrowCountFrom (c2Step phase) start 0 label word +
        arrowCountFrom (c2Step phase) start 1 label word =
      word.count label
```

This is word-level bookkeeping.  It makes no generalized-star-height claim.
The inputs `arrowCountFrom`, `c2Step_twice`, and `c2RunFrom_eq` are `PROVED`;
PST-GRP-03 is `CITED`; L-ABC2-001 and M-PST-003 remain `OPEN`.

## Reproduction

Add the theorem above to `GSH/Height/ArrowCounting.lean`, import
`Mathlib.Data.List.Count`, add a compile-time use to
`GSHTest/ArrowCounting.lean`, and run:

```text
lake build GSH.Height.ArrowCounting GSHTest.ArrowCounting
```

Induction on `word`, followed by `fin_cases start` and a split on
`a = label`, reduces all recursive content using the induction hypothesis.
After three materially similar repair attempts (`simp`; explicit
`zero_ne_one` / `one_ne_zero`; substitution of `a = label`), Lean still leaves
one of the following concrete indicator goals:

```lean
((if 0 = 0 ∧ label = label then 1 else 0) +
  if 0 = 1 ∧ label = label then 1 else 0) = 1

((if 1 = 0 ∧ label = label then 1 else 0) +
  if 1 = 1 ∧ label = label then 1 else 0) = 1
```

The theorem is not refuted; the bounded attempt is stopped by the
three-repair condition in `AGENTS.md`.  No failing Lean source is committed.

## Next distinct repair

Prove a separate two-state indicator lemma by explicit `if_pos` / `if_neg`
rewrites, without asking `simp` to normalize the `ZMod 2` equalities.  Use that
lemma in the word induction.  Acceptance is the exact theorem above together
with the universal example in `GSHTest/ArrowCounting.lean` and a passing
`./scripts/check.sh`.
