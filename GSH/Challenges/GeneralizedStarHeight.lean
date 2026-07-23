import GSH.Blueprint

/-!
# Generalized star-height conjecture

Let `α` be a finite alphabet. Generalized regular expressions over `α` are
built from the empty language, the empty word, and letters using union,
concatenation, complement relative to `α*`, and Kleene star. The generalized
star height of a language is the least nesting depth of Kleene star among all
generalized regular expressions denoting that language.

The challenge below is the **height-one collapse conjecture**: every regular
language over a finite alphabet has generalized star height at most one. It is
not the distinct algorithmic problem of computing the exact generalized star
height of an input regular language.

## Expanded statement

`GeneralizedHeightOneConjecture` unfolds to

```text
∀ (α : Type u) [Fintype α],
  ∀ L : Language α,
    IsRegular L → HasHeightAtMost L 1
```

and `HasHeightAtMost L 1` means that there is a generalized regular expression
`r` with `r.denote = L` and `r.starHeight ≤ 1`.

## Statement-audit notes

* `Language α` is `Set (List α)`, so complement is relative to the fixed free
  monoid `α*`.
* `IsRegular L` currently means that `L` is denoted by some generalized regular
  expression. Connecting this definition to DFA regularity is a separate
  formalization target.
* The empty alphabet is included. This adds only a trivial boundary case and
  avoids a mathematically inessential `Nonempty α` assumption.
* No `DecidableEq α` assumption is included because the proposition and its
  current definitions do not use one.
* This file records an open challenge. The declaration below is not evidence
  that the conjecture has been proved.

## References

* J.-É. Pin, H. Straubing, and D. Thérien,
  *Some Results on the Generalized Star-Height Problem*, Information and
  Computation 101 (1992), 219–250.
  https://hal.science/hal-00019978
* J.-É. Pin, *Open Problems about Regular Languages, 35 Years Later*,
  Theoretical Computer Science 701 (2017), 23–46.
  https://hal.science/hal-01614375
* T. Bourne, *Counting Subwords and Other Results Related to the Generalised
  Star-Height Problem for Regular Languages*, PhD thesis (2017).
  https://research-repository.st-andrews.ac.uk/handle/10023/12024
-/

set_option autoImplicit false

namespace GSH

/--
Every regular language over every finite alphabet has generalized star height
at most one.

This is the height-one collapse conjecture, not the full decision problem for
computing exact generalized star height.
-/
-- BLUEPRINT: L-GSH-CHALLENGE-001
theorem generalized_star_height_conjecture : GeneralizedHeightOneConjecture := by
  sorry

end GSH
