import GSH

/-!
# Acceptance tests for the two-letter scattered-subword count

`GSH/Height/Nilpotent2.lean` proves theorems *about* `binom2` and `stage`.  A
wrong definition would make those theorems true and worthless, so this file
pins both definitions down on concrete words before any height claim is used.

The tests that matter most are the **asymmetry** checks: `binom(w, ab)` counts
pairs `i < j`, so it must distinguish `ab` from `ba`.  A definition that
counted unordered pairs, or adjacent factors instead of scattered subwords,
would pass a symmetric test suite and fail these.
-/

set_option autoImplicit false

namespace GSHTest

open GSH
open GSH.Nilpotent2

/-! ### `binom2` counts scattered, ordered pairs

Alphabet `Bool`; read `true` as the letter `a` and `false` as the letter `b`. -/

/-- Order matters: `ab` has one scattered `ab`, `ba` has none. -/
example : binom2 true false [true, false] = 1 := by decide

example : binom2 true false [false, true] = 0 := by decide

/-- Scattered, not adjacent: `a x b` still counts, with `x` a third letter.
Encoded here as `a a b`, whose two `a`s each pair with the single `b`. -/
example : binom2 true false [true, true, false] = 2 := by decide

/-- `abab` has three scattered occurrences of `ab`: `(1,2)`, `(1,4)`, `(3,4)`. -/
example : binom2 true false [true, false, true, false] = 3 := by decide

/-- `baba` has one: only the `a` at position 2 precedes the `b` at position 3. -/
example : binom2 true false [false, true, false, true] = 1 := by decide

/-- The empty word and single letters have no pairs. -/
example : binom2 true false ([] : Word Bool) = 0 := by decide

example : binom2 true false [true] = 0 := by decide

/-! ### The diagonal case `a = b` is the triangular number -/

example : binom2 true true [true, true, true] = 3 := by decide

example : binom2 true true [true, true, true] = tri 3 := by decide

example : tri 4 = 6 := by decide

/-! ### `stage` splits the count by the residue of the preceding `a`-count

For `w = abab` and `n = 2`: the first `b` has one preceding `a` (stage 1), the
second `b` has two (stage 0).  So `stage_0 = stage_1 = 1`, and
`0 * 1 + 1 * 1 = 1 = 3 % 2 = binom2 % 2`, which is `binom2_mod_eq_sum`. -/

example : stage true false 2 0 0 [true, false, true, false] = 1 := by decide

example : stage true false 2 1 0 [true, false, true, false] = 1 := by decide

/-- A word where the two stages differ, so the decomposition is not trivial. -/
example : stage true false 2 0 0 [false, true, false] = 1 := by decide

example : stage true false 2 1 0 [false, true, false] = 1 := by decide

example : stage true false 3 0 0 [false, false, true, false] = 2 := by decide

example : stage true false 3 1 0 [false, false, true, false] = 1 := by decide

/-! ### The proved height bounds

The `a = b` case is complete; these are its concrete instances.  The
`Counting.cnt` smoke test in `GSHTest/Smoke.lean` already records that the
underlying single-letter expression genuinely contains a star, so the bound
`≤ 1` is not a disguised star-freeness claim. -/

example : HasHeightAtMost {w : Word Bool | binom2 true true w % 2 = 0} 1 :=
  hasHeightAtMost_binom2_self true (by norm_num)

example : HasHeightAtMost {w : Word Bool | binom2 false false w % 3 = 2} 1 :=
  hasHeightAtMost_binom2_self false (by norm_num)

/-! ### The `a ≠ b` case is reduced, not proved

`hasHeightAtMost_binom2_of_stage` still carries the stage hypothesis.  This
`example` records the exact shape of the missing input — Pin–Straubing–Thérien
Proposition 6.6 — so that a future proof of it closes the case by discharging
one argument and nothing else. -/

example
    (hstage : ∀ k c : Nat, k < 2 → c < 2 →
      HasHeightAtMost {w : Word Bool | stage true false 2 k 0 w % 2 = c} 1) :
    HasHeightAtMost {w : Word Bool | binom2 true false w % 2 = 0} 1 :=
  hasHeightAtMost_binom2_of_stage true false (by norm_num) hstage

end GSHTest
