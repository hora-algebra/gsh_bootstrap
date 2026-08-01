import GSH.Height.ArrowCounting
import Mathlib.Data.List.Induction

/-!
# Two-letter pair bookkeeping for the `S₃` route

This file records the elementary, word-level part of the two-state argument.
Words are read two letters at a time.  `pairCount x y` counts the blocks
`[x, y]` in that fixed factorization; it is not the overlapping subword count.

No generalized-star-height claim is made here.  In particular, this file does
not import the disputed final substitution step in the published proof of the
two-state arrow-counting result.
-/

set_option autoImplicit false

namespace GSH

namespace PairCode

open ArrowCounting

/-- The number of occurrences of `[x, y]` when a Boolean word is split into
consecutive blocks of length two from the left.  A final unpaired letter is
ignored. -/
def pairCount (x y : Bool) : Word Bool → Nat
  | a :: b :: word =>
      (if a = x ∧ b = y then 1 else 0) + pairCount x y word
  | _ => 0

@[simp]
theorem pairCount_nil (x y : Bool) : pairCount x y [] = 0 := rfl

@[simp]
theorem pairCount_singleton (x y a : Bool) : pairCount x y [a] = 0 := rfl

@[simp]
theorem pairCount_cons_cons (x y a b : Bool) (word : Word Bool) :
    pairCount x y (a :: b :: word) =
      (if a = x ∧ b = y then 1 else 0) + pairCount x y word := rfl

/-- Both input letters toggle the state of the two-state automaton. -/
def allFlipStep (state : ZMod 2) (_ : Bool) : ZMod 2 :=
  state + 1

@[simp]
theorem allFlipStep_zero (a : Bool) : allFlipStep 0 a = 1 := by
  simp [allFlipStep]

@[simp]
theorem allFlipStep_one (a : Bool) : allFlipStep 1 a = 0 := by
  exact CharTwo.add_self_eq_zero 1

/-- On an even-length word, arrows with source state `0` and a fixed label are
exactly the length-two blocks whose first letter has that label. -/
theorem arrowCount_allFlip_zero_even (label : Bool) (word : Word Bool)
    (hEven : word.length % 2 = 0) :
    arrowCountFrom allFlipStep 0 0 label word =
      pairCount label false word + pairCount label true word := by
  induction word using List.twoStepInduction with
  | nil => simp
  | singleton a => simp at hEven
  | cons_cons a b word ih _ =>
      have hTail : word.length % 2 = 0 := by
        change (word.length + 2) % 2 = 0 at hEven
        simpa only [Nat.add_mod_right] using hEven
      have ih' := ih hTail
      cases a <;> cases b <;> cases label <;>
        simp [arrowCountFrom, pairCount, ih'] <;> omega

/-- On an even-length Boolean word, ordinary occurrences of `false` are the
sum of their occurrences in the four possible length-two blocks. -/
theorem count_false_eq_pairCounts (word : Word Bool)
    (hEven : word.length % 2 = 0) :
    word.count false =
      2 * pairCount false false word +
        pairCount false true word + pairCount true false word := by
  induction word using List.twoStepInduction with
  | nil => simp
  | singleton a => simp at hEven
  | cons_cons a b word ih _ =>
      have hTail : word.length % 2 = 0 := by
        change (word.length + 2) % 2 = 0 at hEven
        simpa only [Nat.add_mod_right] using hEven
      have ih' := ih hTail
      cases a <;> cases b <;> simp [pairCount, ih'] <;> omega

end PairCode

end GSH
