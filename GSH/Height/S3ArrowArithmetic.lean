import GSH.Height.ArrowCounting
import GSH.Height.S3FullFiber
import Mathlib.Data.List.Induction
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The phase-one pair-balance identity for the `S₃` route

This file proves only the finite word arithmetic used by the moving-edge case.
The alphabet is arbitrary and finite; specializing it to the three phase-one
letters of `S₃` gives the required identity.  All arithmetic in the
conclusion is in `ZMod 3`.

No generalized-star-height conclusion is made here.
-/

set_option autoImplicit false

namespace GSH

namespace S3ArrowArithmetic

open ArrowCounting

universe u

variable {α : Type u}

section PairCounts

variable [DecidableEq α]

/-- The number of occurrences of `[x, y]` in the fixed factorization of a word
into consecutive blocks of length two.  A final singleton is ignored. -/
def pairCountOf (x y : α) : Word α → Nat
  | a :: b :: word =>
      (if a = x ∧ b = y then 1 else 0) + pairCountOf x y word
  | _ => 0

@[simp]
theorem pairCountOf_nil (x y : α) : pairCountOf x y [] = 0 := rfl

@[simp]
theorem pairCountOf_singleton (x y a : α) : pairCountOf x y [a] = 0 := rfl

@[simp]
theorem pairCountOf_cons_cons (x y a b : α) (word : Word α) :
    pairCountOf x y (a :: b :: word) =
      (if a = x ∧ b = y then 1 else 0) + pairCountOf x y word := rfl

/-- Every letter toggles the two-state run. -/
def allFlipStepOf (state : ZMod 2) (_ : α) : ZMod 2 :=
  state + 1

omit [DecidableEq α] in
@[simp]
theorem allFlipStepOf_zero (a : α) : allFlipStepOf 0 a = 1 := by
  simp [allFlipStepOf]

omit [DecidableEq α] in
@[simp]
theorem allFlipStepOf_one (a : α) : allFlipStepOf 1 a = 0 := by
  exact CharTwo.add_self_eq_zero 1

section Finite

variable [Fintype α]

/-- The signed sum of fixed pair counts over every letter other than `label`. -/
def pairBalance (label : α) (word : Word α) : ZMod 3 :=
  ∑ other : α,
    if other = label then 0
    else
      (pairCountOf label other word : ZMod 3) -
        (pairCountOf other label word : ZMod 3)

private theorem sum_other_indicator (label value : α) (h : value ≠ label) :
    (∑ other : α,
      if other = label then 0
      else if value = other then (1 : ZMod 3) else 0) = 1 := by
  calc
    _ = ∑ other : α, if value = other then (1 : ZMod 3) else 0 := by
      apply Finset.sum_congr rfl
      intro other _
      by_cases hv : value = other
      · subst other
        simp [h]
      · simp [hv]
    _ = 1 := by simp

private theorem sum_other_neg_indicator (label value : α) (h : value ≠ label) :
    (∑ other : α,
      if other = label then 0
      else -if value = other then (1 : ZMod 3) else 0) = -1 := by
  calc
    _ =
        -(∑ other : α,
          if other = label then 0
          else if value = other then (1 : ZMod 3) else 0) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro other _
      by_cases ho : other = label <;> simp [ho]
    _ = -1 := by rw [sum_other_indicator label value h]

private theorem pairBalance_cons_cons (label a b : α) (word : Word α) :
    pairBalance label (a :: b :: word) =
      (if a = label ∧ b ≠ label then 1 else 0) -
        (if a ≠ label ∧ b = label then 1 else 0) +
          pairBalance label word := by
  classical
  unfold pairBalance
  calc
    (∑ other : α,
        if other = label then 0
        else
          (pairCountOf label other (a :: b :: word) : ZMod 3) -
            (pairCountOf other label (a :: b :: word) : ZMod 3)) =
      (∑ other : α,
        if other = label then 0
        else
          ((if a = label ∧ b = other then 1 else 0) : ZMod 3) -
            ((if a = other ∧ b = label then 1 else 0) : ZMod 3)) +
      ∑ other : α,
        if other = label then 0
        else
          (pairCountOf label other word : ZMod 3) -
            (pairCountOf other label word : ZMod 3) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro other _
        by_cases ho : other = label
        · simp [ho]
        · simp [pairCountOf, ho]
          ring
    _ =
      (if a = label ∧ b ≠ label then 1 else 0) -
        (if a ≠ label ∧ b = label then 1 else 0) +
          ∑ other : α,
            if other = label then 0
            else
              (pairCountOf label other word : ZMod 3) -
                (pairCountOf other label word : ZMod 3) := by
        congr 1
        by_cases ha : a = label
        · by_cases hb : b = label
          · subst a
            subst b
            simp
          · subst a
            simpa [hb] using sum_other_indicator label b hb
        · by_cases hb : b = label
          · subst b
            simpa [ha] using sum_other_neg_indicator label a ha
          · simp [ha, hb]

/-- Exact phase-one identity for the all-toggle two-state run.  The alphabet,
label, and even word are universally quantified. -/
theorem two_mul_evenArrow_eq_count_add_pairBalance
    (label : α) (word : Word α)
    (hEven : word.length % 2 = 0) :
    (2 : ZMod 3) *
        (arrowCountFrom allFlipStepOf 0 0 label word : ZMod 3) =
      (word.count label : ZMod 3) + pairBalance label word := by
  induction word using List.twoStepInduction with
  | nil => simp [pairBalance]
  | singleton a => simp at hEven
  | cons_cons a b word ih _ =>
      have hTail : word.length % 2 = 0 := by
        change (word.length + 2) % 2 = 0 at hEven
        simpa only [Nat.add_mod_right] using hEven
      have ih' := ih hTail
      rw [pairBalance_cons_cons]
      by_cases ha : a = label <;> by_cases hb : b = label <;>
        simp [arrowCountFrom, allFlipStepOf_zero, allFlipStepOf_one,
          ha, hb] at ih' ⊢ <;>
        first
        | (ring; done)
        | linear_combination ih'

end Finite

end PairCounts

/-! ### Connection to the actual six-letter `S₃` alphabet -/

/-- The three `S₃` letters that move between the two phase states. -/
abbrev S3PhaseOne := {p : S3Alphabet // s3Phase p = 1}

local instance : BEq S3PhaseOne := instBEqOfDecidableEq

/-- Erase the phase-zero letters and retain each moving letter together with
its proof of phase one. -/
def phaseOneSubword : Word S3Alphabet → Word S3PhaseOne
  | [] => []
  | p :: word =>
      if hp : s3Phase p = 1 then
        ⟨p, hp⟩ :: phaseOneSubword word
      else
        phaseOneSubword word

/-- The number of retained letters, cast to `ZMod 2`, is the phase sum of the
original word. -/
theorem phaseOneSubword_length_cast (word : Word S3Alphabet) :
    ((phaseOneSubword word).length : ZMod 2) =
      (word.map s3Phase).sum := by
  induction word with
  | nil => simp [phaseOneSubword]
  | cons p word ih =>
      by_cases hs : Equiv.Perm.sign p = 1 <;>
        simp [phaseOneSubword, s3Phase, hs, ih, add_comm]

/-- The retained phase-one word has even length exactly when the original
word has total phase zero. -/
theorem phaseOneSubword_even_iff_phase_sum_zero (word : Word S3Alphabet) :
    (phaseOneSubword word).length % 2 = 0 ↔
      (word.map s3Phase).sum = 0 := by
  rw [← phaseOneSubword_length_cast]
  simpa [Nat.dvd_iff_mod_eq_zero] using
    (ZMod.natCast_eq_zero_iff (phaseOneSubword word).length 2).symm

/-- Filtering to phase-one letters preserves the ordinary count of a chosen
phase-one label. -/
theorem count_phaseOneSubword (label : S3Alphabet)
    (hlabel : s3Phase label = 1) (word : Word S3Alphabet) :
    (phaseOneSubword word).count ⟨label, hlabel⟩ = word.count label := by
  induction word with
  | nil => simp [phaseOneSubword]
  | cons p word ih =>
      by_cases hp : s3Phase p = 1
      · by_cases hpl : p = label
        · subst p
          simp [phaseOneSubword, hlabel, ih]
        · simp [phaseOneSubword, hp, hpl, ih]
      · have hne : p ≠ label := by
          intro h
          subst p
          exact hp hlabel
        simp [phaseOneSubword, hp, hne, ih]

/-- Erasing phase-zero letters preserves every labelled arrow count in the
two-state run; the retained word uses the all-toggle transition. -/
private theorem arrowCount_phaseOneSubword_from (start : ZMod 2)
    (label : S3Alphabet) (hlabel : s3Phase label = 1)
    (word : Word S3Alphabet) :
    arrowCountFrom (c2Step s3Phase) start 0 label word =
      arrowCountFrom allFlipStepOf start 0 ⟨label, hlabel⟩
        (phaseOneSubword word) := by
  induction word generalizing start with
  | nil => simp [phaseOneSubword]
  | cons p word ih =>
      by_cases hp : s3Phase p = 1
      · by_cases hpl : p = label
        · subst p
          simp [phaseOneSubword, hlabel, arrowCountFrom, c2Step,
            allFlipStepOf, ih]
        · simp [phaseOneSubword, hp, hpl, arrowCountFrom, c2Step,
            allFlipStepOf, ih]
      · have hp0 : s3Phase p = 0 := by
          by_cases hs : Equiv.Perm.sign p = 1
          · simp [s3Phase, hs]
          · exact False.elim (hp (by simp [s3Phase, hs]))
        have hne : p ≠ label := by
          intro h
          subst p
          exact hp hlabel
        simp [phaseOneSubword, arrowCountFrom, c2Step, hp0, hne, ih]

/-- Source-zero `S₃` arrow counts for a phase-one label are exactly the
all-toggle arrow counts of the retained phase-one subword. -/
theorem s3ArrowCountFrom_eq_phaseOneSubword (label : S3Alphabet)
    (hlabel : s3Phase label = 1) (word : Word S3Alphabet) :
    s3ArrowCountFrom 0 0 label word =
      arrowCountFrom allFlipStepOf 0 0 ⟨label, hlabel⟩
        (phaseOneSubword word) := by
  exact arrowCount_phaseOneSubword_from 0 label hlabel word

/-- The generic pair-balance identity transported to the actual `S₃`
alphabet. -/
theorem two_mul_s3Arrow_eq_count_add_pairBalance
    (label : S3Alphabet) (hlabel : s3Phase label = 1)
    (word : Word S3Alphabet) (hphase : (word.map s3Phase).sum = 0) :
    (2 : ZMod 3) * (s3ArrowCountFrom 0 0 label word : ZMod 3) =
      (word.count label : ZMod 3) +
        pairBalance ⟨label, hlabel⟩ (phaseOneSubword word) := by
  have hEven : (phaseOneSubword word).length % 2 = 0 :=
    (phaseOneSubword_even_iff_phase_sum_zero word).2 hphase
  rw [s3ArrowCountFrom_eq_phaseOneSubword label hlabel word]
  rw [two_mul_evenArrow_eq_count_add_pairBalance ⟨label, hlabel⟩
    (phaseOneSubword word) hEven]
  rw [count_phaseOneSubword label hlabel word]

end S3ArrowArithmetic

end GSH
