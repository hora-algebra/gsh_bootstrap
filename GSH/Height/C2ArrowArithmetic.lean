import GSH.Height.C2PairTransfer
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Arithmetic reconstruction of a source-zero moving arrow

For an even two-state run, twice the number of occurrences of a phase-one
letter read at state zero equals its ordinary count plus a signed balance of
the distinct consecutive phase-one pairs.  The identity is valid in every
`ZMod modulus`; choosing `modulus = 2 * m` recovers the source-zero count
modulo `m` without assuming that two is invertible.
-/

set_option autoImplicit false

namespace GSH
namespace C2ArrowArithmetic

open ArrowCounting
open C2PairTransfer

universe u

variable {β : Type u} [DecidableEq β]

/-- Every letter toggles the two-state run. -/
def allFlipStep (state : ZMod 2) (_ : β) : ZMod 2 := state + 1

@[simp] theorem allFlipStep_zero (a : β) : allFlipStep 0 a = 1 := by
  simp [allFlipStep]

@[simp] theorem allFlipStep_one (a : β) : allFlipStep 1 a = 0 := by
  exact CharTwo.add_self_eq_zero 1

section Finite

variable [Fintype β]

/-- Signed balance of distinct fixed pair counts around `label`. -/
def pairBalance (modulus : Nat) (label : β) (word : Word β) : ZMod modulus :=
  ∑ other : β,
    if other = label then 0
    else
      (pairCountOf label other word : ZMod modulus) -
        (pairCountOf other label word : ZMod modulus)

private theorem sum_other_indicator (modulus : Nat)
    (label value : β) (h : value ≠ label) :
    (∑ other : β,
      if other = label then 0
      else if value = other then (1 : ZMod modulus) else 0) = 1 := by
  calc
    _ = ∑ other : β, if value = other then (1 : ZMod modulus) else 0 := by
      apply Finset.sum_congr rfl
      intro other _
      by_cases hv : value = other
      · subst other
        simp [h]
      · simp [hv]
    _ = 1 := by simp

private theorem sum_other_neg_indicator (modulus : Nat)
    (label value : β) (h : value ≠ label) :
    (∑ other : β,
      if other = label then 0
      else -if value = other then (1 : ZMod modulus) else 0) = -1 := by
  calc
    _ = -(∑ other : β,
          if other = label then 0
          else if value = other then (1 : ZMod modulus) else 0) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro other _
      by_cases ho : other = label <;> simp [ho]
    _ = -1 := by rw [sum_other_indicator modulus label value h]

private theorem pairBalance_cons_cons (modulus : Nat)
    (label a b : β) (word : Word β) :
    pairBalance modulus label (a :: b :: word) =
      (if a = label ∧ b ≠ label then 1 else 0) -
        (if a ≠ label ∧ b = label then 1 else 0) +
          pairBalance modulus label word := by
  classical
  unfold pairBalance
  calc
    (∑ other : β,
        if other = label then 0
        else
          (pairCountOf label other (a :: b :: word) : ZMod modulus) -
            (pairCountOf other label (a :: b :: word) : ZMod modulus)) =
      (∑ other : β,
        if other = label then 0
        else
          ((if a = label ∧ b = other then 1 else 0) : ZMod modulus) -
            ((if a = other ∧ b = label then 1 else 0) : ZMod modulus)) +
      ∑ other : β,
        if other = label then 0
        else
          (pairCountOf label other word : ZMod modulus) -
            (pairCountOf other label word : ZMod modulus) := by
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
          ∑ other : β,
            if other = label then 0
            else
              (pairCountOf label other word : ZMod modulus) -
                (pairCountOf other label word : ZMod modulus) := by
        congr 1
        by_cases ha : a = label
        · by_cases hb : b = label
          · subst a
            subst b
            simp
          · subst a
            simpa [hb] using sum_other_indicator modulus label b hb
        · by_cases hb : b = label
          · subst b
            simpa [ha] using sum_other_neg_indicator modulus label a ha
          · simp [ha, hb]

/-- Pure all-toggle arithmetic, valid for every modulus. -/
theorem two_mul_allFlipArrow_eq_count_add_pairBalance
    (modulus : Nat) (label : β) (word : Word β)
    (hEven : word.length % 2 = 0) :
    (2 : ZMod modulus) *
        (arrowCountFrom allFlipStep 0 0 label word : ZMod modulus) =
      (word.count label : ZMod modulus) + pairBalance modulus label word := by
  induction word using List.twoStepInduction with
  | nil => simp [pairBalance, pairCountOf]
  | singleton a => simp at hEven
  | cons_cons a b word ih _ =>
      have hTail : word.length % 2 = 0 := by
        change (word.length + 2) % 2 = 0 at hEven
        simpa only [Nat.add_mod_right] using hEven
      have ih' := ih hTail
      rw [pairBalance_cons_cons]
      by_cases ha : a = label <;> by_cases hb : b = label <;>
        simp [arrowCountFrom, allFlipStep_zero, allFlipStep_one,
          ha, hb] at ih' ⊢ <;>
        first
        | (ring; done)
        | linear_combination ih'

end Finite

section Filter

variable {α : Type u} [Fintype α] [DecidableEq α]
variable (phase : α → ZMod 2)

local instance : BEq (C2PairTransfer.PhaseOne phase) :=
  instBEqOfDecidableEq

private theorem phase_zero_of_ne_one (a : α) (ha : phase a ≠ 1) :
    phase a = 0 := by
  have hval : (phase a).val = 0 ∨ (phase a).val = 1 := by
    have := ZMod.val_lt (phase a)
    omega
  rcases hval with hval | hval
  · apply ZMod.val_injective 2
    simpa [hval]
  · exfalso
    apply ha
    apply ZMod.val_injective 2
    simpa [hval, ZMod.val_one]

private theorem count_phaseOneSubword (label : C2PairTransfer.PhaseOne phase)
    (word : Word α) :
    (C2PairTransfer.phaseOneSubword phase word).count label =
      word.count label.1 := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      by_cases ha : phase a = 1
      · by_cases hal : a = label.1
        · subst a
          simp [C2PairTransfer.phaseOneSubword, label.2, ih]
        · have hsub : (⟨a, ha⟩ : C2PairTransfer.PhaseOne phase) ≠ label := by
            intro h
            exact hal (congrArg Subtype.val h)
          simp [C2PairTransfer.phaseOneSubword, ha, hal, hsub, ih]
      · have hal : a ≠ label.1 := by
          intro h
          subst a
          exact ha label.2
        simp [C2PairTransfer.phaseOneSubword, ha, hal, ih]

private theorem arrowCount_phaseOneSubword
    (label : C2PairTransfer.PhaseOne phase) :
    ∀ (start : ZMod 2) (word : Word α),
      arrowCountFrom (c2Step phase) start 0 label.1 word =
        arrowCountFrom allFlipStep start 0 label
          (C2PairTransfer.phaseOneSubword phase word) := by
  intro start word
  induction word generalizing start with
  | nil => rfl
  | cons a word ih =>
      by_cases ha : phase a = 1
      · have hstep : c2Step phase start a = allFlipStep start a := by
          simp [c2Step, allFlipStep, ha]
        by_cases hal : a = label.1
        · subst a
          simp [arrowCountFrom, C2PairTransfer.phaseOneSubword,
            label.2, hstep, ih, allFlipStep]
        · have hsub : (⟨a, ha⟩ : C2PairTransfer.PhaseOne phase) ≠ label := by
            intro h
            exact hal (congrArg Subtype.val h)
          simp [arrowCountFrom, C2PairTransfer.phaseOneSubword,
            ha, hal, hsub, hstep, ih, allFlipStep]
      · have ha0 := phase_zero_of_ne_one phase a ha
        have hal : a ≠ label.1 := by
          intro h
          subst a
          exact ha label.2
        simp [arrowCountFrom, C2PairTransfer.phaseOneSubword,
          ha, ha0, hal, c2Step, ih]

/-- Exact moving-arrow identity on the original alphabet. -/
theorem two_mul_evenArrow_eq_count_add_pairBalance
    (modulus : Nat) (label : C2PairTransfer.PhaseOne phase)
    (word : Word α) (hphase : (word.map phase).sum = 0) :
    (2 : ZMod modulus) *
        (arrowCountFrom (c2Step phase) 0 0 label.1 word : ZMod modulus) =
      (word.count label.1 : ZMod modulus) +
        pairBalance modulus label (C2PairTransfer.phaseOneSubword phase word) := by
  have heven : (C2PairTransfer.phaseOneSubword phase word).length % 2 = 0 :=
    (C2PairTransfer.phaseOneSubword_even_iff_phase_sum_zero
      (phase := phase) word).2 hphase
  have h := C2ArrowArithmetic.two_mul_allFlipArrow_eq_count_add_pairBalance
    modulus label (C2PairTransfer.phaseOneSubword phase word) heven
  rw [← arrowCount_phaseOneSubword phase label 0 word] at h
  have hcount :
      ((C2PairTransfer.phaseOneSubword phase word).count label : ZMod modulus) =
        (word.count label.1 : ZMod modulus) :=
    congrArg (fun n : Nat => (n : ZMod modulus))
      (count_phaseOneSubword phase label word)
  calc
    _ = ((C2PairTransfer.phaseOneSubword phase word).count label : ZMod modulus) +
          pairBalance modulus label
            (C2PairTransfer.phaseOneSubword phase word) := h
    _ = (word.count label.1 : ZMod modulus) +
          pairBalance modulus label
            (C2PairTransfer.phaseOneSubword phase word) :=
      congrArg (fun z => z + pairBalance modulus label
        (C2PairTransfer.phaseOneSubword phase word)) hcount

end Filter

end C2ArrowArithmetic
end GSH
