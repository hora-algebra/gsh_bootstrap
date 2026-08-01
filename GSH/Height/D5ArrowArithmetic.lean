import GSH.Height.D5ArrowCoordinates
import GSH.Height.D5FlipPairTransfer
import GSH.Height.S3ArrowArithmetic

/-!
# Mod-five pair arithmetic for phase-one `D₅` letters

On an even word all letters toggle the two-state prefix run.  Twice the
source-zero count of a label is its ordinary count plus the signed imbalance
of the ordered length-two blocks incident with that label.  We retain the
identity in `ZMod 5`, where multiplication by two is invertible.
-/

set_option autoImplicit false

namespace GSH

namespace D5ArrowArithmetic

open ArrowCounting
open S3ArrowArithmetic
open D5FlipPairTransfer

local instance : BEq D5PhaseOne := instBEqOfDecidableEq

/-- Signed distinct-pair imbalance modulo five. -/
def d5PairBalance5 (label : D5PhaseOne) (word : Word D5PhaseOne) : ZMod 5 :=
  ∑ other : D5PhaseOne,
    if other = label then 0
    else
      (pairCountOf label other word : ZMod 5) -
        (pairCountOf other label word : ZMod 5)

private theorem sum_other_indicator5 (label value : D5PhaseOne)
    (h : value ≠ label) :
    (∑ other : D5PhaseOne,
      if other = label then 0
      else if value = other then (1 : ZMod 5) else 0) = 1 := by
  calc
    _ = ∑ other : D5PhaseOne,
        if value = other then (1 : ZMod 5) else 0 := by
      apply Finset.sum_congr rfl
      intro other _
      by_cases hv : value = other
      · subst other
        simp [h]
      · simp [hv]
    _ = 1 := by simp

private theorem sum_other_neg_indicator5 (label value : D5PhaseOne)
    (h : value ≠ label) :
    (∑ other : D5PhaseOne,
      if other = label then 0
      else -if value = other then (1 : ZMod 5) else 0) = -1 := by
  calc
    _ =
        -(∑ other : D5PhaseOne,
          if other = label then 0
          else if value = other then (1 : ZMod 5) else 0) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro other _
      by_cases ho : other = label <;> simp [ho]
    _ = -1 := by rw [sum_other_indicator5 label value h]

private theorem d5PairBalance5_cons_cons
    (label a b : D5PhaseOne) (word : Word D5PhaseOne) :
    d5PairBalance5 label (a :: b :: word) =
      (if a = label ∧ b ≠ label then 1 else 0) -
        (if a ≠ label ∧ b = label then 1 else 0) +
          d5PairBalance5 label word := by
  classical
  unfold d5PairBalance5
  calc
    (∑ other : D5PhaseOne,
        if other = label then 0
        else
          (pairCountOf label other (a :: b :: word) : ZMod 5) -
            (pairCountOf other label (a :: b :: word) : ZMod 5)) =
      (∑ other : D5PhaseOne,
        if other = label then 0
        else
          ((if a = label ∧ b = other then 1 else 0) : ZMod 5) -
            ((if a = other ∧ b = label then 1 else 0) : ZMod 5)) +
      ∑ other : D5PhaseOne,
        if other = label then 0
        else
          (pairCountOf label other word : ZMod 5) -
            (pairCountOf other label word : ZMod 5) := by
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
          ∑ other : D5PhaseOne,
            if other = label then 0
            else
              (pairCountOf label other word : ZMod 5) -
                (pairCountOf other label word : ZMod 5) := by
        congr 1
        by_cases ha : a = label
        · by_cases hb : b = label
          · subst a
            subst b
            simp
          · subst a
            simpa [hb] using sum_other_indicator5 label b hb
        · by_cases hb : b = label
          · subst b
            simpa [ha] using sum_other_neg_indicator5 label a ha
          · simp [ha, hb]

/-- Exact phase-one identity in `ZMod 5`. -/
private theorem two_mul_evenArrow_eq_count_add_d5PairBalance5
    (label : D5PhaseOne) (word : Word D5PhaseOne)
    (hEven : word.length % 2 = 0) :
    (2 : ZMod 5) *
        (arrowCountFrom allFlipStepOf 0 0 label word : ZMod 5) =
      (word.count label : ZMod 5) + d5PairBalance5 label word := by
  induction word using List.twoStepInduction with
  | nil => simp [d5PairBalance5]
  | singleton a => simp at hEven
  | cons_cons a b word ih _ =>
      have hTail : word.length % 2 = 0 := by
        change (word.length + 2) % 2 = 0 at hEven
        simpa only [Nat.add_mod_right] using hEven
      have ih' := ih hTail
      rw [d5PairBalance5_cons_cons]
      by_cases ha : a = label <;> by_cases hb : b = label <;>
        simp [arrowCountFrom, allFlipStepOf_zero, allFlipStepOf_one,
          ha, hb] at ih' ⊢ <;>
        first
        | (ring; done)
        | linear_combination ih'

/-- Filtering preserves ordinary counts of a phase-one label. -/
theorem count_d5PhaseOneSubword (label : D5Alphabet)
    (hlabel : d5Phase label = 1) (word : Word D5Alphabet) :
    (d5PhaseOneSubword word).count ⟨label, hlabel⟩ =
      word.count label := by
  induction word with
  | nil => simp [d5PhaseOneSubword]
  | cons p word ih =>
      by_cases hp : d5Phase p = 1
      · by_cases hpl : p = label
        · subst p
          simp [d5PhaseOneSubword, hlabel, ih]
        · simp [d5PhaseOneSubword, hp, hpl, ih]
      · have hne : p ≠ label := by
          intro h
          subst p
          exact hp hlabel
        simp [d5PhaseOneSubword, hp, hne, ih]

private theorem d5Phase_eq_zero_of_ne_one (p : D5Alphabet)
    (hp : d5Phase p ≠ 1) : d5Phase p = 0 := by
  rcases p with i | i <;> simp [d5Phase] at hp ⊢

private theorem d5ArrowCount_phaseOneSubword_from (start : ZMod 2)
    (label : D5Alphabet) (hlabel : d5Phase label = 1)
    (word : Word D5Alphabet) :
    d5ArrowCountFrom start 0 label word =
      arrowCountFrom allFlipStepOf start 0 ⟨label, hlabel⟩
        (d5PhaseOneSubword word) := by
  induction word generalizing start with
  | nil => simp [d5PhaseOneSubword, d5ArrowCountFrom]
  | cons p word ih =>
      by_cases hp : d5Phase p = 1
      · by_cases hpl : p = label
        · subst p
          simp [d5PhaseOneSubword, hlabel, d5ArrowCountFrom,
            arrowCountFrom, c2Step, allFlipStepOf]
          simpa [d5ArrowCountFrom] using ih (start + 1)
        · simp [d5PhaseOneSubword, hp, hpl, d5ArrowCountFrom,
            arrowCountFrom, c2Step, allFlipStepOf]
          simpa [d5ArrowCountFrom] using ih (start + 1)
      · have hp0 := d5Phase_eq_zero_of_ne_one p hp
        have hne : p ≠ label := by
          intro h
          subst p
          exact hp hlabel
        simp [d5PhaseOneSubword, hne, d5ArrowCountFrom,
          arrowCountFrom, c2Step, hp0]
        simpa [d5ArrowCountFrom] using ih start

/-- Exact `ZMod 5` identity transported to the full `D₅` alphabet. -/
theorem two_mul_d5Arrow_eq_count_add_pairBalance
    (label : D5Alphabet) (hlabel : d5Phase label = 1)
    (word : Word D5Alphabet) (hphase : (word.map d5Phase).sum = 0) :
    (2 : ZMod 5) * (d5ArrowCountFrom 0 0 label word : ZMod 5) =
      (word.count label : ZMod 5) +
        d5PairBalance5 ⟨label, hlabel⟩ (d5PhaseOneSubword word) := by
  have hEven : (d5PhaseOneSubword word).length % 2 = 0 :=
    (d5PhaseOneSubword_even_iff_phase_sum_zero word).2 hphase
  rw [d5ArrowCount_phaseOneSubword_from 0 label hlabel word]
  rw [two_mul_evenArrow_eq_count_add_d5PairBalance5 ⟨label, hlabel⟩
    (d5PhaseOneSubword word) hEven]
  rw [count_d5PhaseOneSubword label hlabel word]

/-- The mod-five feature determined by ordinary and ordered-pair counts. -/
def d5ArrowFingerprint5 (label : D5Alphabet)
    (hlabel : d5Phase label = 1) (word : Word D5Alphabet) : ZMod 5 :=
  (word.count label : ZMod 5) +
    d5PairBalance5 ⟨label, hlabel⟩ (d5PhaseOneSubword word)

/-- Multiplication by two permutes the five residues. -/
theorem d5TwoMulFin5_injective (left right : Fin 5)
    (h : (2 : ZMod 5) * (left.1 : ZMod 5) =
      (2 : ZMod 5) * (right.1 : ZMod 5)) : left = right := by
  revert left right
  decide

private theorem d5TwoMulFin5_iff (n : Nat) (target : Fin 5) :
    n % 5 = target.1 ↔
      (2 : ZMod 5) * (n : ZMod 5) =
        (2 : ZMod 5) * (target.1 : ZMod 5) := by
  constructor
  · intro h
    have hcast : ((2 * n : Nat) : ZMod 5) =
        ((2 * target.1 : Nat) : ZMod 5) := by
      apply (ZMod.natCast_eq_natCast_iff' (2 * n) (2 * target.1) 5).mpr
      omega
    simpa using hcast
  · intro h
    have hcast : ((2 * n : Nat) : ZMod 5) =
        ((2 * target.1 : Nat) : ZMod 5) := by
      simpa using h
    have hmod :=
      (ZMod.natCast_eq_natCast_iff' (2 * n) (2 * target.1) 5).mp hcast
    omega

/-- Exact downstream consumer: the mod-five arrow residue is equivalent to
the mod-five ordinary-count/pair-balance fingerprint. -/
theorem d5ArrowCount_mod_five_iff_features_mod_five
    (label : D5Alphabet) (hlabel : d5Phase label = 1)
    (word : Word D5Alphabet) (target : Fin 5)
    (hphase : (word.map d5Phase).sum = 0) :
    d5ArrowCountFrom 0 0 label word % 5 = target.1 ↔
      d5ArrowFingerprint5 label hlabel word =
        (2 : ZMod 5) * (target.1 : ZMod 5) := by
  have hidentity :=
    two_mul_d5Arrow_eq_count_add_pairBalance label hlabel word hphase
  rw [d5ArrowFingerprint5, ← hidentity]
  exact d5TwoMulFin5_iff (d5ArrowCountFrom 0 0 label word) target

end D5ArrowArithmetic

end GSH
