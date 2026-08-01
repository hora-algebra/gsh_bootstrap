import GSH.Height.D4ArrowCoordinates
import GSH.Height.S3ArrowArithmetic

/-!
# Mod-eight pair arithmetic for phase-one `D₄` letters

On an even word all letters toggle the two-state prefix run.  Twice the
source-zero count of a label is its ordinary count plus the signed imbalance
of the ordered length-two blocks incident with that label.  We retain the
identity in `ZMod 8`, so it determines the original arrow count modulo four.
-/

set_option autoImplicit false

namespace GSH

namespace D4ArrowArithmetic

open ArrowCounting
open S3ArrowArithmetic

/-- The four reflections, represented as phase-one `D₄` letters. -/
abbrev D4PhaseOne := {p : D4Alphabet // d4Phase p = 1}

local instance : BEq D4PhaseOne := instBEqOfDecidableEq

/-- Signed distinct-pair imbalance, with coefficients retained modulo eight. -/
def d4PairBalance8 (label : D4PhaseOne) (word : Word D4PhaseOne) : ZMod 8 :=
  ∑ other : D4PhaseOne,
    if other = label then 0
    else
      (pairCountOf label other word : ZMod 8) -
        (pairCountOf other label word : ZMod 8)

private theorem sum_other_indicator8 (label value : D4PhaseOne)
    (h : value ≠ label) :
    (∑ other : D4PhaseOne,
      if other = label then 0
      else if value = other then (1 : ZMod 8) else 0) = 1 := by
  calc
    _ = ∑ other : D4PhaseOne,
        if value = other then (1 : ZMod 8) else 0 := by
      apply Finset.sum_congr rfl
      intro other _
      by_cases hv : value = other
      · subst other
        simp [h]
      · simp [hv]
    _ = 1 := by simp

private theorem sum_other_neg_indicator8 (label value : D4PhaseOne)
    (h : value ≠ label) :
    (∑ other : D4PhaseOne,
      if other = label then 0
      else -if value = other then (1 : ZMod 8) else 0) = -1 := by
  calc
    _ =
        -(∑ other : D4PhaseOne,
          if other = label then 0
          else if value = other then (1 : ZMod 8) else 0) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro other _
      by_cases ho : other = label <;> simp [ho]
    _ = -1 := by rw [sum_other_indicator8 label value h]

private theorem d4PairBalance8_cons_cons
    (label a b : D4PhaseOne) (word : Word D4PhaseOne) :
    d4PairBalance8 label (a :: b :: word) =
      (if a = label ∧ b ≠ label then 1 else 0) -
        (if a ≠ label ∧ b = label then 1 else 0) +
          d4PairBalance8 label word := by
  classical
  unfold d4PairBalance8
  calc
    (∑ other : D4PhaseOne,
        if other = label then 0
        else
          (pairCountOf label other (a :: b :: word) : ZMod 8) -
            (pairCountOf other label (a :: b :: word) : ZMod 8)) =
      (∑ other : D4PhaseOne,
        if other = label then 0
        else
          ((if a = label ∧ b = other then 1 else 0) : ZMod 8) -
            ((if a = other ∧ b = label then 1 else 0) : ZMod 8)) +
      ∑ other : D4PhaseOne,
        if other = label then 0
        else
          (pairCountOf label other word : ZMod 8) -
            (pairCountOf other label word : ZMod 8) := by
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
          ∑ other : D4PhaseOne,
            if other = label then 0
            else
              (pairCountOf label other word : ZMod 8) -
                (pairCountOf other label word : ZMod 8) := by
        congr 1
        by_cases ha : a = label
        · by_cases hb : b = label
          · subst a
            subst b
            simp
          · subst a
            simpa [hb] using sum_other_indicator8 label b hb
        · by_cases hb : b = label
          · subst b
            simpa [ha] using sum_other_neg_indicator8 label a ha
          · simp [ha, hb]

/-- Exact phase-one identity in `ZMod 8`.  Reducing its source-zero count
modulo four loses no information because the left side is twice that count. -/
private theorem two_mul_evenArrow_eq_count_add_d4PairBalance8
    (label : D4PhaseOne) (word : Word D4PhaseOne)
    (hEven : word.length % 2 = 0) :
    (2 : ZMod 8) *
        (arrowCountFrom allFlipStepOf 0 0 label word : ZMod 8) =
      (word.count label : ZMod 8) + d4PairBalance8 label word := by
  induction word using List.twoStepInduction with
  | nil => simp [d4PairBalance8]
  | singleton a => simp at hEven
  | cons_cons a b word ih _ =>
      have hTail : word.length % 2 = 0 := by
        change (word.length + 2) % 2 = 0 at hEven
        simpa only [Nat.add_mod_right] using hEven
      have ih' := ih hTail
      rw [d4PairBalance8_cons_cons]
      by_cases ha : a = label <;> by_cases hb : b = label <;>
        simp [arrowCountFrom, allFlipStepOf_zero, allFlipStepOf_one,
          ha, hb] at ih' ⊢ <;>
        first
        | (ring; done)
        | linear_combination ih'

/-- Delete phase-zero letters and retain phase-one `D₄` letters. -/
def d4PhaseOneSubword : Word D4Alphabet → Word D4PhaseOne
  | [] => []
  | p :: word =>
      if hp : d4Phase p = 1 then
        ⟨p, hp⟩ :: d4PhaseOneSubword word
      else
        d4PhaseOneSubword word

private theorem d4Phase_eq_zero_of_ne_one (p : D4Alphabet)
    (hp : d4Phase p ≠ 1) : d4Phase p = 0 := by
  rcases p with i | i <;> simp [d4Phase] at hp ⊢

theorem d4PhaseOneSubword_length_cast (word : Word D4Alphabet) :
    ((d4PhaseOneSubword word).length : ZMod 2) =
      (word.map d4Phase).sum := by
  induction word with
  | nil => simp [d4PhaseOneSubword]
  | cons p word ih =>
      by_cases hp : d4Phase p = 1
      · simp [d4PhaseOneSubword, hp, ih, add_comm]
      · have hp0 := d4Phase_eq_zero_of_ne_one p hp
        simp [d4PhaseOneSubword, hp0, ih]

theorem d4PhaseOneSubword_even_iff_phase_sum_zero
    (word : Word D4Alphabet) :
    (d4PhaseOneSubword word).length % 2 = 0 ↔
      (word.map d4Phase).sum = 0 := by
  rw [← d4PhaseOneSubword_length_cast]
  simpa [Nat.dvd_iff_mod_eq_zero] using
    (ZMod.natCast_eq_zero_iff (d4PhaseOneSubword word).length 2).symm

theorem count_d4PhaseOneSubword (label : D4Alphabet)
    (hlabel : d4Phase label = 1) (word : Word D4Alphabet) :
    (d4PhaseOneSubword word).count ⟨label, hlabel⟩ =
      word.count label := by
  induction word with
  | nil => simp [d4PhaseOneSubword]
  | cons p word ih =>
      by_cases hp : d4Phase p = 1
      · by_cases hpl : p = label
        · subst p
          simp [d4PhaseOneSubword, hlabel, ih]
        · simp [d4PhaseOneSubword, hp, hpl, ih]
      · have hne : p ≠ label := by
          intro h
          subst p
          exact hp hlabel
        simp [d4PhaseOneSubword, hp, hne, ih]

private theorem d4ArrowCount_phaseOneSubword_from (start : ZMod 2)
    (label : D4Alphabet) (hlabel : d4Phase label = 1)
    (word : Word D4Alphabet) :
    d4ArrowCountFrom start 0 label word =
      arrowCountFrom allFlipStepOf start 0 ⟨label, hlabel⟩
        (d4PhaseOneSubword word) := by
  induction word generalizing start with
  | nil => simp [d4PhaseOneSubword, d4ArrowCountFrom]
  | cons p word ih =>
      by_cases hp : d4Phase p = 1
      · by_cases hpl : p = label
        · subst p
          simp [d4PhaseOneSubword, hlabel, d4ArrowCountFrom,
            arrowCountFrom, c2Step, allFlipStepOf]
          simpa [d4ArrowCountFrom] using ih (start + 1)
        · simp [d4PhaseOneSubword, hp, hpl, d4ArrowCountFrom,
            arrowCountFrom, c2Step, allFlipStepOf]
          simpa [d4ArrowCountFrom] using ih (start + 1)
      · have hp0 := d4Phase_eq_zero_of_ne_one p hp
        have hne : p ≠ label := by
          intro h
          subst p
          exact hp hlabel
        simp [d4PhaseOneSubword, hne, d4ArrowCountFrom,
          arrowCountFrom, c2Step, hp0]
        simpa [d4ArrowCountFrom] using ih start

/-- Exact `ZMod 8` identity transported to the full `D₄` alphabet. -/
theorem two_mul_d4Arrow_eq_count_add_pairBalance
    (label : D4Alphabet) (hlabel : d4Phase label = 1)
    (word : Word D4Alphabet) (hphase : (word.map d4Phase).sum = 0) :
    (2 : ZMod 8) * (d4ArrowCountFrom 0 0 label word : ZMod 8) =
      (word.count label : ZMod 8) +
        d4PairBalance8 ⟨label, hlabel⟩ (d4PhaseOneSubword word) := by
  have hEven : (d4PhaseOneSubword word).length % 2 = 0 :=
    (d4PhaseOneSubword_even_iff_phase_sum_zero word).2 hphase
  rw [d4ArrowCount_phaseOneSubword_from 0 label hlabel word]
  rw [two_mul_evenArrow_eq_count_add_d4PairBalance8 ⟨label, hlabel⟩
    (d4PhaseOneSubword word) hEven]
  rw [count_d4PhaseOneSubword label hlabel word]

/-- The mod-eight feature determined by ordinary and ordered-pair counts. -/
def d4ArrowFingerprint8 (label : D4Alphabet)
    (hlabel : d4Phase label = 1) (word : Word D4Alphabet) : ZMod 8 :=
  (word.count label : ZMod 8) +
    d4PairBalance8 ⟨label, hlabel⟩ (d4PhaseOneSubword word)

/-- Multiplication by two embeds the four residues into `ZMod 8`. -/
theorem d4TwoMulFin4_injective (left right : Fin 4)
    (h : (2 : ZMod 8) * (left.1 : ZMod 8) =
      (2 : ZMod 8) * (right.1 : ZMod 8)) : left = right := by
  revert left right
  decide

private theorem d4TwoMulFin4_iff (n : Nat) (target : Fin 4) :
    n % 4 = target.1 ↔
      (2 : ZMod 8) * (n : ZMod 8) =
        (2 : ZMod 8) * (target.1 : ZMod 8) := by
  constructor
  · intro h
    have hcast : ((2 * n : Nat) : ZMod 8) =
        ((2 * target.1 : Nat) : ZMod 8) := by
      apply (ZMod.natCast_eq_natCast_iff' (2 * n) (2 * target.1) 8).mpr
      omega
    simpa using hcast
  · intro h
    have hcast : ((2 * n : Nat) : ZMod 8) =
        ((2 * target.1 : Nat) : ZMod 8) := by
      simpa using h
    have hmod :=
      (ZMod.natCast_eq_natCast_iff' (2 * n) (2 * target.1) 8).mp hcast
    omega

/-- Exact downstream consumer: the mod-four arrow residue is equivalent to
the mod-eight ordinary-count/pair-balance fingerprint. -/
theorem d4ArrowCount_mod_four_iff_features_mod_eight
    (label : D4Alphabet) (hlabel : d4Phase label = 1)
    (word : Word D4Alphabet) (target : Fin 4)
    (hphase : (word.map d4Phase).sum = 0) :
    d4ArrowCountFrom 0 0 label word % 4 = target.1 ↔
      d4ArrowFingerprint8 label hlabel word =
        (2 : ZMod 8) * (target.1 : ZMod 8) := by
  have hidentity :=
    two_mul_d4Arrow_eq_count_add_pairBalance label hlabel word hphase
  rw [d4ArrowFingerprint8, ← hidentity]
  exact d4TwoMulFin4_iff (d4ArrowCountFrom 0 0 label word) target

end D4ArrowArithmetic

end GSH
