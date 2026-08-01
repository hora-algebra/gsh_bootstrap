import GSH.Height.ArrowCounting
import GSH.Height.D4FullFiber

/-!
# Prefix arrow coordinates for `D₄`

The raw coordinate in `D4FullFiber` follows mathlib's right-oriented
constructor convention.  Multiplying it by the reflection sign produces the
usual prefix-oriented semidirect-product coordinate.  A signed sum of
two-state arrow counts then reconstructs that coordinate for a whole word.
-/

set_option autoImplicit false

namespace GSH

open scoped BigOperators

/-- Prefix-oriented signed `ZMod 4` coordinate. -/
def d4Beta (p : D4Alphabet) : ZMod 4 :=
  d4Weight (d4Phase p) * d4Coord p

/-- The signed coordinate obeys the prefix semidirect-product law. -/
@[simp]
theorem d4Beta_mul (p q : D4Alphabet) :
    d4Beta (p * q) =
      d4Beta p + d4Weight (d4Phase p) * d4Beta q := by
  rcases p with i | i <;> rcases q with j | j <;>
    simp [d4Beta, d4Weight, d4Phase, d4Coord,
      DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr] <;> ring

/-- The phase and signed coordinate detect the identity. -/
theorem d4_eq_one_iff_phase_beta (p : D4Alphabet) :
    p = 1 ↔ d4Phase p = 0 ∧ d4Beta p = 0 := by
  rw [d4_eq_one_iff_coordinates]
  constructor
  · rintro ⟨hphase, hcoord⟩
    exact ⟨hphase, by simp [d4Beta, hcoord]⟩
  · rintro ⟨hphase, hbeta⟩
    refine ⟨hphase, ?_⟩
    simpa [d4Beta, d4Weight, hphase] using hbeta

/-- Advancing the phase run multiplies the current sign by the letter sign. -/
@[simp]
theorem d4Weight_add_phase (state : ZMod 2) (p : D4Alphabet) :
    d4Weight (state + d4Phase p) =
      d4Weight state * d4Weight (d4Phase p) := by
  rcases p with i | i <;> revert state i <;> decide

/-- Prefix-run occurrences of `label` read from a specified source state. -/
def d4ArrowCountFrom (start source : ZMod 2) (label : D4Alphabet)
    (word : Word D4Alphabet) : Nat :=
  ArrowCounting.arrowCountFrom (ArrowCounting.c2Step d4Phase)
    start source label word

/-- The two source-state counts of a fixed `D₄` label partition its ordinary
occurrences.  This is the arithmetic input used to recover source one from
the already constructed source-zero residue languages. -/
theorem d4ArrowCount_partition (start : ZMod 2) (label : D4Alphabet)
    (word : Word D4Alphabet) :
    d4ArrowCountFrom start 0 label word +
        d4ArrowCountFrom start 1 label word =
      word.count label := by
  induction word generalizing start with
  | nil => rfl
  | cons a word ih =>
      have hstate : start = 0 ∨ start = 1 := by
        revert start
        decide
      rcases hstate with rfl | rfl
      · simp only [d4ArrowCountFrom, ArrowCounting.arrowCountFrom_cons,
          List.count_cons]
        have htail :
            ArrowCounting.arrowCountFrom (ArrowCounting.c2Step d4Phase)
                (ArrowCounting.c2Step d4Phase 0 a) 0 label word +
              ArrowCounting.arrowCountFrom (ArrowCounting.c2Step d4Phase)
                (ArrowCounting.c2Step d4Phase 0 a) 1 label word =
              word.count label := by
          simpa [d4ArrowCountFrom] using
            ih (ArrowCounting.c2Step d4Phase 0 a)
        by_cases ha : a = label
        · subst a
          simp only [beq_self_eq_true, if_true, if_false, true_and, false_and,
            eq_self, zero_ne_one] at ⊢
          omega
        · simpa [ha, Nat.add_assoc, Nat.add_comm] using htail
      · simp only [d4ArrowCountFrom, ArrowCounting.arrowCountFrom_cons,
          List.count_cons]
        have htail :
            ArrowCounting.arrowCountFrom (ArrowCounting.c2Step d4Phase)
                (ArrowCounting.c2Step d4Phase 1 a) 0 label word +
              ArrowCounting.arrowCountFrom (ArrowCounting.c2Step d4Phase)
                (ArrowCounting.c2Step d4Phase 1 a) 1 label word =
              word.count label := by
          simpa [d4ArrowCountFrom] using
            ih (ArrowCounting.c2Step d4Phase 1 a)
        by_cases ha : a = label
        · subst a
          simp only [beq_self_eq_true, if_true, if_false, true_and, false_and,
            eq_self, one_ne_zero] at ⊢
          omega
        · simpa [ha, Nat.add_comm] using htail

/-- Signed prefix arrow-count sum, with coefficients in `ZMod 4`. -/
def d4BetaByArrowsFrom (start : ZMod 2) (word : Word D4Alphabet) : ZMod 4 :=
  Finset.univ.sum fun label =>
    d4Beta label * (d4ArrowCountFrom start 0 label word : ZMod 4) -
      d4Beta label * (d4ArrowCountFrom start 1 label word : ZMod 4)

private theorem d4_indicator_sum (start : ZMod 2) (a : D4Alphabet) :
    (Finset.univ.sum fun label =>
        d4Beta label *
            (((if start = 0 ∧ a = label then 1 else 0) : Nat) : ZMod 4) -
          d4Beta label *
            (((if start = 1 ∧ a = label then 1 else 0) : Nat) : ZMod 4)) =
      d4Weight start * d4Beta a := by
  revert start a
  decide

/-- Peeling the first letter advances the prefix phase run. -/
theorem d4BetaByArrowsFrom_cons (start : ZMod 2) (a : D4Alphabet)
    (word : Word D4Alphabet) :
    d4BetaByArrowsFrom start (a :: word) =
      d4Weight start * d4Beta a +
        d4BetaByArrowsFrom (start + d4Phase a) word := by
  rw [d4BetaByArrowsFrom]
  change
    (Finset.univ.sum fun label =>
        d4Beta label *
            (((if start = 0 ∧ a = label then 1 else 0) +
              d4ArrowCountFrom (start + d4Phase a) 0 label word : Nat) :
                ZMod 4) -
          d4Beta label *
            (((if start = 1 ∧ a = label then 1 else 0) +
              d4ArrowCountFrom (start + d4Phase a) 1 label word : Nat) :
                ZMod 4)) = _
  calc
    _ =
        (Finset.univ.sum fun label =>
          (d4Beta label *
                (((if start = 0 ∧ a = label then 1 else 0) : Nat) :
                  ZMod 4) -
              d4Beta label *
                (((if start = 1 ∧ a = label then 1 else 0) : Nat) :
                  ZMod 4)) +
            (d4Beta label *
                (d4ArrowCountFrom (start + d4Phase a) 0 label word : ZMod 4) -
              d4Beta label *
                (d4ArrowCountFrom (start + d4Phase a) 1 label word :
                  ZMod 4))) := by
          apply Finset.sum_congr rfl
          intro label _
          push_cast
          ring
    _ =
        (Finset.univ.sum fun label =>
          d4Beta label *
                (((if start = 0 ∧ a = label then 1 else 0) : Nat) :
                  ZMod 4) -
              d4Beta label *
                (((if start = 1 ∧ a = label then 1 else 0) : Nat) :
                  ZMod 4)) +
          d4BetaByArrowsFrom (start + d4Phase a) word := by
          rw [Finset.sum_add_distrib]
          rfl
    _ = _ := by rw [d4_indicator_sum]

/-- The signed arrow sum reconstructs the product coordinate from any initial
phase state. -/
theorem d4BetaByArrowsFrom_eq (start : ZMod 2) (word : Word D4Alphabet) :
    d4BetaByArrowsFrom start word =
      d4Weight start * d4Beta word.prod := by
  induction word generalizing start with
  | nil =>
      rw [show d4BetaByArrowsFrom start [] = 0 by
        simp [d4BetaByArrowsFrom, d4ArrowCountFrom]]
      rw [show ([] : Word D4Alphabet).prod = 1 by rfl]
      rw [DihedralGroup.one_def]
      simp [d4Beta, d4Phase, d4Coord]
  | cons a word ih =>
      rw [d4BetaByArrowsFrom_cons, ih, d4Weight_add_phase]
      simp only [List.prod_cons, d4Beta_mul]
      ring

/-- Signed arrow sum for the run beginning at phase zero. -/
def d4BetaByArrows (word : Word D4Alphabet) : ZMod 4 :=
  d4BetaByArrowsFrom 0 word

/-- On a phase-zero fibre it is unnecessary to construct source-one
languages separately: the signed coordinate is determined by the source-zero
arrow counts and ordinary label counts. -/
theorem d4BetaByArrows_eq_sourceZero_total (word : Word D4Alphabet) :
    d4BetaByArrows word =
      Finset.univ.sum fun label =>
        d4Beta label *
          ((2 : ZMod 4) *
              (d4ArrowCountFrom 0 0 label word : ZMod 4) -
            (word.count label : ZMod 4)) := by
  rw [d4BetaByArrows, d4BetaByArrowsFrom]
  apply Finset.sum_congr rfl
  intro label _
  have hpartition := congrArg (fun n : Nat => (n : ZMod 4))
    (d4ArrowCount_partition 0 label word)
  push_cast at hpartition
  rw [← hpartition]
  ring

/-- The product's prefix coordinate is exactly the signed arrow-count sum. -/
theorem d4Beta_prod_eq_arrowCounts (word : Word D4Alphabet) :
    d4Beta word.prod = d4BetaByArrows word := by
  simpa [d4BetaByArrows, d4Weight] using
    (d4BetaByArrowsFrom_eq 0 word).symm

/-- Exact identity reconstruction from phase and prefix arrow counts. -/
theorem d4_prod_eq_one_iff_arrowCounts (word : Word D4Alphabet) :
    word.prod = 1 ↔
      (word.map d4Phase).sum = 0 ∧ d4BetaByArrows word = 0 := by
  rw [d4_eq_one_iff_phase_beta, d4Phase_prod_eq_sum,
    d4Beta_prod_eq_arrowCounts]

/-- Arithmetic identity fibre in prefix arrow coordinates. -/
def d4ArrowCoordinateFiber : Language D4Alphabet :=
  {word | (word.map d4Phase).sum = 0 ∧ d4BetaByArrows word = 0}

/-- The full-alphabet identity fibre is exactly the prefix-arrow language. -/
theorem fullIdentityFiber_d4_eq_arrowCoordinateFiber :
    fullIdentityFiber D4Alphabet = d4ArrowCoordinateFiber := by
  ext word
  exact (mem_fullIdentityFiber_iff word).trans
    (d4_prod_eq_one_iff_arrowCounts word)

end GSH
