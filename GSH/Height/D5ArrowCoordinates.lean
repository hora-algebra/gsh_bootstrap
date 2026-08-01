import GSH.Height.ArrowCounting
import GSH.Height.D5FullFiber

/-! # Prefix arrow coordinates for `D₅` -/

set_option autoImplicit false

namespace GSH

open scoped BigOperators

/-- Prefix-oriented signed coordinate. -/
def d5Beta (p : D5Alphabet) : ZMod 5 :=
  d5Weight (d5Phase p) * d5Coord p

@[simp]
theorem d5Beta_mul (p q : D5Alphabet) :
    d5Beta (p * q) =
      d5Beta p + d5Weight (d5Phase p) * d5Beta q := by
  rcases p with i | i <;> rcases q with j | j <;>
    simp [d5Beta, d5Weight, d5Phase, d5Coord,
      DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr] <;> ring

theorem d5_eq_one_iff_phase_beta (p : D5Alphabet) :
    p = 1 ↔ d5Phase p = 0 ∧ d5Beta p = 0 := by
  rw [d5_eq_one_iff_coordinates]
  constructor
  · rintro ⟨hphase, hcoord⟩
    exact ⟨hphase, by simp [d5Beta, hcoord]⟩
  · rintro ⟨hphase, hbeta⟩
    refine ⟨hphase, ?_⟩
    simpa [d5Beta, d5Weight, hphase] using hbeta

@[simp]
theorem d5Weight_add_phase (state : ZMod 2) (p : D5Alphabet) :
    d5Weight (state + d5Phase p) =
      d5Weight state * d5Weight (d5Phase p) := by
  rcases p with i | i <;> revert state i <;> decide

/-- Prefix-run occurrences of one labelled arrow. -/
def d5ArrowCountFrom (start source : ZMod 2) (label : D5Alphabet)
    (word : Word D5Alphabet) : Nat :=
  ArrowCounting.arrowCountFrom (ArrowCounting.c2Step d5Phase)
    start source label word

/-- The two source counts partition ordinary occurrences. -/
theorem d5ArrowCount_partition (start : ZMod 2) (label : D5Alphabet)
    (word : Word D5Alphabet) :
    d5ArrowCountFrom start 0 label word +
        d5ArrowCountFrom start 1 label word = word.count label := by
  induction word generalizing start with
  | nil => rfl
  | cons a word ih =>
      have hstate : start = 0 ∨ start = 1 := by
        revert start
        decide
      rcases hstate with rfl | rfl
      · simp only [d5ArrowCountFrom, ArrowCounting.arrowCountFrom_cons,
          List.count_cons]
        have htail :
            ArrowCounting.arrowCountFrom (ArrowCounting.c2Step d5Phase)
                (ArrowCounting.c2Step d5Phase 0 a) 0 label word +
              ArrowCounting.arrowCountFrom (ArrowCounting.c2Step d5Phase)
                (ArrowCounting.c2Step d5Phase 0 a) 1 label word =
              word.count label := by
          simpa [d5ArrowCountFrom] using
            ih (ArrowCounting.c2Step d5Phase 0 a)
        by_cases ha : a = label
        · subst a
          simp only [beq_self_eq_true, if_true, if_false, true_and,
            false_and, eq_self, zero_ne_one] at ⊢
          omega
        · simpa [ha, Nat.add_assoc, Nat.add_comm] using htail
      · simp only [d5ArrowCountFrom, ArrowCounting.arrowCountFrom_cons,
          List.count_cons]
        have htail :
            ArrowCounting.arrowCountFrom (ArrowCounting.c2Step d5Phase)
                (ArrowCounting.c2Step d5Phase 1 a) 0 label word +
              ArrowCounting.arrowCountFrom (ArrowCounting.c2Step d5Phase)
                (ArrowCounting.c2Step d5Phase 1 a) 1 label word =
              word.count label := by
          simpa [d5ArrowCountFrom] using
            ih (ArrowCounting.c2Step d5Phase 1 a)
        by_cases ha : a = label
        · subst a
          simp only [beq_self_eq_true, if_true, if_false, true_and,
            false_and, eq_self, one_ne_zero] at ⊢
          omega
        · simpa [ha, Nat.add_comm] using htail

/-- Signed prefix arrow sum. -/
def d5BetaByArrowsFrom (start : ZMod 2)
    (word : Word D5Alphabet) : ZMod 5 :=
  Finset.univ.sum fun label =>
    d5Beta label * (d5ArrowCountFrom start 0 label word : ZMod 5) -
      d5Beta label * (d5ArrowCountFrom start 1 label word : ZMod 5)

private theorem d5_indicator_sum (start : ZMod 2) (a : D5Alphabet) :
    (Finset.univ.sum fun label =>
        d5Beta label *
            (((if start = 0 ∧ a = label then 1 else 0) : Nat) : ZMod 5) -
          d5Beta label *
            (((if start = 1 ∧ a = label then 1 else 0) : Nat) : ZMod 5)) =
      d5Weight start * d5Beta a := by
  revert start a
  decide

theorem d5BetaByArrowsFrom_cons (start : ZMod 2) (a : D5Alphabet)
    (word : Word D5Alphabet) :
    d5BetaByArrowsFrom start (a :: word) =
      d5Weight start * d5Beta a +
        d5BetaByArrowsFrom (start + d5Phase a) word := by
  rw [d5BetaByArrowsFrom]
  change
    (Finset.univ.sum fun label =>
        d5Beta label *
            (((if start = 0 ∧ a = label then 1 else 0) +
              d5ArrowCountFrom (start + d5Phase a) 0 label word : Nat) :
                ZMod 5) -
          d5Beta label *
            (((if start = 1 ∧ a = label then 1 else 0) +
              d5ArrowCountFrom (start + d5Phase a) 1 label word : Nat) :
                ZMod 5)) = _
  calc
    _ = Finset.univ.sum (fun label =>
          (d5Beta label *
              (((if start = 0 ∧ a = label then 1 else 0) : Nat) :
                ZMod 5) -
            d5Beta label *
              (((if start = 1 ∧ a = label then 1 else 0) : Nat) :
                ZMod 5)) +
          (d5Beta label *
              (d5ArrowCountFrom (start + d5Phase a) 0 label word : ZMod 5) -
            d5Beta label *
              (d5ArrowCountFrom (start + d5Phase a) 1 label word :
                ZMod 5))) := by
          apply Finset.sum_congr rfl
          intro label _
          push_cast
          ring
    _ = (Finset.univ.sum fun label =>
          d5Beta label *
              (((if start = 0 ∧ a = label then 1 else 0) : Nat) :
                ZMod 5) -
            d5Beta label *
              (((if start = 1 ∧ a = label then 1 else 0) : Nat) :
                ZMod 5)) +
          d5BetaByArrowsFrom (start + d5Phase a) word := by
            rw [Finset.sum_add_distrib]
            rfl
    _ = _ := by rw [d5_indicator_sum]

theorem d5BetaByArrowsFrom_eq (start : ZMod 2)
    (word : Word D5Alphabet) :
    d5BetaByArrowsFrom start word =
      d5Weight start * d5Beta word.prod := by
  induction word generalizing start with
  | nil =>
      rw [show d5BetaByArrowsFrom start [] = 0 by
        simp [d5BetaByArrowsFrom, d5ArrowCountFrom]]
      rw [show ([] : Word D5Alphabet).prod = 1 by rfl]
      rw [DihedralGroup.one_def]
      simp [d5Beta, d5Phase, d5Coord]
  | cons a word ih =>
      rw [d5BetaByArrowsFrom_cons, ih, d5Weight_add_phase]
      simp only [List.prod_cons, d5Beta_mul]
      ring

def d5BetaByArrows (word : Word D5Alphabet) : ZMod 5 :=
  d5BetaByArrowsFrom 0 word

/-- Source-one counts are eliminated as ordinary count minus source zero. -/
theorem d5BetaByArrows_eq_sourceZero_total (word : Word D5Alphabet) :
    d5BetaByArrows word =
      Finset.univ.sum fun label =>
        d5Beta label *
          ((2 : ZMod 5) *
              (d5ArrowCountFrom 0 0 label word : ZMod 5) -
            (word.count label : ZMod 5)) := by
  rw [d5BetaByArrows, d5BetaByArrowsFrom]
  apply Finset.sum_congr rfl
  intro label _
  have hpartition := congrArg (fun n : Nat => (n : ZMod 5))
    (d5ArrowCount_partition 0 label word)
  push_cast at hpartition
  rw [← hpartition]
  ring

theorem d5Beta_prod_eq_arrowCounts (word : Word D5Alphabet) :
    d5Beta word.prod = d5BetaByArrows word := by
  simpa [d5BetaByArrows, d5Weight] using
    (d5BetaByArrowsFrom_eq 0 word).symm

theorem d5_prod_eq_one_iff_arrowCounts (word : Word D5Alphabet) :
    word.prod = 1 ↔
      (word.map d5Phase).sum = 0 ∧ d5BetaByArrows word = 0 := by
  rw [d5_eq_one_iff_phase_beta, d5Phase_prod_eq_sum,
    d5Beta_prod_eq_arrowCounts]

def d5ArrowCoordinateFiber : Language D5Alphabet :=
  {word | (word.map d5Phase).sum = 0 ∧ d5BetaByArrows word = 0}

theorem fullIdentityFiber_d5_eq_arrowCoordinateFiber :
    fullIdentityFiber D5Alphabet = d5ArrowCoordinateFiber := by
  ext word
  exact (mem_fullIdentityFiber_iff word).trans
    (d5_prod_eq_one_iff_arrowCounts word)

end GSH
