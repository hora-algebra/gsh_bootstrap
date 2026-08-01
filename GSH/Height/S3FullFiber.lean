import GSH.Height.ArrowCounting
import GSH.Height.FullAlphabet
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Direct coordinates for the full-alphabet identity fibre of `S₃`

This file analyzes products in `Equiv.Perm (Fin 3)` directly, without using
the semidirect-product presentation from `GSH.Groups.S3`.

A permutation is determined by two coordinates:

* its sign, written additively as a phase in `ZMod 2`;
* the image of `0`, written in `ZMod 3`.

The second coordinate of a word product is the signed sum of the letter
coordinates.  The sign at a position is the source state of the two-state run,
so this signed sum can be written using the labelled-arrow counts from
`GSH.Height.ArrowCounting`.

This is only the word-level reconstruction of the identity fibre.  It does not
prove that the arrow-count residue languages have generalized star height at
most one.
-/

set_option autoImplicit false

namespace GSH

open scoped BigOperators

abbrev S3Alphabet := Equiv.Perm (Fin 3)

/-- The sign of a permutation, written additively in `ZMod 2`. -/
def s3Phase (p : S3Alphabet) : ZMod 2 :=
  if Equiv.Perm.sign p = 1 then 0 else 1

/-- The slope of the affine action of `S₃` on `ZMod 3`. -/
def s3Slope (p : S3Alphabet) : ZMod 3 :=
  if Equiv.Perm.sign p = 1 then 1 else -1

/-- The standard coordinate `Fin 3 → ZMod 3`. -/
def s3PointCoord (i : Fin 3) : ZMod 3 := i.1

/-- The translation coordinate of a permutation: the image of `0`. -/
def s3Beta (p : S3Alphabet) : ZMod 3 :=
  s3PointCoord (p 0)

/-- The phase is additive under permutation multiplication. -/
@[simp]
theorem s3Phase_mul (p q : S3Alphabet) :
    s3Phase (p * q) = s3Phase p + s3Phase q := by
  revert p q
  decide

/-- The translation coordinate obeys the affine multiplication law. -/
@[simp]
theorem s3Beta_mul (p q : S3Alphabet) :
    s3Beta (p * q) = s3Beta p + s3Slope p * s3Beta q := by
  revert p q
  decide

/-- The two coordinates detect the identity permutation. -/
theorem s3_eq_one_iff_phase_beta (p : S3Alphabet) :
    p = 1 ↔ s3Phase p = 0 ∧ s3Beta p = 0 := by
  revert p
  decide

/-- The sign with which a letter coordinate contributes when the current
`C₂` state is `state`. -/
def s3StateWeight (state : ZMod 2) : ZMod 3 :=
  if state = 0 then 1 else -1

/-- Advancing the two-state run multiplies the current weight by the slope of
the letter read. -/
@[simp]
theorem s3StateWeight_add_phase (state : ZMod 2) (p : S3Alphabet) :
    s3StateWeight (state + s3Phase p) = s3StateWeight state * s3Slope p := by
  revert state p
  decide

/-- The count of occurrences of `label` whose source in the sign run is
`source`, when the run begins at `start`. -/
def s3ArrowCountFrom (start source : ZMod 2) (label : S3Alphabet)
    (word : Word S3Alphabet) : Nat :=
  ArrowCounting.arrowCountFrom (ArrowCounting.c2Step s3Phase)
    start source label word

/-- The signed sum of the letter translation coordinates, presented through
the two source-state arrow counts. -/
def s3BetaByArrowsFrom (start : ZMod 2) (word : Word S3Alphabet) : ZMod 3 :=
  Finset.univ.sum fun label =>
    s3Beta label * (s3ArrowCountFrom start 0 label word : ZMod 3) -
      s3Beta label * (s3ArrowCountFrom start 1 label word : ZMod 3)

/-- At the first position, the sum of the two source indicators contributes
exactly the signed coordinate of the letter read. -/
private theorem s3_indicator_sum (start : ZMod 2) (a : S3Alphabet) :
    (Finset.univ.sum fun label =>
        s3Beta label *
            (((if start = 0 ∧ a = label then 1 else 0) : Nat) : ZMod 3) -
          s3Beta label *
            (((if start = 1 ∧ a = label then 1 else 0) : Nat) : ZMod 3)) =
      s3StateWeight start * s3Beta a := by
  revert start a
  decide

/-- Peeling the first letter from the signed arrow sum advances the sign run. -/
theorem s3BetaByArrowsFrom_cons (start : ZMod 2) (a : S3Alphabet)
    (word : Word S3Alphabet) :
    s3BetaByArrowsFrom start (a :: word) =
      s3StateWeight start * s3Beta a +
        s3BetaByArrowsFrom (start + s3Phase a) word := by
  rw [s3BetaByArrowsFrom]
  change
    (Finset.univ.sum fun label =>
        s3Beta label *
            (((if start = 0 ∧ a = label then 1 else 0) +
              s3ArrowCountFrom (start + s3Phase a) 0 label word : Nat) : ZMod 3) -
          s3Beta label *
            (((if start = 1 ∧ a = label then 1 else 0) +
              s3ArrowCountFrom (start + s3Phase a) 1 label word : Nat) : ZMod 3)) = _
  calc
    _ =
        (Finset.univ.sum fun label =>
          (s3Beta label *
                (((if start = 0 ∧ a = label then 1 else 0) : Nat) : ZMod 3) -
              s3Beta label *
                (((if start = 1 ∧ a = label then 1 else 0) : Nat) : ZMod 3)) +
            (s3Beta label *
                (s3ArrowCountFrom (start + s3Phase a) 0 label word : ZMod 3) -
              s3Beta label *
                (s3ArrowCountFrom (start + s3Phase a) 1 label word : ZMod 3))) := by
          apply Finset.sum_congr rfl
          intro label _
          push_cast
          ring
    _ =
        (Finset.univ.sum fun label =>
          s3Beta label *
                (((if start = 0 ∧ a = label then 1 else 0) : Nat) : ZMod 3) -
              s3Beta label *
                (((if start = 1 ∧ a = label then 1 else 0) : Nat) : ZMod 3)) +
          s3BetaByArrowsFrom (start + s3Phase a) word := by
          rw [Finset.sum_add_distrib]
          rfl
    _ = _ := by rw [s3_indicator_sum]

/-- The signed arrow sum is the translation coordinate of the word product,
with the sign determined by the initial state. -/
theorem s3BetaByArrowsFrom_eq (start : ZMod 2) (word : Word S3Alphabet) :
    s3BetaByArrowsFrom start word =
      s3StateWeight start * s3Beta word.prod := by
  induction word generalizing start with
  | nil =>
      simp [s3BetaByArrowsFrom, s3ArrowCountFrom, s3StateWeight, s3Beta,
        s3PointCoord]
  | cons a word ih =>
      rw [s3BetaByArrowsFrom_cons, ih, s3StateWeight_add_phase]
      simp only [List.prod_cons, s3Beta_mul]
      ring

/-- The signed arrow sum for the run beginning at phase zero. -/
def s3BetaByArrows (word : Word S3Alphabet) : ZMod 3 :=
  s3BetaByArrowsFrom 0 word

/-- The translation coordinate of a word product is its signed arrow sum. -/
theorem s3Beta_prod_eq_arrowCounts (word : Word S3Alphabet) :
    s3Beta word.prod = s3BetaByArrows word := by
  simpa [s3BetaByArrows, s3StateWeight] using
    (s3BetaByArrowsFrom_eq 0 word).symm

/-- The phase of a word product is the sum of the phases of its letters. -/
theorem s3Phase_prod_eq_sum (word : Word S3Alphabet) :
    s3Phase word.prod = (word.map s3Phase).sum := by
  induction word with
  | nil => simp [s3Phase]
  | cons a word ih => simp [ih]

/-- Exact word-level reconstruction of multiplication in `S₃` from the
two-state arrow counts. -/
theorem s3_prod_eq_one_iff_arrowCounts (word : Word S3Alphabet) :
    word.prod = 1 ↔
      (word.map s3Phase).sum = 0 ∧ s3BetaByArrows word = 0 := by
  rw [s3_eq_one_iff_phase_beta, s3Phase_prod_eq_sum,
    s3Beta_prod_eq_arrowCounts]

/-- The arithmetic language reconstructed by the phase and signed-arrow
coordinates. -/
def s3ArrowCoordinateFiber : Language S3Alphabet :=
  {word | (word.map s3Phase).sum = 0 ∧ s3BetaByArrows word = 0}

theorem mem_s3ArrowCoordinateFiber_iff (word : Word S3Alphabet) :
    word ∈ s3ArrowCoordinateFiber ↔
      (word.map s3Phase).sum = 0 ∧ s3BetaByArrows word = 0 :=
  Iff.rfl

/-- The full-alphabet identity fibre of `S₃` is exactly the arithmetic
phase-and-arrow-count language. -/
theorem fullIdentityFiber_s3_eq_arrowCoordinateFiber :
    fullIdentityFiber S3Alphabet = s3ArrowCoordinateFiber := by
  ext word
  exact (mem_fullIdentityFiber_iff word).trans
    (s3_prod_eq_one_iff_arrowCounts word)

end GSH
