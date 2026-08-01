import GSH.Height.FullAlphabet
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Direct coordinates for the full-alphabet identity fibre of `D₅`

This is the `D₅`-specific word reconstruction needed by the next small-group
case.  It deliberately does not introduce a generic semidirect-product API.
-/

set_option autoImplicit false

namespace GSH

abbrev D5Alphabet := DihedralGroup 5

/-- Rotation/reflection coordinate. -/
def d5Phase : D5Alphabet → ZMod 2
  | .r _ => 0
  | .sr _ => 1

/-- The `ZMod 5` coordinate carried by either constructor. -/
def d5Coord : D5Alphabet → ZMod 5
  | .r i => i
  | .sr i => i

/-- Sign by which a left coordinate contributes after a suffix. -/
def d5Weight (phase : ZMod 2) : ZMod 5 :=
  if phase = 0 then 1 else -1

@[simp]
theorem d5Phase_mul (p q : D5Alphabet) :
    d5Phase (p * q) = d5Phase p + d5Phase q := by
  rcases p with i | i <;> rcases q with j | j <;>
    simp [d5Phase, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
  decide

@[simp]
theorem d5Coord_mul (p q : D5Alphabet) :
    d5Coord (p * q) =
      d5Coord q + d5Weight (d5Phase q) * d5Coord p := by
  rcases p with i | i <;> rcases q with j | j <;>
    simp [d5Coord, d5Phase, d5Weight, DihedralGroup.r_mul_r,
      DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
      DihedralGroup.sr_mul_sr] <;> ring

/-- The two constructor coordinates detect the identity. -/
theorem d5_eq_one_iff_coordinates (p : D5Alphabet) :
    p = 1 ↔ d5Phase p = 0 ∧ d5Coord p = 0 := by
  rcases p with i | i
  · simp only [d5Phase, d5Coord, eq_self, true_and]
    constructor
    · intro h
      rw [← DihedralGroup.r_zero] at h
      exact DihedralGroup.r.inj h
    · rintro rfl
      exact DihedralGroup.r_zero
  · simp only [d5Phase, d5Coord, one_ne_zero, false_and, iff_false]
    intro h
    rw [← DihedralGroup.r_zero] at h
    cases h

/-- The second coordinate of a word product, evaluated from right to left. -/
def d5WordCoord : Word D5Alphabet → ZMod 5
  | [] => 0
  | letter :: word =>
      d5WordCoord word +
        d5Weight ((word.map d5Phase).sum) * d5Coord letter

/-- The phase of a word product is the sum of its letter phases. -/
theorem d5Phase_prod_eq_sum (word : Word D5Alphabet) :
    d5Phase word.prod = (word.map d5Phase).sum := by
  induction word with
  | nil => change d5Phase (1 : D5Alphabet) = 0; rfl
  | cons letter word ih => simp [ih]

/-- The recursive word coordinate is exactly the product coordinate. -/
theorem d5Coord_prod_eq_wordCoord (word : Word D5Alphabet) :
    d5Coord word.prod = d5WordCoord word := by
  induction word with
  | nil => change d5Coord (1 : D5Alphabet) = 0; rfl
  | cons letter word ih =>
      simp only [List.prod_cons, d5Coord_mul, ih, d5WordCoord]
      rw [d5Phase_prod_eq_sum]

/-- Exact word-level reconstruction of the identity fibre of `D₅`. -/
theorem d5_prod_eq_one_iff_coordinates (word : Word D5Alphabet) :
    word.prod = 1 ↔
      (word.map d5Phase).sum = 0 ∧ d5WordCoord word = 0 := by
  rw [d5_eq_one_iff_coordinates, d5Phase_prod_eq_sum,
    d5Coord_prod_eq_wordCoord]

/-- The arithmetic coordinate language for the full `D₅` alphabet. -/
def d5CoordinateFiber : Language D5Alphabet :=
  {word | (word.map d5Phase).sum = 0 ∧ d5WordCoord word = 0}

/-- The full-alphabet identity fibre is exactly the coordinate language. -/
theorem fullIdentityFiber_d5_eq_coordinateFiber :
    fullIdentityFiber D5Alphabet = d5CoordinateFiber := by
  ext word
  exact (mem_fullIdentityFiber_iff word).trans
    (d5_prod_eq_one_iff_coordinates word)

end GSH
