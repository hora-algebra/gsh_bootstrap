import GSH.Height.FullAlphabet
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Direct coordinates for the full-alphabet identity fibre of `D₄`

An element of `DihedralGroup 4` is either `r i` or `sr i`.  We record this
choice in `ZMod 2` and retain `i : ZMod 4` as the second coordinate.  The
recursive word coordinate below follows the actual multiplication convention
of mathlib's dihedral group.
-/

set_option autoImplicit false

namespace GSH

abbrev D4Alphabet := DihedralGroup 4

/-- Rotation/reflection coordinate. -/
def d4Phase : D4Alphabet → ZMod 2
  | .r _ => 0
  | .sr _ => 1

/-- The `ZMod 4` coordinate carried by either constructor. -/
def d4Coord : D4Alphabet → ZMod 4
  | .r i => i
  | .sr i => i

/-- Sign by which a left factor contributes after a suffix of known phase. -/
def d4Weight (phase : ZMod 2) : ZMod 4 :=
  if phase = 0 then 1 else -1

@[simp]
theorem d4Phase_mul (p q : D4Alphabet) :
    d4Phase (p * q) = d4Phase p + d4Phase q := by
  rcases p with i | i <;> rcases q with j | j <;>
    simp [d4Phase, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
  decide

@[simp]
theorem d4Coord_mul (p q : D4Alphabet) :
    d4Coord (p * q) =
      d4Coord q + d4Weight (d4Phase q) * d4Coord p := by
  rcases p with i | i <;> rcases q with j | j <;>
    simp [d4Coord, d4Phase, d4Weight, DihedralGroup.r_mul_r,
      DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
      DihedralGroup.sr_mul_sr] <;> ring

/-- The two constructor coordinates detect the identity. -/
theorem d4_eq_one_iff_coordinates (p : D4Alphabet) :
    p = 1 ↔ d4Phase p = 0 ∧ d4Coord p = 0 := by
  rcases p with i | i
  · simp only [d4Phase, d4Coord, eq_self, true_and]
    constructor
    · intro h
      rw [← DihedralGroup.r_zero] at h
      exact DihedralGroup.r.inj h
    · rintro rfl
      exact DihedralGroup.r_zero
  · simp only [d4Phase, d4Coord, one_ne_zero, false_and, iff_false]
    intro h
    rw [← DihedralGroup.r_zero] at h
    cases h

/-- The second coordinate of a word product, computed from right to left as
required by mathlib's `DihedralGroup` multiplication convention. -/
def d4WordCoord : Word D4Alphabet → ZMod 4
  | [] => 0
  | letter :: word =>
      d4WordCoord word +
        d4Weight ((word.map d4Phase).sum) * d4Coord letter

/-- The phase of a word product is the sum of its letter phases. -/
theorem d4Phase_prod_eq_sum (word : Word D4Alphabet) :
    d4Phase word.prod = (word.map d4Phase).sum := by
  induction word with
  | nil => change d4Phase (1 : D4Alphabet) = 0; rfl
  | cons letter word ih => simp [ih]

/-- The recursive word coordinate is exactly the coordinate of the product. -/
theorem d4Coord_prod_eq_wordCoord (word : Word D4Alphabet) :
    d4Coord word.prod = d4WordCoord word := by
  induction word with
  | nil => change d4Coord (1 : D4Alphabet) = 0; rfl
  | cons letter word ih =>
      simp only [List.prod_cons, d4Coord_mul, ih, d4WordCoord]
      rw [d4Phase_prod_eq_sum]

/-- Exact word-level reconstruction of the identity fibre of `D₄`. -/
theorem d4_prod_eq_one_iff_coordinates (word : Word D4Alphabet) :
    word.prod = 1 ↔
      (word.map d4Phase).sum = 0 ∧ d4WordCoord word = 0 := by
  rw [d4_eq_one_iff_coordinates, d4Phase_prod_eq_sum,
    d4Coord_prod_eq_wordCoord]

/-- The arithmetic coordinate language for the full `D₄` alphabet. -/
def d4CoordinateFiber : Language D4Alphabet :=
  {word | (word.map d4Phase).sum = 0 ∧ d4WordCoord word = 0}

/-- The full-alphabet identity fibre is exactly the coordinate language. -/
theorem fullIdentityFiber_d4_eq_coordinateFiber :
    fullIdentityFiber D4Alphabet = d4CoordinateFiber := by
  ext word
  exact (mem_fullIdentityFiber_iff word).trans
    (d4_prod_eq_one_iff_coordinates word)

end GSH
