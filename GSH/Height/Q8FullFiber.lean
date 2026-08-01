import GSH.Height.D4FullFiber
import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Direct coordinates for the full-alphabet identity fibre of `Q₈`

Mathlib writes the quaternion group as `QuaternionGroup 2`, with elements
`a i` and `xa i`, `i : ZMod 4`.  The constructor bit is a `ZMod 2` phase.
Unlike the dihedral group, multiplying two `xa` constructors contributes the
central cocycle `2 : ZMod 4`; the recursive word coordinate below records
that cocycle exactly.
-/

set_option autoImplicit false

namespace GSH

abbrev Q8Alphabet := QuaternionGroup 2

/-- The two quaternion constructors as an additive `C₂` phase. -/
def q8Phase : Q8Alphabet → ZMod 2
  | .a _ => 0
  | .xa _ => 1

/-- The `ZMod 4` coordinate carried by either quaternion constructor. -/
def q8Coord : Q8Alphabet → ZMod 4
  | .a i => i
  | .xa i => i

/-- The sign acting on a left coordinate after a suffix of known phase. -/
def q8Weight (phase : ZMod 2) : ZMod 4 :=
  if phase = 0 then 1 else -1

/-- The central quaternion cocycle: it is two exactly when both factors are
in the `xa` constructor. -/
def q8Twist (left right : ZMod 2) : ZMod 4 :=
  if left = 1 ∧ right = 1 then 2 else 0

@[simp]
theorem q8Phase_mul (p q : Q8Alphabet) :
    q8Phase (p * q) = q8Phase p + q8Phase q := by
  rcases p with i | i <;> rcases q with j | j <;>
    simp [q8Phase, QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_xa,
      QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa]
  decide

@[simp]
theorem q8Coord_mul (p q : Q8Alphabet) :
    q8Coord (p * q) =
      q8Coord q + q8Weight (q8Phase q) * q8Coord p +
        q8Twist (q8Phase p) (q8Phase q) := by
  rcases p with i | i <;> rcases q with j | j <;>
    simp [q8Coord, q8Phase, q8Weight, q8Twist,
      QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_xa,
      QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa] <;> ring

/-- Phase and coordinate detect the identity of `Q₈`. -/
theorem q8_eq_one_iff_coordinates (p : Q8Alphabet) :
    p = 1 ↔ q8Phase p = 0 ∧ q8Coord p = 0 := by
  rcases p with i | i
  · simp only [q8Phase, q8Coord, eq_self, true_and]
    constructor
    · intro h
      rw [QuaternionGroup.one_def] at h
      exact QuaternionGroup.a.inj h
    · rintro rfl
      exact QuaternionGroup.a_zero
  · simp only [q8Phase, q8Coord, one_ne_zero, false_and, iff_false]
    intro h
    rw [QuaternionGroup.one_def] at h
    cases h

/-- The second coordinate of a quaternion word product, evaluated from the
right so that both the suffix sign and the central cocycle are explicit. -/
def q8WordCoord : Word Q8Alphabet → ZMod 4
  | [] => 0
  | letter :: word =>
      q8WordCoord word +
        q8Weight ((word.map q8Phase).sum) * q8Coord letter +
          q8Twist (q8Phase letter) ((word.map q8Phase).sum)

/-- Forget the quaternion cocycle while retaining constructor and coordinate.
This is only a letter map; it is deliberately not claimed to be a group
homomorphism. -/
def q8ToD4 : Q8Alphabet → D4Alphabet
  | .a i => .r i
  | .xa i => .sr i

@[simp] theorem d4Phase_q8ToD4 (p : Q8Alphabet) :
    d4Phase (q8ToD4 p) = q8Phase p := by cases p <;> rfl

@[simp] theorem d4Coord_q8ToD4 (p : Q8Alphabet) :
    d4Coord (q8ToD4 p) = q8Coord p := by cases p <;> rfl

/-- Number of `xa` letters in a quaternion word. -/
def q8FlipCount : Word Q8Alphabet → Nat
  | [] => 0
  | .a _ :: word => q8FlipCount word
  | .xa _ :: word => q8FlipCount word + 1

/-- The accumulated central cocycle in a quaternion word. -/
def q8WordTwist : Word Q8Alphabet → ZMod 4
  | [] => 0
  | letter :: word =>
      q8WordTwist word +
        q8Twist (q8Phase letter) ((word.map q8Phase).sum)

/-- The constructor phase is the parity of the number of `xa` letters. -/
theorem q8Phase_sum_eq_flipCount (word : Word Q8Alphabet) :
    (word.map q8Phase).sum = (q8FlipCount word : ZMod 2) := by
  induction word with
  | nil => rfl
  | cons letter word ih =>
      rcases letter with i | i
      · simpa [q8FlipCount, q8Phase] using ih
      · simp only [List.map_cons, List.sum_cons, q8Phase, q8FlipCount, ih]
        push_cast
        ring

/-- Quaternion and dihedral word coordinates differ exactly by the central
cocycle accumulated from pairs of flip letters. -/
theorem q8WordCoord_eq_d4WordCoord_add_twist (word : Word Q8Alphabet) :
    q8WordCoord word =
      d4WordCoord (word.map q8ToD4) + q8WordTwist word := by
  induction word with
  | nil => rfl
  | cons letter word ih =>
      simp [q8WordCoord, q8WordTwist, d4WordCoord, ih,
        q8Weight, d4Weight]
      have hf : d4Phase ∘ q8ToD4 = q8Phase := by
        funext p
        exact d4Phase_q8ToD4 p
      rw [hf]
      ring

/-- The two possible central corrections, selected by the total flip count
modulo four. -/
def q8Correction (count : Nat) : ZMod 4 :=
  if count % 4 = 0 ∨ count % 4 = 1 then 0 else 2

private theorem q8Correction_succ (count : Nat) :
    q8Correction (count + 1) = q8Correction count +
      q8Twist 1 (count : ZMod 2) := by
  have hlt : count % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases h : count % 4
  all_goals have h2 : count % 2 = (count % 4) % 2 := by omega
  all_goals rw [← ZMod.natCast_mod count 2, h2]
  all_goals simp [q8Correction, q8Twist, Nat.add_mod, h]
  all_goals decide

/-- The accumulated cocycle depends only on the flip count modulo four. -/
theorem q8WordTwist_eq_correction (word : Word Q8Alphabet) :
    q8WordTwist word = q8Correction (q8FlipCount word) := by
  induction word with
  | nil => rfl
  | cons letter word ih =>
      rcases letter with i | i
      · simpa [q8WordTwist, q8FlipCount, q8Twist, q8Phase] using ih
      · simp only [q8WordTwist, q8FlipCount, q8Phase,
          q8Phase_sum_eq_flipCount, ih]
        rw [q8Correction_succ]

/-- A rotation by two is detected by the same two coordinates as the
identity, with second coordinate two instead of zero. -/
theorem d4_eq_r_two_iff_coordinates (p : D4Alphabet) :
    p = DihedralGroup.r (2 : ZMod 4) ↔
      d4Phase p = 0 ∧ d4Coord p = 2 := by
  rcases p with i | i
  · simp only [d4Phase, d4Coord, eq_self, true_and]
    simp
  · simp only [d4Phase, d4Coord, one_ne_zero, false_and, iff_false]
    intro h
    cases h

/-- The constructor phase of a word product is the sum of letter phases. -/
theorem q8Phase_prod_eq_sum (word : Word Q8Alphabet) :
    q8Phase word.prod = (word.map q8Phase).sum := by
  induction word with
  | nil => change q8Phase (1 : Q8Alphabet) = 0; rfl
  | cons letter word ih => simp [ih]

/-- The recursive coordinate is exactly the coordinate of the word product. -/
theorem q8Coord_prod_eq_wordCoord (word : Word Q8Alphabet) :
    q8Coord word.prod = q8WordCoord word := by
  induction word with
  | nil => change q8Coord (1 : Q8Alphabet) = 0; rfl
  | cons letter word ih =>
      simp only [List.prod_cons, q8Coord_mul, ih, q8WordCoord]
      rw [q8Phase_prod_eq_sum]

/-- Exact word-level reconstruction of the identity fibre of `Q₈`. -/
theorem q8_prod_eq_one_iff_coordinates (word : Word Q8Alphabet) :
    word.prod = 1 ↔
      (word.map q8Phase).sum = 0 ∧ q8WordCoord word = 0 := by
  rw [q8_eq_one_iff_coordinates, q8Phase_prod_eq_sum,
    q8Coord_prod_eq_wordCoord]

/-- Exact correction to the tempting but false transport of the `Q₈`
identity fibre to `D₄`.  For phase-zero words the only possibilities are:
zero flip letters modulo four and dihedral product `1`, or two flip letters
modulo four and dihedral product `r 2`. -/
theorem q8_prod_eq_one_iff_correctedD4 (word : Word Q8Alphabet) :
    word.prod = 1 ↔
      (q8FlipCount word % 4 = 0 ∧
          (word.map q8ToD4).prod = 1) ∨
        (q8FlipCount word % 4 = 2 ∧
          (word.map q8ToD4).prod = DihedralGroup.r (2 : ZMod 4)) := by
  rw [q8_prod_eq_one_iff_coordinates, q8Phase_sum_eq_flipCount,
    q8WordCoord_eq_d4WordCoord_add_twist,
    q8WordTwist_eq_correction]
  rw [d4_eq_one_iff_coordinates, d4_eq_r_two_iff_coordinates,
    d4Phase_prod_eq_sum, d4Coord_prod_eq_wordCoord]
  have hphase : ((word.map q8ToD4).map d4Phase).sum =
      (word.map q8Phase).sum := by
    have hf : d4Phase ∘ q8ToD4 = q8Phase := by
      funext p
      exact d4Phase_q8ToD4 p
    simp [hf]
  rw [hphase, q8Phase_sum_eq_flipCount]
  have hlt : q8FlipCount word % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases h : q8FlipCount word % 4
  all_goals have h2 : q8FlipCount word % 2 =
      (q8FlipCount word % 4) % 2 := by omega
  all_goals rw [← ZMod.natCast_mod (q8FlipCount word) 2, h2, h]
  all_goals simp [q8Correction, h]
  all_goals have htwo : (2 : ZMod 4) + 2 = 0 := by decide
  all_goals constructor <;> intro hcoord
  · calc
      d4WordCoord (word.map q8ToD4) =
          (d4WordCoord (word.map q8ToD4) + 2) + 2 := by
            rw [add_assoc, htwo, add_zero]
      _ = 0 + 2 := by rw [hcoord]
      _ = 2 := zero_add _
  · simpa [hcoord] using htwo

/-- The arithmetic coordinate language for the full `Q₈` alphabet. -/
def q8CoordinateFiber : Language Q8Alphabet :=
  {word | (word.map q8Phase).sum = 0 ∧ q8WordCoord word = 0}

/-- The full-alphabet identity fibre is exactly the quaternion coordinate
language. -/
theorem fullIdentityFiber_q8_eq_coordinateFiber :
    fullIdentityFiber Q8Alphabet = q8CoordinateFiber := by
  ext word
  exact (mem_fullIdentityFiber_iff word).trans
    (q8_prod_eq_one_iff_coordinates word)

end GSH
