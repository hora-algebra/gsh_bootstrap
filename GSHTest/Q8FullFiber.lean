import GSH.Height.Q8FullFiber

set_option autoImplicit false

namespace GSHTest

open GSH

/-- Exact word-level parent required before any height argument. -/
example : fullIdentityFiber Q8Alphabet = q8CoordinateFiber :=
  fullIdentityFiber_q8_eq_coordinateFiber

/-- The exact D₄ transport correction consumed by the next height proof. -/
example (word : Word Q8Alphabet) :
    word.prod = 1 ↔
      (q8FlipCount word % 4 = 0 ∧
          (word.map q8ToD4).prod = 1) ∨
        (q8FlipCount word % 4 = 2 ∧
          (word.map q8ToD4).prod = DihedralGroup.r (2 : ZMod 4)) :=
  q8_prod_eq_one_iff_correctedD4 word

/-- Negative control: the letter map to `D₄` is not a group homomorphism;
the central correction in the preceding theorem is essential. -/
example :
    q8ToD4 ((QuaternionGroup.xa 0 : Q8Alphabet) * QuaternionGroup.xa 0) ≠
      q8ToD4 (QuaternionGroup.xa 0 : Q8Alphabet) *
        q8ToD4 (QuaternionGroup.xa 0 : Q8Alphabet) := by
  decide

/-- Exact quantifier-preserving group consumer for the next height theorem. -/
example (h : HasHeightAtMost (fullIdentityFiber Q8Alphabet) 1) :
    HeightOneForGroup (QuaternionGroup 2) :=
  heightOneForGroup_of_fullIdentityFiber h

end GSHTest
