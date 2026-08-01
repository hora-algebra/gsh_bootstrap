import GSH.Height.D4FullFiber

set_option autoImplicit false

namespace GSHTest

open GSH

/-- Compile-time acceptance for the exact word-level `D₄` coordinates. -/
example (word : Word (DihedralGroup 4)) :
    word.prod = 1 ↔
      (word.map d4Phase).sum = 0 ∧ d4WordCoord word = 0 := by
  exact d4_prod_eq_one_iff_coordinates word

/-- The coordinate language is exactly the full-alphabet identity fibre. -/
example :
    fullIdentityFiber (DihedralGroup 4) = d4CoordinateFiber := by
  exact fullIdentityFiber_d4_eq_coordinateFiber

end GSHTest
