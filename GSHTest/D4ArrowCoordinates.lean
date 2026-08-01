import GSH.Height.D4ArrowCoordinates

set_option autoImplicit false

namespace GSHTest

open GSH

/-- Prefix arrow counts reconstruct the signed `ZMod 4` coordinate. -/
example (word : Word D4Alphabet) :
    d4Beta word.prod = d4BetaByArrows word := by
  exact d4Beta_prod_eq_arrowCounts word

/-- Exact full-alphabet identity fibre in prefix arrow coordinates. -/
example :
    fullIdentityFiber D4Alphabet = d4ArrowCoordinateFiber := by
  exact fullIdentityFiber_d4_eq_arrowCoordinateFiber

end GSHTest
