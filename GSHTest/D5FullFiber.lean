import GSH.Height.D5FullFiber

set_option autoImplicit false

namespace GSHTest

open GSH

/-- Exact word-level parent for the `D₅` full identity fibre. -/
example : fullIdentityFiber (DihedralGroup 5) = d5CoordinateFiber :=
  fullIdentityFiber_d5_eq_coordinateFiber

/-- Exact quantifier-preserving consumer for the next height theorem. -/
example (h : HasHeightAtMost
    (fullIdentityFiber (DihedralGroup 5)) 1) :
    HeightOneForGroup (DihedralGroup 5) :=
  heightOneForGroup_of_fullIdentityFiber h

end GSHTest
