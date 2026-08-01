import GSH.Height.D5ArrowAssembly

set_option autoImplicit false

namespace GSHTest

open GSH

example : HasHeightAtMost d5ArrowCoordinateFiber 1 :=
  hasHeightAtMost_d5ArrowCoordinateFiber

example : HasHeightAtMost
    (fullIdentityFiber (DihedralGroup 5)) 1 :=
  heightOne_fullIdentityFiber_D5

/-- Exact group-level consumer, preserving every finite alphabet,
recognizing morphism, and accepting subset. -/
example : HeightOneForGroup (DihedralGroup 5) := heightOne_D5

end GSHTest
