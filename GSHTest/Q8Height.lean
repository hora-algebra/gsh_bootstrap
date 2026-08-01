import GSH.Height.Q8Height

set_option autoImplicit false

namespace GSHTest

open GSH

/-- Exact full-alphabet acceptance theorem for `Q₈`. -/
example : HasHeightAtMost (fullIdentityFiber (QuaternionGroup 2)) 1 :=
  heightOne_fullIdentityFiber_Q8

/-- Exact group theorem, retaining every finite recognizing alphabet and
every accepting subset. -/
example : HeightOneForGroup (QuaternionGroup 2) := heightOne_Q8

end GSHTest
