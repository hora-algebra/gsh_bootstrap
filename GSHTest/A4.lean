import GSH.Groups.A4

/-! Consumer-first checks for the first Lean component of the `A₄` target. -/

set_option autoImplicit false

open GSH

example (g : A4) :
    a4VectorPart g * a4T ^ (a4PhaseValue g).val = g :=
  a4_vectorPart_mul_phase g

example : fullIdentityFiber A4 = a4PhaseFiber ∩ a4V4CoordinateFiber :=
  fullIdentityFiber_A4_eq_phase_inter_v4

example : HasHeightAtMost a4PhaseFiber 1 :=
  hasHeightAtMost_a4PhaseFiber

-- Exact next parent: the remaining open step is exactly the `V₄` coordinate.
example (hV4 : HasHeightAtMost a4V4CoordinateFiber 1) :
    HasHeightAtMost (fullIdentityFiber A4) 1 :=
  heightOne_fullIdentityFiber_A4_of_v4 hV4

example (hV4 : HasHeightAtMost a4V4CoordinateFiber 1) :
    HeightOneForGroup A4 :=
  heightOneForGroup_of_fullIdentityFiber
    (heightOne_fullIdentityFiber_A4_of_v4 hV4)
