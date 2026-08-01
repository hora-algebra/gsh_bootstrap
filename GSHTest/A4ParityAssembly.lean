import GSH.Height.A4ParityAssembly

/-! Consumer-first acceptance tests for the `A₄` parity assembly. -/

set_option autoImplicit false

open GSH

example : a4ParityAssembly = a4PhaseLabelCoordinateFiber :=
  a4ParityAssembly_eq

example
    (hfeatures : ∀ event : ZMod 3 × A4,
      HasHeightAtMost (a4PhaseLabelParityFeature event) 1) :
    HasHeightAtMost a4PhaseLabelCoordinateFiber 1 :=
  hasHeightAtMost_a4Coordinate_of_parities hfeatures

example
    (hfeatures : ∀ event : ZMod 3 × A4,
      HasHeightAtMost (a4PhaseLabelParityFeature event) 1) :
    HeightOneForGroup A4 :=
  heightOne_A4_of_parities hfeatures
