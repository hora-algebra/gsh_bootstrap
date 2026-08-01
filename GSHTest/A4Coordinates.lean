import GSH.Height.A4Coordinates

/-! Consumer-first checks for the exact `A₄` residual-coordinate state. -/

set_option autoImplicit false

open GSH

example (word : Word A4) :
    a4VectorPart word.prod = (a4VectorFromPhaseLabelCounts word : A4) :=
  a4VectorPart_prod_eq_phaseLabelCounts word

example : a4V4CoordinateFiber = a4PhaseLabelCoordinateFiber :=
  a4V4CoordinateFiber_eq_phaseLabelCoordinateFiber

-- Exact next parent: prove height one for this count-state zero cell.
example (h : HasHeightAtMost a4PhaseLabelCoordinateFiber 1) :
    HasHeightAtMost a4V4CoordinateFiber 1 := by
  rw [a4V4CoordinateFiber_eq_phaseLabelCoordinateFiber]
  exact h
