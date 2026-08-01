import GSH.Groups
import GSH.Groups.Abelian
import GSH.Height.FullAlphabet
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-!
# Phase and residual coordinates for `A₄`

The direct full-alphabet proof for `A₄ = V₄ ⋊ C₃` separates the explicit
`ZMod 3` phase from the remaining `V₄` coordinate.  This file closes the phase
half in Lean and proves the exact intersection by which the residual
coordinate feeds the full identity fibre.

This does not import the finite Python evidence for the remaining coordinate.
-/

set_option autoImplicit false

namespace GSH

/-- The canonical Klein four subgroup of `A₄`. -/
abbrev A4Klein : Subgroup A4 := alternatingGroup.kleinFour (Fin 4)

instance : A4Klein.Normal :=
  alternatingGroup.normal_kleinFour (by simp)

/-- The fixed three-cycle used in the normal form `g = v(g) t ^ ε(g)`. -/
def a4T : A4 :=
  ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap (1 : Fin 4) 2, by simp⟩

private def a4V01 : A4 :=
  ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3, by simp⟩

private def a4V02 : A4 :=
  ⟨Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3, by simp⟩

private def a4V03 : A4 :=
  ⟨Equiv.swap (0 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2, by simp⟩

/-- Executable membership in the four concrete elements of `V₄`. -/
def a4InKlein (g : A4) : Bool :=
  decide (g = 1 ∨ g = a4V01 ∨ g = a4V02 ∨ g = a4V03)

/-- The explicit exponent `ε(g) ∈ ZMod 3` in `g = v(g) t ^ ε(g)`. -/
def a4PhaseValue (g : A4) : ZMod 3 :=
  if a4InKlein g then 0
  else if a4InKlein (g * a4T⁻¹) then 1 else 2

/-- The explicit phase homomorphism `A₄ → C₃`. -/
def a4Phase : A4 →* Multiplicative (ZMod 3) where
  toFun g := Multiplicative.ofAdd (a4PhaseValue g)
  map_one' := by decide
  map_mul' := by
    intro x y
    revert x y
    decide

/-- The `V₄` coordinate in the normal form `g = v(g) t ^ ε(g)`. -/
def a4VectorPart (g : A4) : A4 :=
  g * (a4T ^ (a4PhaseValue g).val)⁻¹

/-- The explicit coordinates reconstruct every element of `A₄`. -/
theorem a4_vectorPart_mul_phase (g : A4) :
    a4VectorPart g * a4T ^ (a4PhaseValue g).val = g := by
  revert g
  decide

/-- The two coordinates detect the identity exactly. -/
theorem a4_eq_one_iff_coordinates (g : A4) :
    g = 1 ↔ a4Phase g = 1 ∧ a4VectorPart g = 1 := by
  revert g
  decide

/-- Words whose accumulated `ZMod 3` phase is zero. -/
def a4PhaseFiber : Language A4 :=
  (Recognition.mk (FreeMonoid.lift a4Phase)
    ({1} : Set (Multiplicative (ZMod 3)))).language

/-- The quotient phase of a word is the quotient of its product. -/
theorem mem_a4PhaseFiber_iff (word : Word A4) :
    word ∈ a4PhaseFiber ↔ a4Phase word.prod = 1 := by
  simp [a4PhaseFiber, Recognition.language, FreeMonoid.lift_ofList,
    map_list_prod]

/-- Words whose residual `V₄` coordinate is zero.  Proving height one for this
language is the remaining coordinate obligation. -/
def a4V4CoordinateFiber : Language A4 :=
  {word | a4VectorPart word.prod = 1}

@[simp] theorem mem_a4V4CoordinateFiber_iff (word : Word A4) :
    word ∈ a4V4CoordinateFiber ↔ a4VectorPart word.prod = 1 := Iff.rfl

/-- The full identity fibre is exactly the intersection of its phase-zero and
residual-coordinate-zero conditions. -/
theorem fullIdentityFiber_A4_eq_phase_inter_v4 :
    fullIdentityFiber A4 = a4PhaseFiber ∩ a4V4CoordinateFiber := by
  ext word
  rw [mem_fullIdentityFiber_iff, Set.mem_inter_iff,
    mem_a4PhaseFiber_iff, mem_a4V4CoordinateFiber_iff]
  exact a4_eq_one_iff_coordinates word.prod

/-- The `C₃`-phase part of the full-alphabet `A₄` construction already has
generalized star height at most one. -/
theorem hasHeightAtMost_a4PhaseFiber :
    HasHeightAtMost a4PhaseFiber 1 := by
  exact heightOne_of_commGroup (Multiplicative (ZMod 3)) A4
    (Recognition.mk (FreeMonoid.lift a4Phase)
      ({1} : Set (Multiplicative (ZMod 3))))

/-- Exact consumer of the phase theorem: once the residual `V₄` coordinate
language has height at most one, so does the full identity fibre. -/
theorem heightOne_fullIdentityFiber_A4_of_v4
    (hV4 : HasHeightAtMost a4V4CoordinateFiber 1) :
    HasHeightAtMost (fullIdentityFiber A4) 1 := by
  rw [fullIdentityFiber_A4_eq_phase_inter_v4]
  exact hasHeightAtMost_a4PhaseFiber.inter hV4

end GSH
