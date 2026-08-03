import GSH.Recognition

/-!
# Acceptance tests for the syntactic quotient monoid

These examples pin the API required by obligation `L-SYN-002`: the syntactic
relation is packaged as a multiplicative congruence, its quotient carries a
proved monoid structure, and the canonical quotient map is a monoid
homomorphism whose kernel is exactly syntactic equivalence.
-/

set_option autoImplicit false

namespace GSHTest.SyntacticMonoid

open GSH

universe u

variable {α : Type u} (L : Language α)

example : Monoid (SyntacticQuotient L) := inferInstance

example (u v : Word α) :
    syntacticMorphism L (FreeMonoid.ofList (u ++ v)) =
      syntacticMorphism L (FreeMonoid.ofList u) *
        syntacticMorphism L (FreeMonoid.ofList v) := by
  simp

example : Function.Surjective (syntacticMorphism L) :=
  syntacticMorphism_surjective L

example (u v : Word α) :
    syntacticMorphism L (FreeMonoid.ofList u) =
        syntacticMorphism L (FreeMonoid.ofList v) ↔
      SyntacticEq L u v := by
  exact syntacticMorphism_eq_iff L u v

end GSHTest.SyntacticMonoid
