import GSH.Regex.Generalized
import GSH.Monoid.Syntactic

/-!
# Aperiodicity and the Schützenberger interface

The final equivalence is a blueprint declaration, not yet a formalization of
Schützenberger's theorem.
-/

set_option autoImplicit false

namespace GSH

universe u v

/-- A monoid is aperiodic when every element has an eventually idempotent power. -/
def IsAperiodicMonoid (M : Type v) [Monoid M] : Prop :=
  ∀ x : M, ∃ n : Nat, x ^ (n + 1) = x ^ n

/-- A syntactic-monoid formulation for one language. -/
def HasAperiodicSyntacticMonoid {α : Type u} (L : Language α) : Prop :=
  IsAperiodicMonoid (SyntacticMonoid L)

-- BLUEPRINT: L-SF-001
/-- Schützenberger's theorem, retained as an explicit formalization target. -/
theorem schutzenberger_interface {α : Type u} (L : Language α) (hreg : IsRegular L) :
    IsStarFree L ↔ HasAperiodicSyntacticMonoid L := by
  sorry

end GSH
