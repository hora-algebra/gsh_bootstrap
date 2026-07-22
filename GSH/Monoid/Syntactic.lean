import GSH.Language.Basic
import Mathlib.Algebra.Group.Defs

/-!
# Syntactic congruence

The quotient-monoid instance is deliberately isolated: the contextual
relation must first be proved to be a two-sided congruence.
-/

set_option autoImplicit false

namespace GSH

universe u

/-- Two words are syntactically equivalent when every two-sided context gives
the same membership answer. -/
def SyntacticEq {α : Type u} (L : Language α) (u v : Word α) : Prop :=
  ∀ x y : Word α, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L

namespace SyntacticEq

variable {α : Type u} {L : Language α} {u v w : Word α}

@[refl] theorem refl (u : Word α) : SyntacticEq L u u := by
  intro x y
  rfl

@[symm] theorem symm (h : SyntacticEq L u v) : SyntacticEq L v u := by
  intro x y
  exact (h x y).symm

@[trans] theorem trans (h₁ : SyntacticEq L u v) (h₂ : SyntacticEq L v w) :
    SyntacticEq L u w := by
  intro x y
  exact (h₁ x y).trans (h₂ x y)

/-- Compatibility with appending the same prefix. -/
theorem append_left (p : Word α) (h : SyntacticEq L u v) :
    SyntacticEq L (p ++ u) (p ++ v) := by
  intro x y
  simpa [List.append_assoc] using h (x ++ p) y

/-- Compatibility with appending the same suffix. -/
theorem append_right (q : Word α) (h : SyntacticEq L u v) :
    SyntacticEq L (u ++ q) (v ++ q) := by
  intro x y
  simpa [List.append_assoc] using h x (q ++ y)

/-- Two-sided compatibility for word multiplication. -/
theorem append_congr {u' v' : Word α}
    (hu : SyntacticEq L u u') (hv : SyntacticEq L v v') :
    SyntacticEq L (u ++ v) (u' ++ v') := by
  exact (append_right v hu).trans (append_left u' hv)

end SyntacticEq

/-- The setoid underlying the syntactic quotient. -/
def syntacticSetoid {α : Type u} (L : Language α) : Setoid (Word α) where
  r := SyntacticEq L
  iseqv := ⟨SyntacticEq.refl, SyntacticEq.symm, SyntacticEq.trans⟩

/-- The carrier of the syntactic monoid. -/
abbrev SyntacticMonoid {α : Type u} (L : Language α) :=
  Quotient (syntacticSetoid L)

-- BLUEPRINT: L-SYN-002
/-- The quotient monoid structure induced by two-sided congruence. -/
instance syntacticMonoidInst {α : Type u} (L : Language α) :
    Monoid (SyntacticMonoid L) := by
  sorry

end GSH
