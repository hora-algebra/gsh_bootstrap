import GSH.Language.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Recognition by finite monoids

Recognition data is a morphism from the free monoid of words and an accepting
subset.  The morphism need not be surjective.
-/

set_option autoImplicit false

namespace GSH

universe u v

structure Recognition (α : Type u) (M : Type v) [Monoid M] where
  -- API repair 2026-07-22: `List α →* M` does not elaborate because plain
  -- `List α` carries no `MulOneClass` instance in mathlib; the free monoid on
  -- `α` is `FreeMonoid α`, a definitional synonym for `List α`
  -- (`FreeMonoid.ofList` is the identity equivalence).
  morphism : FreeMonoid α →* M
  accepting : Set M

namespace Recognition

variable {α : Type u} {M : Type v} [Monoid M]

/-- The inverse image of the accepting subset. -/
def language (R : Recognition α M) : Language α :=
  {w | R.morphism (FreeMonoid.ofList w) ∈ R.accepting}

@[simp] theorem mem_language_iff (R : Recognition α M) (w : Word α) :
    w ∈ R.language ↔ R.morphism (FreeMonoid.ofList w) ∈ R.accepting := by
  rfl

end Recognition

/-- Existential recognition by a specified monoid. -/
def RecognizedBy (M : Type v) [Monoid M] {α : Type u} (L : Language α) : Prop :=
  ∃ R : Recognition α M, R.language = L

end GSH
