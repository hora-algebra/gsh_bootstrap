import GSH.Height.FiniteBoolean

/-!
# Compile-time acceptance tests for finite Boolean feature assembly
-/

set_option autoImplicit false

namespace GSHTest

open GSH

universe u v

example {α : Type u} {ι : Type v} [Fintype ι]
    (features : ι → Language α) (accept : (ι → Bool) → Prop) {n : Nat}
    (hfeatures : ∀ i, HasHeightAtMost (features i) n) :
    HasHeightAtMost
      (Language.booleanCombination features accept) n :=
  HasHeightAtMost.booleanCombination features accept hfeatures

example {α : Type u} {ι : Type v} [Fintype ι]
    (features : ι → Language α) (accept : (ι → Bool) → Prop)
    (word : Word α) :
    word ∈ Language.booleanCombination features accept ↔
      accept (Language.truthVector features word) := by
  rfl

end GSHTest
