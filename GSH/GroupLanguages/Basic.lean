import GSH.Regex.Generalized
import GSH.Monoid.Recognition
import Mathlib.Data.Fintype.Basic

/-!
# Height-one statements for recognizing monoids and groups
-/

set_option autoImplicit false

namespace GSH

universe u v

/-- Every language recognized by `M` has a height-one certificate. -/
def HeightOneForMonoid (M : Type v) [Monoid M] : Prop :=
  ∀ (α : Type u) [Fintype α] [DecidableEq α],
    ∀ R : Recognition α M, HasHeightAtMost R.language 1

/-- Group-specialized name for the same recognition property. -/
-- API repair 2026-07-22: the alphabet universe `u` quantified inside
-- `HeightOneForMonoid` must be bound explicitly here, otherwise it is left as
-- a universe metavariable.
def HeightOneForGroup (G : Type v) [Group G] : Prop :=
  HeightOneForMonoid.{u, v} G

end GSH
