import GSH.GroupLanguages.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Small-group ladder

`A4` is concrete.  For the dicyclic group of order twelve, this file records
the presentation-level target without choosing a canonical mathlib model.
-/

set_option autoImplicit false

namespace GSH

/-- The alternating group on four points. -/
abbrev A4 := alternatingGroup (Fin 4)

/-- Relations for the order-twelve dicyclic presentation used in Bourne's
notation.  A concrete model should additionally prove generation and order 12. -/
def SatisfiesDic3Relations {G : Type} [Group G] (a b : G) : Prop :=
  a ^ 3 = 1 ∧ b ^ 4 = 1 ∧ b⁻¹ * a * b = a⁻¹

universe u

/-- Research target for the first unresolved alternating-group case. -/
-- API repair 2026-07-22: the alphabet universe must be bound explicitly; see
-- `HeightOneForGroup`.
def A4HeightOneTarget : Prop := HeightOneForGroup.{u} A4

end GSH
