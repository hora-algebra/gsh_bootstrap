import GSH.GroupLanguages.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The alternating group `A_5`
-/

set_option autoImplicit false

namespace GSH

/-- Mathlib's canonical concrete realization of `A_5`. -/
abbrev A5 := alternatingGroup (Fin 5)

/-- `A_5` is simple; this is existing mathlib infrastructure, not a result of
this project. -/
theorem a5_isSimple : IsSimpleGroup A5 := by
  simpa [A5] using
    (alternatingGroup.isSimpleGroup (α := Fin 5) (by decide))

universe u

/-- The ambitious finite-group target. -/
-- API repair 2026-07-22: the alphabet universe must be bound explicitly; see
-- `HeightOneForGroup`.
def A5HeightOneTarget : Prop := HeightOneForGroup.{u} A5

end GSH
