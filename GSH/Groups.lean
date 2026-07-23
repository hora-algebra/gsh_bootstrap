import GSH.Recognition
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Concrete groups and top-level group targets

This file collects the surveyed finite groups and the named workshop targets
in one place (consolidated 2026-07-23 from `GSH/Groups/SmallGroups.lean`,
`GSH/Groups/A5.lean`, and `GSH/Blueprint.lean`, definitions unchanged).

`A4` is concrete.  For the dicyclic group of order twelve, this file records
the presentation-level target without choosing a canonical mathlib model.
The target declarations intentionally contain no claim that the targets have
been proved.

The global conjecture `GeneralizedHeightOneConjecture` lives with its whole
definition chain in `GSH/Challenges/GeneralizedStarHeight.lean`.
-/

set_option autoImplicit false

namespace GSH

universe u

/-! ### The small-group ladder -/

/-- The alternating group on four points. -/
abbrev A4 := alternatingGroup (Fin 4)

/-- Relations for the order-twelve dicyclic presentation used in Bourne's
notation.  A concrete model should additionally prove generation and order 12. -/
def SatisfiesDic3Relations {G : Type} [Group G] (a b : G) : Prop :=
  a ^ 3 = 1 ∧ b ^ 4 = 1 ∧ b⁻¹ * a * b = a⁻¹

/-- Research target for the first unresolved alternating-group case. -/
-- API repair 2026-07-22: the alphabet universe must be bound explicitly; see
-- `HeightOneForGroup`.
def A4HeightOneTarget : Prop := HeightOneForGroup.{u} A4

/-! ### The alternating group `A_5` -/

/-- Mathlib's canonical concrete realization of `A_5`. -/
abbrev A5 := alternatingGroup (Fin 5)

/-- `A_5` is simple; this is existing mathlib infrastructure, not a result of
this project. -/
theorem a5_isSimple : IsSimpleGroup A5 := by
  -- API repair 2026-07-22: the hypothesis `5 ≤ Nat.card (Fin 5)` is not
  -- decidable-by-reduction because `Nat.card` is classically defined; mathlib
  -- discharges the same goal with `simp` (`Nat.card_fin`).
  simpa [A5] using
    (alternatingGroup.isSimpleGroup (α := Fin 5) (by simp))

/-- The ambitious finite-group target. -/
-- API repair 2026-07-22: the alphabet universe must be bound explicitly; see
-- `HeightOneForGroup`.
def A5HeightOneTarget : Prop := HeightOneForGroup.{u} A5

/-! ### Named workshop milestones -/

/-- Small-group milestone preceding `A_5` in the surveyed program. -/
-- API repair 2026-07-22: alphabet universe bound explicitly; see
-- `HeightOneForGroup`.
def SmallGroupMilestone : Prop := A4HeightOneTarget.{u}

/-- Non-solvable finite-group milestone. -/
def A5Milestone : Prop := A5HeightOneTarget.{u}

end GSH
