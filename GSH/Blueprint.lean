import GSH.Groups.A5
import GSH.Groups.SmallGroups
import GSH.StarFree.Aperiodic

/-!
# Top-level theorem interfaces

These declarations are names for workshop targets.  They intentionally contain
no claim that the targets have been proved.
-/

set_option autoImplicit false

namespace GSH

universe u

/-- Global height-one collapse over finite alphabets. -/
def GeneralizedHeightOneConjecture : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α], HeightOneCollapse α

/-- Small-group milestone preceding `A_5` in the surveyed program. -/
-- API repair 2026-07-22: alphabet universe bound explicitly; see
-- `HeightOneForGroup`.
def SmallGroupMilestone : Prop := A4HeightOneTarget.{u}

/-- Non-solvable finite-group milestone. -/
def A5Milestone : Prop := A5HeightOneTarget.{u}

end GSH
