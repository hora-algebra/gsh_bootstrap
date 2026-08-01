import GSH.Height.D4FlipPairHeight

set_option autoImplicit false

namespace GSHTest

open GSH
open GSH.D4ArrowArithmetic
open GSH.D4FlipPairHeight

/-- The neutral suffix required by the D₄ pair transfer is star-free. -/
example : IsStarFree d4Neutral := by
  exact d4Neutral_starFree

/-- Tracked consumer for the modulus-eight formula height theorem. -/
example (x y : D4PhaseOne) (hne : x.1 ≠ y.1) :
    HasHeightAtMost
      (TransferCore.formula (d4DistinguishedPairBlock x y)
        (d4OtherPairBlocks x y) 8) 1 := by
  exact hasHeightAtMost_d4PairFormula x y hne

end GSHTest
