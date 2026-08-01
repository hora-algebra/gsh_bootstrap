import GSH.Height.D5FlipPairHeight

set_option autoImplicit false

namespace GSHTest

open GSH GSH.D5FlipPairHeight

example (x y : D5PhaseOne) (hne : x.1 ≠ y.1) :
    HasHeightAtMost
      (TransferCore.formula (d5DistinguishedPairBlock x y)
        (d5OtherPairBlocks x y) 5) 1 :=
  hasHeightAtMost_d5PairFormula x y hne

end GSHTest
