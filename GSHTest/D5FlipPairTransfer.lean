import GSH.Height.D5FlipPairTransfer

set_option autoImplicit false

namespace GSHTest

open GSH GSH.D5FlipPairTransfer

example (x y : D5PhaseOne) :
    d5PairResidueZero x y =
      Language.concat
        (TransferCore.formula
          (D5FlipPairHeight.d5DistinguishedPairBlock x y)
          (D5FlipPairHeight.d5OtherPairBlocks x y) 5)
        D5FlipPairHeight.d5Neutral :=
  d5PairResidue_zero_eq_formula x y

example (x y : D5PhaseOne) (hne : x.1 ≠ y.1) :
    HasHeightAtMost (d5PairResidueZero x y) 1 :=
  hasHeightAtMost_d5PairResidue_zero x y hne

end GSHTest
