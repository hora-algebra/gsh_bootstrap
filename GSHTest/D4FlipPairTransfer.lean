import GSH.Height.D4FlipPairTransfer

set_option autoImplicit false

open GSH
open GSH.D4ArrowArithmetic
open GSH.D4FlipPairTransfer

example (x y : D4PhaseOne) :
    d4PairResidueZero x y =
      Language.concat
        (TransferCore.formula
          (D4FlipPairHeight.d4DistinguishedPairBlock x y)
          (D4FlipPairHeight.d4OtherPairBlocks x y) 8)
        D4FlipPairHeight.d4Neutral :=
  d4PairResidue_zero_eq_formula x y

example (x y : D4PhaseOne) (hne : x.1 ≠ y.1) :
    HasHeightAtMost (d4PairResidueZero x y) 1 :=
  hasHeightAtMost_d4PairResidue_zero x y hne
