import GSH.Height.S3FlipPairTransfer

set_option autoImplicit false

namespace GSHTest

open GSH
open GSH.S3ArrowArithmetic
open GSH.S3FlipPairTransfer

/-- Compile-time acceptance test for the exact zero-residue pair language. -/
example (x y : S3PhaseOne) :
    s3PairResidueZero x y =
      Language.concat
        (TransferCore.formula (distinguishedPairBlock x y)
          (otherPairBlocks x y) 3)
        neutralWords := by
  exact s3PairResidue_zero_eq_formula x y

/-- Height-one consumer for a distinct phase-one pair. -/
example (x y : S3PhaseOne) (hne : x.1 ≠ y.1) :
    HasHeightAtMost (s3PairResidueZero x y) 1 := by
  exact hasHeightAtMost_s3PairResidue_zero x y hne

end GSHTest
