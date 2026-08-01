import GSH.Height.S3FlipPairQuotients

set_option autoImplicit false

namespace GSHTest

open GSH
open GSH.S3ArrowArithmetic
open GSH.S3FlipPairQuotients

example (x y : S3PhaseOne) :
    s3PairResidue x y 0 = GSH.S3FlipPairTransfer.s3PairResidueZero x y := by
  exact s3PairResidue_zero x y

example (x y : S3PhaseOne) (hne : x.1 ≠ y.1) :
    Language.leftQuotient y.1
        (Language.leftQuotient x.1 (s3PairResidue x y 0)) =
      s3PairResidue x y 2 := by
  exact leftQuotient_pair_zero_eq_two x y hne

example (x y : S3PhaseOne) (hne : x.1 ≠ y.1) :
    Language.leftQuotient y.1
        (Language.leftQuotient x.1
          (Language.leftQuotient y.1
            (Language.leftQuotient x.1 (s3PairResidue x y 0)))) =
      s3PairResidue x y 1 := by
  exact leftQuotient_pair_twice_zero_eq_one x y hne

/-- Compile-time consumer for all three fixed-pair residues. -/
example (x y : S3PhaseOne) (hne : x.1 ≠ y.1) (residue : Fin 3) :
    HasHeightAtMost (s3PairResidue x y residue.1) 1 := by
  exact hasHeightAtMost_s3PairResidue x y hne residue

end GSHTest
