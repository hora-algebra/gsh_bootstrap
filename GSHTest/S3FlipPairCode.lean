import GSH.Height.S3FlipPairCode

set_option autoImplicit false

namespace GSHTest

open GSH
open GSH.S3FlipPairCode

/-- Universal acceptance for existence of the phase-one pair code. -/
example (word : Word S3Alphabet) (hphase : (word.map s3Phase).sum = 0) :
    ∃ pieces suffix, IsPairFactorization pieces suffix word :=
  exists_pairFactorization word hphase

/-- Universal acceptance for the distinguished ordered-pair count. -/
example (x y : S3ArrowArithmetic.S3PhaseOne)
    (pieces : List (Word S3Alphabet)) (suffix word : Word S3Alphabet)
    (hfactor : IsPairFactorization pieces suffix word) :
    pairBlockCount x y pieces =
      S3ArrowArithmetic.pairCountOf x y
        (S3ArrowArithmetic.phaseOneSubword word) :=
  pairBlockCount_eq_pairCountOf x y pieces suffix word hfactor

/-- Universal acceptance for uniqueness of block/suffix factorization. -/
example (leftPieces rightPieces : List (Word S3Alphabet))
    (leftSuffix rightSuffix word : Word S3Alphabet)
    (hleft : IsPairFactorization leftPieces leftSuffix word)
    (hright : IsPairFactorization rightPieces rightSuffix word) :
    leftPieces = rightPieces ∧ leftSuffix = rightSuffix :=
  pairFactorization_unique leftPieces rightPieces leftSuffix rightSuffix word
    hleft hright

end GSHTest
