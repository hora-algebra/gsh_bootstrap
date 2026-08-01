import GSH.Height.S3FlipArrowAssembly

set_option autoImplicit false

namespace GSHTest

open GSH

/-- Compile-time acceptance for even, source-zero moving-label residues. -/
example (label : S3Alphabet) (hlabel : s3Phase label = 1)
    (residue : Fin 3) :
    HasHeightAtMost
      {word : Word S3Alphabet |
        (word.map s3Phase).sum = 0 ∧
          s3ArrowCountFrom 0 0 label word % 3 = residue.1} 1 := by
  exact hasHeightAtMost_s3FlipEvenSourceZero label hlabel residue

end GSHTest
