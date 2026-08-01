import GSH.Height.S3FlipSourceOne

set_option autoImplicit false

namespace GSHTest

open GSH

example (label : S3Alphabet) (residue : Fin 3) :
    s3FlipSourceOneAssembly label residue =
      s3FlipEvenSourceOneResidue label residue.1 := by
  exact s3FlipSourceOneAssembly_eq label residue

example (label : S3Alphabet) (hlabel : s3Phase label = 1)
    (residue : Fin 3) :
    HasHeightAtMost
      (s3FlipEvenSourceOneResidue label residue.1) 1 := by
  exact hasHeightAtMost_s3FlipEvenSourceOne label hlabel residue

/-- Compile-time acceptance for either moving-edge source state. -/
example (label : S3Alphabet) (hlabel : s3Phase label = 1)
    (source : ZMod 2) (residue : Fin 3) :
    HasHeightAtMost
      {word : Word S3Alphabet |
        (word.map s3Phase).sum = 0 ∧
          s3ArrowCountFrom 0 source label word % 3 = residue.1} 1 := by
  exact hasHeightAtMost_s3FlipEven label hlabel source residue

end GSHTest
