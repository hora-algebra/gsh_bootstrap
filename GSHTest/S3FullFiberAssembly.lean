import GSH.Height.S3FullFiberAssembly

set_option autoImplicit false

namespace GSHTest

open GSH

/-- Exact consumer-first bridge from all arrow-residue features to the full
`S₃` identity fibre. -/
example
    (harrow : ∀ (label : S3Alphabet) (source : ZMod 2) (residue : Fin 3),
      HasHeightAtMost
        {word : Word S3Alphabet |
          s3ArrowCountFrom 0 source label word % 3 = residue.1} 1) :
    HasHeightAtMost (fullIdentityFiber S3Alphabet) 1 :=
  hasHeightAtMost_fullIdentityFiber_S3_of_arrowResidues harrow

/-- The exact quantified group theorem follows from the same finite feature
family. -/
example
    (harrow : ∀ (label : S3Alphabet) (source : ZMod 2) (residue : Fin 3),
      HasHeightAtMost
        {word : Word S3Alphabet |
          s3ArrowCountFrom 0 source label word % 3 = residue.1} 1) :
    HeightOneForGroup S3Alphabet :=
  heightOne_S3_of_arrowResidues harrow

end GSHTest
