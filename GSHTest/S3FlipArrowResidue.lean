import GSH.Height.S3FlipArrowResidue

set_option autoImplicit false

namespace GSHTest

open GSH

/-- Every labelled arrow residue over the full six-letter alphabet. -/
example (label : S3Alphabet) (source : ZMod 2) (residue : Fin 3) :
    HasHeightAtMost
      {word : Word S3Alphabet |
        s3ArrowCountFrom 0 source label word % 3 = residue.1} 1 :=
  hasHeightAtMost_s3ArrowResidue label source residue

/-- The exact full-alphabet identity-fibre theorem. -/
example : HasHeightAtMost
    (fullIdentityFiber (Equiv.Perm (Fin 3))) 1 :=
  heightOne_fullIdentityFiber_S3

/-- Exact consumer-first theorem for the smallest noncommutative group. -/
example : HeightOneForGroup (Equiv.Perm (Fin 3)) :=
  heightOne_S3

end GSHTest
