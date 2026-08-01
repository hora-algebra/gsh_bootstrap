import GSH.Height.D4ArrowAssembly

set_option autoImplicit false

namespace GSHTest

open GSH

/-- Exact consumer for every phase-one source-zero arrow residue. -/
example (label : D4Alphabet) (hlabel : d4Phase label = 1)
    (residue : Fin 4) :
    HasHeightAtMost
      {word : Word D4Alphabet |
        (word.map d4Phase).sum = 0 ∧
          d4ArrowCountFrom 0 0 label word % 4 = residue.1} 1 :=
  hasHeightAtMost_d4FlipEvenSourceZero label hlabel residue

/-- Exact next parent: the complete arithmetic coordinate fibre. -/
example : HasHeightAtMost d4ArrowCoordinateFiber 1 :=
  hasHeightAtMost_d4ArrowCoordinateFiber

/-- Exact full-alphabet parent. -/
example : HasHeightAtMost (fullIdentityFiber (DihedralGroup 4)) 1 :=
  heightOne_fullIdentityFiber_D4

/-- Exact group-level consumer, retaining every finite recognizing alphabet
and every accepting subset through `HeightOneForGroup`. -/
example : HeightOneForGroup (DihedralGroup 4) := heightOne_D4

end GSHTest
