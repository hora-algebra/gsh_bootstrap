import GSH.Height.D5FlipPairQuotients

set_option autoImplicit false

namespace GSHTest

open GSH GSH.D5FlipPairQuotients

example (x y : D5PhaseOne) (hne : x.1 ≠ y.1)
    (residue : Fin 5) :
    HasHeightAtMost (d5PairResidue x y residue) 1 :=
  hasHeightAtMost_d5PairResidue x y hne residue

end GSHTest
