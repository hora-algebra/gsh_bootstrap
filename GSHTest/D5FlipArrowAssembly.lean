import GSH.Height.D5FlipArrowAssembly

set_option autoImplicit false

namespace GSHTest

open GSH

example (label : D5Alphabet) (hlabel : d5Phase label = 1)
    (residue : Fin 5) :
    HasHeightAtMost
      {word : Word D5Alphabet |
        (word.map d5Phase).sum = 0 ∧
          d5ArrowCountFrom 0 0 label word % 5 = residue.1} 1 :=
  hasHeightAtMost_d5FlipEvenSourceZero label hlabel residue

end GSHTest
