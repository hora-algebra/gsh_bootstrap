import GSH.Height.D4SelfLoopTransfer

set_option autoImplicit false

namespace GSHTest

open GSH
open GSH.D4SelfLoopTransfer

example (label : D4Alphabet) (hlabel : d4Phase label = 0) :
    d4SelfLoopEvenResidue label 0 =
      TransferCore.formula (Language.letter label)
        {word | S3ArrowResidue.SelfLoopReturnBlock d4Phase label word} 4 :=
  d4SelfLoopEven_zero_eq_formula label hlabel

/-- Exact source-zero consumer for all four self-loop residues. -/
example (label : D4Alphabet) (hlabel : d4Phase label = 0)
    (residue : Fin 4) :
    HasHeightAtMost (d4SelfLoopEvenResidue label residue) 1 :=
  hasHeightAtMost_d4SelfLoopEvenSourceZero label hlabel residue

end GSHTest
