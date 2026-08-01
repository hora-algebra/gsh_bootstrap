import GSH.Height.D5SelfLoopTransfer

set_option autoImplicit false

namespace GSHTest

open GSH
open GSH.D5SelfLoopTransfer

example (label : D5Alphabet) (hlabel : d5Phase label = 0) :
    d5SelfLoopEvenResidue label 0 =
      TransferCore.formula (Language.letter label)
        {word | S3ArrowResidue.SelfLoopReturnBlock d5Phase label word} 5 :=
  d5SelfLoopEven_zero_eq_formula label hlabel

/-- Exact source-zero consumer for all five self-loop residues. -/
example (label : D5Alphabet) (hlabel : d5Phase label = 0)
    (residue : Fin 5) :
    HasHeightAtMost (d5SelfLoopEvenResidue label residue) 1 :=
  hasHeightAtMost_d5SelfLoopEvenSourceZero label hlabel residue

end GSHTest
