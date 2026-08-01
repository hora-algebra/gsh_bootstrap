import GSH.Height.S3SelfLoopTransfer

set_option autoImplicit false

namespace GSHTest

open GSH

/-- Exact language equality completing the self-loop Transfer edge. -/
example (label : S3Alphabet) (hlabel : s3Phase label = 0) :
    S3SelfLoopQuotients.evenResidue label 0 =
      TransferCore.formula (Language.letter label)
        {word | S3ArrowResidue.SelfLoopReturnBlock s3Phase label word} 3 :=
  s3SelfLoopEven_zero_eq_formula label hlabel

/-- The first unconditional height theorem in the self-loop branch. -/
example (label : S3Alphabet) (hlabel : s3Phase label = 0) :
    HasHeightAtMost (S3SelfLoopQuotients.evenResidue label 0) 1 :=
  hasHeightAtMost_s3SelfLoopEven_zero label hlabel

/-- All even-final self-loop residues and both source states. -/
example (label : S3Alphabet) (hlabel : s3Phase label = 0)
    (source : ZMod 2) (residue : Fin 3) :
    HasHeightAtMost
      {word : Word S3Alphabet |
        (word.map s3Phase).sum = 0 ∧
          s3ArrowCountFrom 0 source label word % 3 = residue.1} 1 :=
  hasHeightAtMost_s3SelfLoopEven label hlabel source residue

/-- Complete self-loop branch, with no final-phase restriction. -/
example (label : S3Alphabet) (hlabel : s3Phase label = 0)
    (source : ZMod 2) (residue : Fin 3) :
    HasHeightAtMost
      {word : Word S3Alphabet |
        s3ArrowCountFrom 0 source label word % 3 = residue.1} 1 :=
  hasHeightAtMost_s3SelfLoopArrowResidue
    label hlabel source residue

end GSHTest
