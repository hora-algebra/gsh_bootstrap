import GSH.Height.S3ArrowResidue
import GSH.Height.TransferCore

/-!
# Acceptance tests for the PST transfer core
-/

set_option autoImplicit false

open GSH

example {alpha : Type} (L0 L1 : Language alpha) (modulus : Nat)
    (hL0 : IsStarFree L0) (hL1 : IsStarFree L1)
    (hL0Star : IsStarFree (Language.star L0)) :
    HasHeightAtMost (TransferCore.formula L0 L1 modulus) 1 :=
  TransferCore.hasHeightAtMost_formula L0 L1 modulus hL0 hL1 hL0Star

/-- BLUEPRINT: exact next-parent shape for the phase-zero, zero-source,
residue-zero self-loop edge.  This is intentionally not called a completed
consumer: the displayed language equality is the remaining prefix-code
factorization theorem, and is not hidden by this test. -/
example (label : S3Alphabet)
    (hLabel : IsStarFree (Language.letter label))
    (hReturn : IsStarFree
      {word | S3ArrowResidue.SelfLoopReturnBlock s3Phase label word})
    (hLabelStar : IsStarFree (Language.star (Language.letter label)))
    (hFactorization :
      {word : Word S3Alphabet |
          (word.map s3Phase).sum = 0 ∧
            s3ArrowCountFrom 0 0 label word % 3 = 0} =
        TransferCore.formula (Language.letter label)
          {word | S3ArrowResidue.SelfLoopReturnBlock s3Phase label word} 3) :
    HasHeightAtMost
      {word : Word S3Alphabet |
        (word.map s3Phase).sum = 0 ∧
          s3ArrowCountFrom 0 0 label word % 3 = 0} 1 := by
  exact (TransferCore.hasHeightAtMost_formula
    (Language.letter label)
      {word | S3ArrowResidue.SelfLoopReturnBlock s3Phase label word}
      3 hLabel hReturn hLabelStar).congr hFactorization.symm
