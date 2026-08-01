import GSH.Height.S3ArrowResidue

set_option autoImplicit false

namespace GSHTest

open GSH

/-- Compile-time consumer for the return-block factorization used by every
phase-zero `S₃` letter in the self-loop branch of the arrow construction. -/
example (label : S3Alphabet) (hlabel : s3Phase label = 0)
    (pieces : List (Word S3Alphabet))
    (hpieces : ∀ piece ∈ pieces,
      S3ArrowResidue.SelfLoopCodeBlock s3Phase label piece) :
    ArrowCounting.arrowCountFrom (ArrowCounting.c2Step s3Phase)
        0 0 label pieces.flatten = pieces.count [label] :=
  S3ArrowResidue.count_join_codeBlocks s3Phase label pieces hlabel hpieces

end GSHTest
