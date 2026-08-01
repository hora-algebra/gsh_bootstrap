import GSH.Height.S3SelfLoopHeight

set_option autoImplicit false

namespace GSHTest

open GSH

/-- Exact acceptance for a singleton `S₃` letter language. -/
example (label : S3Alphabet) :
    IsStarFree (Language.letter label) :=
  isStarFree_s3Letter label

/-- Exact acceptance for the generalized-star-free singleton star. -/
example (label : S3Alphabet) :
    IsStarFree (Language.star (Language.letter label)) :=
  isStarFree_s3LetterStar label

/-- Exact acceptance for the PST self-loop return-block language. -/
example (label : S3Alphabet) :
    IsStarFree
      {word | S3ArrowResidue.SelfLoopReturnBlock s3Phase label word} :=
  isStarFree_s3SelfLoopReturnBlock label

end GSHTest
