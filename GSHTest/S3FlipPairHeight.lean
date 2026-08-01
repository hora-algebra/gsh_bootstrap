import GSH.Height.S3FlipPairHeight

set_option autoImplicit false

namespace GSHTest

open GSH
open GSH.S3FlipPairHeight

example (x y : S3Alphabet) (_hx : s3Phase x = 1)
    (_hy : s3Phase y = 1) (_hne : x ≠ y) :
    IsStarFree (pairBlock x y) := by
  exact isStarFree_pairBlock x y

example (x y : S3Alphabet) :
    GRegex.starHeight (pairBlockStarR x y) = 0 := by
  simp

/-- Exact compile-time consumer of the unconditional semantic theorem. -/
example (x y : S3Alphabet) (hx : s3Phase x = 1)
    (hy : s3Phase y = 1) (hne : x ≠ y) :
    IsStarFree (Language.star (pairBlock x y)) := by
  exact isStarFree_pairBlockStar x y hx hy hne

end GSHTest
