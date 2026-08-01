import GSH.Height.S3FullFiber

set_option autoImplicit false

namespace GSHTest

open GSH

/-! The finite coordinate tables are available universally. -/

example (p q : S3Alphabet) :
    s3Phase (p * q) = s3Phase p + s3Phase q :=
  s3Phase_mul p q

example (p q : S3Alphabet) :
    s3Beta (p * q) = s3Beta p + s3Slope p * s3Beta q :=
  s3Beta_mul p q

example (p : S3Alphabet) :
    p = 1 ↔ s3Phase p = 0 ∧ s3Beta p = 0 :=
  s3_eq_one_iff_phase_beta p

/-! The word-level reconstruction has no bound on word length. -/

example (word : Word S3Alphabet) :
    word.prod = 1 ↔
      (word.map s3Phase).sum = 0 ∧ s3BetaByArrows word = 0 :=
  s3_prod_eq_one_iff_arrowCounts word

example :
    fullIdentityFiber S3Alphabet = s3ArrowCoordinateFiber :=
  fullIdentityFiber_s3_eq_arrowCoordinateFiber

end GSHTest
