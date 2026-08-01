import GSH.Height.S3SelfLoopQuotients

set_option autoImplicit false

namespace GSHTest

open GSH

/-- The residue-two even self-loop language is the first left quotient of
the zero-residue language. -/
example (label : S3Alphabet) (hlabel : s3Phase label = 0) :
    Language.leftQuotient label
        (S3SelfLoopQuotients.evenResidue label 0) =
      S3SelfLoopQuotients.evenResidue label 2 :=
  S3SelfLoopQuotients.leftQuotient_zero_eq_two label hlabel

/-- The residue-one even self-loop language is the second left quotient of
the zero-residue language. -/
example (label : S3Alphabet) (hlabel : s3Phase label = 0) :
    Language.leftQuotient label
        (Language.leftQuotient label
          (S3SelfLoopQuotients.evenResidue label 0)) =
      S3SelfLoopQuotients.evenResidue label 1 :=
  S3SelfLoopQuotients.leftQuotient_twice_zero_eq_one label hlabel

/-- Exact conditional parent: only the zero-residue height theorem remains
after the quotient reduction. -/
example (label : S3Alphabet) (hlabel : s3Phase label = 0)
    (hzero : HasHeightAtMost
      (S3SelfLoopQuotients.evenResidue label 0) 1)
    (residue : Fin 3) :
    HasHeightAtMost
      (S3SelfLoopQuotients.evenResidue label residue.1) 1 :=
  S3SelfLoopQuotients.hasHeightAtMost_evenResidue_of_zero
    label hlabel hzero residue

end GSHTest
