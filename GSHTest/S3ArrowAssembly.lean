import GSH.Height.S3ArrowAssembly

set_option autoImplicit false

namespace GSHTest

open GSH

/-- The two source-state arrow counts partition the ordinary occurrence
count, universally over the initial state, label, and word. -/
example (start : ZMod 2) (label : S3Alphabet) (word : Word S3Alphabet) :
    s3ArrowCountFrom start 0 label word +
        s3ArrowCountFrom start 1 label word =
      word.count label :=
  s3ArrowCount_partition start label word

example (shift start source : ZMod 2) (label : S3Alphabet)
    (word : Word S3Alphabet) :
    s3ArrowCountFrom (start + shift) (source + shift) label word =
      s3ArrowCountFrom start source label word :=
  s3ArrowCount_shift shift start source label word

/-- Exact conditional parent for source one: only the even source-zero
zero-residue theorem remains. -/
example (label : S3Alphabet) (hlabel : s3Phase label = 0)
    (hzero : HasHeightAtMost
      (S3SelfLoopQuotients.evenResidue label 0) 1)
    (residue : Fin 3) :
    HasHeightAtMost
      (s3SelfLoopEvenSourceOneResidue label residue.1) 1 :=
  hasHeightAtMost_s3SelfLoopEvenSourceOne_of_zero
    label hlabel hzero residue

end GSHTest
