import GSH.Height.S3PhaseAssembly

set_option autoImplicit false

namespace GSHTest

open GSH

/-- The finite count-residue assembly has exactly the phase-zero semantics. -/
example : s3PhaseZeroAssembly = s3PhaseZeroLanguage :=
  s3PhaseZeroAssembly_eq

/-- The phase-zero condition needed by the full `S₃` fibre has height one. -/
example : HasHeightAtMost s3PhaseZeroLanguage 1 :=
  hasHeightAtMost_s3PhaseZeroLanguage

end GSHTest
