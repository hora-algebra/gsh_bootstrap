import GSH.Groups.S3

set_option autoImplicit false

namespace GSHTest

open GSH

universe u

noncomputable section

/-! The concrete split-extension presentation of `S₃` is available. -/

example :
    (alternatingGroup (Fin 3)) ⋊[s3ConjugationAction]
      s3Reflection ≃* Equiv.Perm (Fin 3) :=
  s3SemidirectEquiv

/-! The remaining semidirect-product theorem would imply the exact `S₃`
target, with all quantifiers of `HeightOneForGroup` unchanged. -/

example
    (h : HeightOneForGroup.{u}
      ((alternatingGroup (Fin 3)) ⋊[s3ConjugationAction] s3Reflection)) :
    HeightOneForGroup.{u} (Equiv.Perm (Fin 3)) :=
  heightOne_S3_of_semidirect h

end

end GSHTest
