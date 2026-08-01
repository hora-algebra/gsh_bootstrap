import GSH.Groups.Dic3

set_option autoImplicit false

namespace GSHTest

open GSH

example : Function.Injective dic3ToS3C4 := dic3ToS3C4_injective

/-- Exact group-level target with all recognition quantifiers intact. -/
example : HeightOneForGroup (QuaternionGroup 3) := heightOne_Dic3

end GSHTest
