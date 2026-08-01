import GSH.Groups.D6

set_option autoImplicit false

namespace GSHTest

open GSH

example : Function.Injective d6ToS3C2 := d6ToS3C2_injective

/-- Exact group-level consumer, preserving every finite alphabet,
recognizing morphism, and accepting subset. -/
example : HeightOneForGroup (DihedralGroup 6) := heightOne_D6

end GSHTest
