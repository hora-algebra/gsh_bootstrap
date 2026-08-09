import GSH.Groups.OrderTwelveClassification

/-!
# Acceptance test for the ladder through order twelve

The headline theorem must retain the exact `HeightOneForGroup` quantifiers:
every finite alphabet, every morphism from its free monoid, and every accepting
subset.  In particular, this is not a list of fixed-alphabet word problems.
-/

set_option autoImplicit false

namespace GSHTest

open GSH

universe u v

example : HeightOneUpTo.{u, v} 12 :=
  heightOneUpTo_twelve

example (G : Type v) [Group G] [Fintype G]
    (hcard : Fintype.card G ≤ 12) : HeightOneForGroup.{u, v} G :=
  heightOneUpTo_twelve G hcard

end GSHTest
