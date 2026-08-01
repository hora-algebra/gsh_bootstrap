import GSH.Height.Products

set_option autoImplicit false

namespace GSHTest

open GSH

universe u v w

/-- Exact finite-direct-product consumer. -/
example {G : Type v} {H : Type w}
    [Group G] [Fintype G] [Group H] [Fintype H]
    (hG : HeightOneForGroup.{u, v} G)
    (hH : HeightOneForGroup.{u, w} H) :
    HeightOneForGroup.{u, max v w} (G × H) :=
  heightOneForGroup_prod hG hH

end GSHTest
