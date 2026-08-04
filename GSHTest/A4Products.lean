import GSH.Results.A4Products

/-!
# Acceptance tests for finite products and the `C₂ × A₄` consequence

These examples pin the exact `HeightOneForGroup` quantifiers.  They do not
replace the groups by a fixed alphabet or by a single word problem.
-/

set_option autoImplicit false

namespace GSHTest

open GSH

universe u v w

example {G : Type v} {H : Type w}
    [Group G] [Fintype G] [Group H] [Fintype H]
    (hG : HeightOneForGroup.{u, v} G)
    (hH : HeightOneForGroup.{u, w} H) :
    HeightOneForGroup.{u, max v w} (G × H) :=
  heightOneForGroup_prod hG hH

example (C : Type v) [CommGroup C] [Fintype C] :
    HeightOneForGroup.{u, v} (C × A4) :=
  heightOneForGroup_comm_prod_A4 C

example : HeightOneForGroup (Multiplicative (ZMod 2) × A4) :=
  heightOne_C2_prod_A4

end GSHTest
