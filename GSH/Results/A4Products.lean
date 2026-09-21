import GSH.Groups.Abelian
import GSH.Height.Products
import GSH.Results.A4FullAlphabet
import Mathlib.Data.ZMod.Basic

/-!
# Product consequences of the `A₄` theorem

Kazumi Kasaura's theorem `A4FullAlphabet.heightOneForGroup_A4` combines with
finite-product closure and the existing commutative-group theorem to give an
infinite family of non-`A₄` examples.  The first concrete frontier consequence
is `C₂ × A₄`.
-/

set_option autoImplicit false

namespace GSH

universe u v

/-- Every direct product of a finite commutative group with `A₄` has the full
height-one recognition property. -/
theorem heightOneForGroup_comm_prod_A4 (C : Type v)
    [CommGroup C] [Fintype C] : HeightOneForGroup.{u, v} (C × A4) :=
  heightOneForGroup_prod (heightOne_of_commGroup C)
    A4FullAlphabet.heightOneForGroup_A4

/-- In particular, every language recognized by `C₂ × A₄` has generalized
star height at most one. -/
theorem heightOne_C2_prod_A4 :
    HeightOneForGroup (Multiplicative (ZMod 2) × A4) :=
  heightOneForGroup_comm_prod_A4 (Multiplicative (ZMod 2))

end GSH
