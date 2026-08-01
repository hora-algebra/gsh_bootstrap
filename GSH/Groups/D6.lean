import GSH.Height.Products
import GSH.Height.S3FlipArrowResidue
import GSH.Groups.Abelian
import GSH.Transfer
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Height one for the dihedral group D6

The exact group theorem is transported along a concrete embedding

`DihedralGroup 6 ↪ S₃ × Multiplicative (ZMod 2)`.

The two factors already have the height-one property, and finite direct
products preserve it.  This avoids duplicating the full-alphabet arrow
analysis used for `S₃`, `D₄`, and `D₅`.
-/

set_option autoImplicit false

namespace GSH

/-- Rotation of the three vertices by the residue `i`. -/
def d6Fin3Rot (i : ZMod 3) : Equiv.Perm (Fin 3) :=
  (ZMod.finEquiv 3).toEquiv.trans
    ((Equiv.addRight (-i)).trans (ZMod.finEquiv 3).symm.toEquiv)

/-- Reflection of the three vertices with affine coordinate `i`. -/
def d6Fin3Ref (i : ZMod 3) : Equiv.Perm (Fin 3) :=
  (ZMod.finEquiv 3).toEquiv.trans
    ((Equiv.neg (ZMod 3)).trans
      ((Equiv.addRight i).trans (ZMod.finEquiv 3).symm.toEquiv))

/-- Reduction of a `ZMod 6` coordinate modulo three. -/
def d6Mod3 (i : ZMod 6) : ZMod 3 :=
  ZMod.castHom (by norm_num : 3 ∣ 6) (ZMod 3) i

/-- Reduction of a `ZMod 6` coordinate modulo two. -/
def d6Mod2 (i : ZMod 6) : ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 6) (ZMod 2) i

/-- The explicit embedding `D₆ ↪ S₃ × C₂`.  The `S₃` coordinate is the
action after reducing modulo three; the `C₂` coordinate remembers the parity
lost in that reduction. -/
def d6ToS3C2 : DihedralGroup 6 →*
    (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) where
  toFun
    | .r i => (d6Fin3Rot (d6Mod3 i), Multiplicative.ofAdd (d6Mod2 i))
    | .sr i => (d6Fin3Ref (d6Mod3 i), Multiplicative.ofAdd (d6Mod2 i))
  map_one' := by decide
  map_mul' := by
    intro x y
    revert x y
    decide

/-- The concrete `D₆ → S₃ × C₂` morphism loses no element. -/
theorem d6ToS3C2_injective : Function.Injective d6ToS3C2 := by
  intro x y
  revert x y
  decide

/-- Every language recognized by `D₆`, over every finite alphabet and for
every accepting subset, has generalized star height at most one. -/
theorem heightOne_D6 : HeightOneForGroup (DihedralGroup 6) := by
  apply HeightOneForGroup.of_injective d6ToS3C2 d6ToS3C2_injective
  exact heightOneForGroup_prod heightOne_S3
    (heightOne_of_commGroup (Multiplicative (ZMod 2)))

end GSH
