import GSH.Groups.D6
import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Height one for the dicyclic group `Dic₃`

We embed `QuaternionGroup 3` explicitly into `S₃ × C₄`.  The first
coordinate forgets the central shift in the quaternion multiplication after
reduction modulo three; the second coordinate records exactly the parity and
constructor information lost there.
-/

set_option autoImplicit false

namespace GSH

/-- The even `C₄` coordinate attached to `a i`. -/
def dic3EvenC4 (i : ZMod 6) : ZMod 4 :=
  (2 : ZMod 4) * (i.val : ZMod 4)

/-- Explicit embedding `Dic₃ ↪ S₃ × C₄`.

The coordinates are
`a i ↦ (rotation (i mod 3), 2i)` and
`xa i ↦ (reflection (i mod 3), 1 + 2i)`. -/
def dic3ToS3C4 : QuaternionGroup 3 →*
    (Equiv.Perm (Fin 3) × Multiplicative (ZMod 4)) where
  toFun
    | .a i =>
        (d6Fin3Rot (d6Mod3 i), Multiplicative.ofAdd (dic3EvenC4 i))
    | .xa i =>
        (d6Fin3Ref (d6Mod3 i),
          Multiplicative.ofAdd (1 + dic3EvenC4 i))
  map_one' := by decide
  map_mul' := by
    intro x y
    revert x y
    decide

/-- The concrete `Dic₃ → S₃ × C₄` morphism loses no element. -/
theorem dic3ToS3C4_injective : Function.Injective dic3ToS3C4 := by
  intro x y
  revert x y
  decide

/-- Every language recognized by `Dic₃`, over every finite alphabet and every
accepting subset, has generalized star height at most one. -/
theorem heightOne_Dic3 : HeightOneForGroup (QuaternionGroup 3) := by
  apply HeightOneForGroup.of_injective dic3ToS3C4 dic3ToS3C4_injective
  exact heightOneForGroup_prod heightOne_S3
    (heightOne_of_commGroup (Multiplicative (ZMod 4)))

end GSH
