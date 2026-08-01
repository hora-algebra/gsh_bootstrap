import GSH.Height.Closure
import GSH.Recognition
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fintype.Prod

/-!
# Height-one groups are closed under finite direct products

An arbitrary accepting subset of `G × H` is a finite union of singleton
product fibres.  Each singleton product fibre is the intersection of one
language recognized by `G` and one recognized by `H`.
-/

set_option autoImplicit false

namespace GSH

universe u v w

/-- The exact recognition property is closed under finite direct products.
The conclusion retains every finite alphabet, recognizing morphism, and
accepting subset quantified by `HeightOneForGroup`. -/
theorem heightOneForGroup_prod {G : Type v} {H : Type w}
    [Group G] [Fintype G] [Group H] [Fintype H]
    (hG : HeightOneForGroup.{u, v} G)
    (hH : HeightOneForGroup.{u, w} H) :
    HeightOneForGroup.{u, max v w} (G × H) := by
  intro α _ _ R
  classical
  let leftFiber (g : G) : Recognition α G :=
    { morphism := (MonoidHom.fst G H).comp R.morphism
      accepting := {g} }
  let rightFiber (h : H) : Recognition α H :=
    { morphism := (MonoidHom.snd G H).comp R.morphism
      accepting := {h} }
  let accepted : Finset (G × H) :=
    Finset.univ.filter fun p => p ∈ R.accepting
  have hdecomp :
      R.language =
        ⋃ p ∈ accepted,
          (leftFiber p.1).language ∩ (rightFiber p.2).language := by
    ext word
    simp [accepted, leftFiber, rightFiber,
      Recognition.mem_language_iff]
  rw [hdecomp]
  exact HasHeightAtMost.finset_biUnion accepted _ fun p =>
    (hG α (leftFiber p.1)).inter (hH α (rightFiber p.2))

end GSH
