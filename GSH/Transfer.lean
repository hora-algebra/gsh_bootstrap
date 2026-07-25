import GSH.Recognition
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Transfer of the height-one property along morphisms

`HeightOneForMonoid M` quantifies over *all* alphabets, *all* morphisms
`α* →* M` and *all* accepting subsets, so it transfers along morphisms of the
recognizing monoid with no work on the language side at all:

* along an **injective** morphism `M →* N` the property descends from `N` to
  `M` (push the accepting set forward);
* along a **surjective** morphism `K →* G` it descends from `K` to `G` (lift
  each letter to a preimage, then pull the accepting set back).

Together these say that `HeightOneForGroup` is inherited by **divisors**: a
quotient of a subgroup of a group with the property has the property.  This is
the mechanism by which the finite-group ladder will climb once a base class is
established, and it is what makes an embedding such as `Dic_3 ↪ (C_3×C_4)⋊C_2`
a proof rather than an analogy.

Obligation `L-TRANS-001` in `PROOF_OBLIGATIONS.md`.  This file is `sorry`-free.
-/

set_option autoImplicit false

namespace GSH

universe u v w

/-- Recognition transfers along an injective morphism: if every language
recognized by `N` has height at most one, so does every language recognized by
a submonoid-like image `M ↪ N`. -/
theorem HeightOneForMonoid.of_injective {M : Type v} {N : Type w} [Monoid M] [Monoid N]
    (φ : M →* N) (hφ : Function.Injective φ) (h : HeightOneForMonoid.{u, w} N) :
    HeightOneForMonoid.{u, v} M := by
  intro α _ _ R
  have hlang : R.language = (Recognition.mk (φ.comp R.morphism) (φ '' R.accepting)).language := by
    ext w
    simp only [Recognition.mem_language_iff, MonoidHom.coe_comp, Function.comp_apply]
    constructor
    · intro hw
      exact ⟨_, hw, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      exact hφ hxy ▸ hy
  rw [hlang]
  exact h α _

/-- Recognition transfers along a surjective morphism: choose a preimage for
each letter, so that a morphism into the quotient factors through one into the
source. -/
theorem HeightOneForMonoid.of_surjective {K : Type v} {M : Type w} [Monoid K] [Monoid M]
    (φ : K →* M) (hφ : Function.Surjective φ) (h : HeightOneForMonoid.{u, v} K) :
    HeightOneForMonoid.{u, w} M := by
  intro α _ _ R
  classical
  choose g hg using fun a : α => hφ (R.morphism (FreeMonoid.of a))
  have hcomp : φ.comp (FreeMonoid.lift g) = R.morphism := by
    apply FreeMonoid.hom_eq
    intro a
    simpa using hg a
  have hlang :
      R.language = (Recognition.mk (FreeMonoid.lift g) (φ ⁻¹' R.accepting)).language := by
    ext w
    simp only [Recognition.mem_language_iff, Set.mem_preimage]
    rw [← hcomp]
    rfl
  rw [hlang]
  exact h α _

/-! ### Group-level corollaries -/

/-- A group embedding transports the height-one property downwards. -/
theorem HeightOneForGroup.of_injective {G : Type v} {H : Type w} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Injective φ) (h : HeightOneForGroup.{u, w} H) :
    HeightOneForGroup.{u, v} G :=
  HeightOneForMonoid.of_injective φ hφ h

/-- A group quotient inherits the height-one property. -/
theorem HeightOneForGroup.of_surjective {K : Type v} {G : Type w} [Group K] [Group G]
    (φ : K →* G) (hφ : Function.Surjective φ) (h : HeightOneForGroup.{u, v} K) :
    HeightOneForGroup.{u, w} G :=
  HeightOneForMonoid.of_surjective φ hφ h

/-- Isomorphic groups have the property simultaneously. -/
theorem HeightOneForGroup.of_mulEquiv {G : Type v} {H : Type w} [Group G] [Group H]
    (e : G ≃* H) (h : HeightOneForGroup.{u, w} H) : HeightOneForGroup.{u, v} G :=
  HeightOneForGroup.of_injective e.toMonoidHom e.injective h

/-- Subgroups inherit the property from the ambient group. -/
theorem HeightOneForGroup.subgroup {G : Type v} [Group G] (H : Subgroup G)
    (h : HeightOneForGroup.{u, v} G) : HeightOneForGroup.{u, v} H :=
  HeightOneForGroup.of_injective H.subtype (Subgroup.subtype_injective H) h

end GSH
