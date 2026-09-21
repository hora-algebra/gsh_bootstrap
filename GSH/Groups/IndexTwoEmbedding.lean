import GSH.Height.C2Wreath
import Mathlib.GroupTheory.Index

/-!
# An index-two subgroup embeds in its regular wreath product

This is the index-two case of the Krasner--Kaloujnine embedding.  It is
formulated directly, avoiding any splitting assumption: if `H ≤ G` has index
two, a chosen element outside `H` supplies a set-theoretic transversal and an
injective homomorphism

`G →* H ≀ᵣ Multiplicative (ZMod 2)`.
-/

set_option autoImplicit false

namespace GSH
namespace IndexTwoEmbedding

universe v

abbrev C2 := Multiplicative (ZMod 2)

variable {G : Type v} [Group G] (H : Subgroup G)

noncomputable section

/-- The additive membership phase: zero on `H`, one outside `H`. -/
def phaseAdd (H : Subgroup G) (g : G) : ZMod 2 := by
  classical
  exact if g ∈ H then 0 else 1

@[simp] theorem phaseAdd_eq_zero_iff (g : G) :
    phaseAdd H g = 0 ↔ g ∈ H := by
  by_cases hg : g ∈ H <;> simp [phaseAdd, hg]

@[simp] theorem phaseAdd_eq_one_iff (g : G) :
    phaseAdd H g = 1 ↔ g ∉ H := by
  by_cases hg : g ∈ H <;> simp [phaseAdd, hg]

/-- Membership phase as a group homomorphism, using the index-two
multiplication criterion. -/
def phaseHom (hindex : H.index = 2) : G →* C2 where
  toFun g := Multiplicative.ofAdd (phaseAdd H g)
  map_one' := by simp [phaseAdd]
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    have hmem := H.mul_mem_iff_of_index_two hindex (a := a) (b := b)
    by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;>
      simp [phaseAdd, ha, hb, hmem] <;> decide

/-- A two-element transversal: identity over phase zero and `t` over phase
one. -/
def representative (t : G) (q : C2) : G :=
  if q.toAdd = 0 then 1 else t

@[simp] theorem representative_one (t : G) :
    representative t (1 : C2) = 1 := by simp [representative]

theorem phaseHom_representative (hindex : H.index = 2)
    (t : G) (ht : t ∉ H) (q : C2) :
    phaseHom H hindex (representative t q) = q := by
  apply Multiplicative.toAdd.injective
  rcases show q.toAdd = 0 ∨ q.toAdd = 1 by
      revert q
      decide with hq | hq
  · simp [representative, hq, phaseHom, phaseAdd]
  · simp [representative, hq, phaseHom, phaseAdd, ht]

/-- The base coordinate in the index-two embedding. -/
def baseCoordinate (hindex : H.index = 2) (t : G) (ht : t ∉ H)
    (g : G) (q : C2) : H :=
  ⟨representative t q * g *
      (representative t ((phaseHom H hindex g)⁻¹ * q))⁻¹,
    by
      rw [← phaseAdd_eq_zero_iff H]
      apply Multiplicative.ofAdd.injective
      change phaseHom H hindex
          (representative t q * g *
            (representative t ((phaseHom H hindex g)⁻¹ * q))⁻¹) = 1
      simp [phaseHom_representative H hindex t ht]
      have hp : phaseHom H hindex g * phaseHom H hindex g = 1 := by
        apply Multiplicative.toAdd.injective
        change phaseAdd H g + phaseAdd H g = 0
        exact CharTwo.add_self_eq_zero _
      calc
        q * phaseHom H hindex g *
            (q⁻¹ * phaseHom H hindex g) =
            (q * q⁻¹) *
              (phaseHom H hindex g * phaseHom H hindex g) := by ac_rfl
        _ = phaseHom H hindex g * phaseHom H hindex g := by simp
        _ = 1 := hp⟩

/-- The index-two Krasner--Kaloujnine homomorphism. -/
def embedding (hindex : H.index = 2) (t : G) (ht : t ∉ H) :
    G →* (H ≀ᵣ C2) where
  toFun g := ⟨baseCoordinate H hindex t ht g, phaseHom H hindex g⟩
  map_one' := by
    apply RegularWreathProduct.ext
    · funext q
      apply Subtype.ext
      simp [baseCoordinate]
    · simp
  map_mul' a b := by
    apply RegularWreathProduct.ext
    · funext q
      apply Subtype.ext
      simp only [RegularWreathProduct.mul_left, Pi.mul_apply,
        baseCoordinate, Subgroup.coe_mul, Subgroup.coe_mk]
      simp only [map_mul]
      group
    · exact map_mul (phaseHom H hindex) a b

/-- The index-two embedding is injective. -/
theorem embedding_injective (hindex : H.index = 2) (t : G) (ht : t ∉ H) :
    Function.Injective (embedding H hindex t ht) := by
  intro a b hab
  have hphase : phaseHom H hindex a = phaseHom H hindex b :=
    congrArg RegularWreathProduct.right hab
  have hbase :
      representative t 1 * a *
          (representative t ((phaseHom H hindex a)⁻¹ * 1))⁻¹ =
        representative t 1 * b *
          (representative t ((phaseHom H hindex b)⁻¹ * 1))⁻¹ := by
    have hleft := congrArg (fun w : H ≀ᵣ C2 => w.left 1) hab
    exact congrArg Subtype.val hleft
  rw [hphase] at hbase
  calc
    a = (representative t 1)⁻¹ *
        (representative t 1 * a *
          (representative t ((phaseHom H hindex b)⁻¹ * 1))⁻¹) *
        representative t ((phaseHom H hindex b)⁻¹ * 1) := by group
    _ = (representative t 1)⁻¹ *
        (representative t 1 * b *
          (representative t ((phaseHom H hindex b)⁻¹ * 1))⁻¹) *
        representative t ((phaseHom H hindex b)⁻¹ * 1) := by rw [hbase]
    _ = b := by group

/-- Every index-two subgroup admits the embedding, with the transversal chosen
from the index hypothesis. -/
theorem exists_embedding (hindex : H.index = 2) :
    ∃ φ : G →* (H ≀ᵣ C2), Function.Injective φ := by
  obtain ⟨t, ht, _⟩ := H.index_eq_two_iff_exists_notMem_and.mp hindex
  exact ⟨embedding H hindex t ht, embedding_injective H hindex t ht⟩

/-- A finite group with a commutative subgroup of index two has the
height-one property. -/
theorem heightOne_of_commutative_index_two [Fintype G]
    (hindex : H.index = 2) (hcomm : ∀ a b : H, a * b = b * a) :
    HeightOneForGroup G := by
  letI : CommGroup H :=
    { (inferInstance : Group H) with mul_comm := hcomm }
  letI : Fintype H := Fintype.ofFinite H
  obtain ⟨φ, hφ⟩ := exists_embedding H hindex
  exact HeightOneForGroup.of_injective φ hφ C2Wreath.heightOneForGroup

end
end IndexTwoEmbedding
end GSH
