import GSH.Height.Counting
import GSH.Transfer
import Mathlib.GroupTheory.OrderOfElement

/-!
# Every finite commutative group has the height-one property

`HeightOneForGroup G` for finite commutative `G`: for every finite alphabet,
every morphism `φ : α* →* G` and every accepting set `P ⊆ G`, the language
`φ⁻¹(P)` has generalized star height at most one.

Obligation `L-ABEL-001`; the mathematical content is the reconstruction asked
for by `M-PST-002` in `PROOF_OBLIGATIONS.md`.  This file is `sorry`-free.

## Argument

Write `f a = φ(a)` and `m = |G|`.  Commutativity turns the value of `φ` on a
word into a product over the alphabet weighted by letter counts,

  `φ(w) = ∏_{a ∈ α} (f a) ^ (count a w)`,

and Lagrange (`pow_card_eq_one`) makes each factor depend only on
`count a w % m`.  So `φ(w)` is a function of the **residue vector**
`res w : α → Fin m`, and every `φ`-fibre is a union of fibres of `res`.  The
alphabet is finite, so there are finitely many residue vectors; each `res`-fibre
is a finite intersection of counting languages, which have height at most one by
`GSH.Counting.hasHeightAtMost_count`, and bounded height is closed under finite
unions and intersections.

Note what is *not* used: no structure theorem for finite abelian groups, and no
choice of generators.  The alphabet, not the group, is what gets decomposed.
-/

set_option autoImplicit false

namespace GSH

universe u v

namespace Abelian

/-! ### Residue vectors and their fibres -/

variable {α : Type u} [DecidableEq α]

/-- The vector of letter counts of `w`, taken modulo `m`. -/
def res (m : Nat) (hm : 0 < m) (w : Word α) : α → Fin m :=
  fun a => ⟨w.count a % m, Nat.mod_lt _ hm⟩

/-- The set of words with a prescribed residue vector, presented as an
intersection of counting languages. -/
def fib (m : Nat) (c : α → Fin m) : Language α :=
  ⋂ a : α, {w : Word α | w.count a % m = (c a : Nat)}

theorem mem_fib {m : Nat} (hm : 0 < m) {c : α → Fin m} {w : Word α} :
    w ∈ fib m c ↔ res m hm w = c := by
  simp only [fib, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · intro h
    funext a
    exact Fin.ext (h a)
  · intro h a
    exact congrArg Fin.val (congrFun h a)

/-- Each residue fibre has generalized star height at most one. -/
theorem hasHeightAtMost_fib [Fintype α] {m : Nat} (c : α → Fin m) :
    HasHeightAtMost (fib m c) 1 :=
  HasHeightAtMost.iInter _ fun a => Counting.hasHeightAtMost_count a (c a).is_lt

/-! ### Evaluating a morphism through letter counts -/

/-- In a commutative monoid the product along a word is the product over the
alphabet of letter values raised to their multiplicities. -/
theorem prod_map_count {M : Type v} [CommMonoid M] [Fintype α]
    (f : α → M) (w : List α) : (w.map f).prod = ∏ a : α, (f a) ^ (w.count a) := by
  induction w with
  | nil => simp
  | cons b w ih =>
      rw [List.map_cons, List.prod_cons, ih]
      have hsplit : ∀ a : α, (f a) ^ ((b :: w).count a)
          = (f a) ^ (w.count a) * (if a = b then f a else 1) := by
        intro a
        rw [List.count_cons]
        by_cases hab : a = b
        · subst hab; simp [pow_succ]
        · have hba : ¬ (b = a) := fun h => hab h.symm
          simp [hab, hba]
      rw [Finset.prod_congr rfl fun a _ => hsplit a, Finset.prod_mul_distrib,
        Finset.prod_ite_eq' Finset.univ b f]
      simp [mul_comm]

end Abelian

/-! ### The theorem -/

/-- **Every finite commutative group has the height-one property.** -/
theorem heightOne_of_commGroup (G : Type v) [CommGroup G] [Fintype G] :
    HeightOneForGroup.{u, v} G := by
  intro α _ _ R
  classical
  obtain ⟨f, hf⟩ : ∃ f : α → G, ∀ a, R.morphism (FreeMonoid.of a) = f a :=
    ⟨fun a => R.morphism (FreeMonoid.of a), fun _ => rfl⟩
  have hm : 0 < Fintype.card G := Fintype.card_pos
  have hfm : ∀ a : α, (f a) ^ (Fintype.card G) = 1 := fun a => pow_card_eq_one
  -- the value of the morphism through letter counts
  have hmor : R.morphism = FreeMonoid.lift f := by
    apply FreeMonoid.hom_eq
    intro a
    simpa using hf a
  have hword : ∀ w : Word α,
      R.morphism (FreeMonoid.ofList w) = ∏ a : α, (f a) ^ (w.count a) := by
    intro w
    rw [hmor, FreeMonoid.lift_ofList, Abelian.prod_map_count]
  -- the value depends only on the residue vector
  have hkey : ∀ w w' : Word α, Abelian.res (Fintype.card G) hm w
        = Abelian.res (Fintype.card G) hm w' →
      R.morphism (FreeMonoid.ofList w) = R.morphism (FreeMonoid.ofList w') := by
    intro w w' h
    rw [hword w, hword w']
    refine Finset.prod_congr rfl fun a _ => ?_
    have hres : w.count a % Fintype.card G = w'.count a % Fintype.card G :=
      congrArg Fin.val (congrFun h a)
    have hpow : ∀ k : Nat, (f a) ^ k = (f a) ^ (k % Fintype.card G) := by
      intro k
      conv_lhs => rw [← Nat.div_add_mod k (Fintype.card G)]
      rw [pow_add, pow_mul, hfm a, one_pow, one_mul]
    rw [hpow (w.count a), hpow (w'.count a), hres]
  -- the language is a finite union of residue fibres
  set S : Finset (α → Fin (Fintype.card G)) :=
    Finset.univ.filter (fun c => ∃ w : Word α, Abelian.res (Fintype.card G) hm w = c ∧
      w ∈ R.language) with hS
  have hdecomp : R.language = ⋃ c ∈ S, Abelian.fib (Fintype.card G) c := by
    ext w
    simp only [Set.mem_iUnion, Abelian.mem_fib hm, hS, Finset.mem_filter, Finset.mem_univ,
      true_and, exists_prop]
    constructor
    · intro hw
      exact ⟨Abelian.res (Fintype.card G) hm w, ⟨w, rfl, hw⟩, rfl⟩
    · rintro ⟨c, ⟨w₀, hw₀c, hw₀⟩, hwc⟩
      have hww₀ : Abelian.res (Fintype.card G) hm w = Abelian.res (Fintype.card G) hm w₀ := by
        rw [hwc, hw₀c]
      show R.morphism (FreeMonoid.ofList w) ∈ R.accepting
      rw [hkey w w₀ hww₀]
      exact hw₀
  rw [hdecomp]
  exact HasHeightAtMost.finset_biUnion S _ fun c => Abelian.hasHeightAtMost_fib c

/-- The same statement with commutativity as a hypothesis rather than an
instance, which is the form the small-order ladder consumes. -/
theorem heightOne_of_mul_comm (G : Type v) [Group G] [Fintype G]
    (hc : ∀ a b : G, a * b = b * a) : HeightOneForGroup.{u, v} G := by
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := hc }
  exact heightOne_of_commGroup.{u, v} G

end GSH
