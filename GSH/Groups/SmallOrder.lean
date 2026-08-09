import GSH.Groups.Abelian
import GSH.Groups.IndexTwoEmbedding
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.PGroup

/-!
# The finite-group ladder indexed by order

`HeightOneUpTo n` is the statement "every language recognized by a group of
order at most `n` has generalized star height at most one".

This file proves the ladder through order eleven.  Orders six, eight, and ten
have a commutative subgroup of index two; the specialized
Krasner--Kaloujnine embedding in `GSH.Groups.IndexTwoEmbedding` handles split
and non-split extensions uniformly.  The remaining orders are commutative.

Order twelve is kept in `GSH.Groups.OrderTwelveClassification`: its Sylow-three
fork gives either `A₄` or a commutative subgroup of index two.  The `A₄` branch
uses Kazumi Kasaura's theorem `GSH.A4FullAlphabet.heightOneForGroup_A4`
without modifying its proof.
-/

set_option autoImplicit false

namespace GSH

universe u v

/-- Every group of order at most five is commutative. -/
theorem mul_comm_of_card_le_five (G : Type v) [Group G] [Fintype G]
    (h : Fintype.card G ≤ 5) : ∀ a b : G, a * b = b * a := by
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  have hcard : Nat.card G = Fintype.card G := Nat.card_eq_fintype_card
  have key : Fintype.card G = 1 ∨ Fintype.card G = 2 ∨ Fintype.card G = 3
      ∨ Fintype.card G = 4 ∨ Fintype.card G = 5 := by omega
  rcases key with hc | hc | hc | hc | hc
  · haveI : Subsingleton G := Fintype.card_le_one_iff_subsingleton.1 hc.le
    exact fun a b => Subsingleton.elim _ _
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := isCyclic_of_prime_card (α := G) (p := 2) (by rw [hcard, hc])
    exact (inferInstance : IsMulCommutative G).is_comm.comm
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI := isCyclic_of_prime_card (α := G) (p := 3) (by rw [hcard, hc])
    exact (inferInstance : IsMulCommutative G).is_comm.comm
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := G) (p := 2)
      (by rw [hcard, hc]; norm_num)).is_comm.comm
  · haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    haveI := isCyclic_of_prime_card (α := G) (p := 5) (by rw [hcard, hc])
    exact (inferInstance : IsMulCommutative G).is_comm.comm

/-- Every language recognized by a group of order at most `n` has generalized
star height at most one. -/
def HeightOneUpTo (n : Nat) : Prop :=
  ∀ (G : Type v) [Group G] [Fintype G], Fintype.card G ≤ n → HeightOneForGroup.{u, v} G

/-- **The ladder holds up to order five.**  Obligation `L-ORD5-001`. -/
theorem heightOneUpTo_five : HeightOneUpTo.{u, v} 5 := by
  intro G _ _ h
  exact heightOne_of_mul_comm.{u, v} G (mul_comm_of_card_le_five G h)

/-! ### The noncommutative orders below twelve -/

private theorem heightOne_of_card_six (G : Type v) [Group G] [Fintype G]
    (hcard : Fintype.card G = 6) : HeightOneForGroup.{u, v} G := by
  have hnat : Nat.card G = 6 := by simpa [Nat.card_eq_fintype_card] using hcard
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 3 G := default
  have hPcard : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, hnat]
    rw [show 6 = 3 * 2 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)]
    rw [Nat.prime_three.factorization, Nat.prime_two.factorization]
    norm_num
  have hindex : P.1.index = 2 := by
    have hmul := P.1.card_mul_index
    rw [hPcard, hnat] at hmul
    omega
  have hcomm : ∀ a b : P.1, a * b = b * a := by
    letI := isCyclic_of_prime_card (α := P.1) (p := 3) hPcard
    exact (inferInstance : IsMulCommutative P.1).is_comm.comm
  exact IndexTwoEmbedding.heightOne_of_commutative_index_two P.1 hindex hcomm

private theorem heightOne_of_card_eight (G : Type v) [Group G] [Fintype G]
    (hcard : Fintype.card G = 8) : HeightOneForGroup.{u, v} G := by
  have hnat : Nat.card G = 8 := by simpa [Nat.card_eq_fintype_card] using hcard
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpGroup : IsPGroup 2 G := IsPGroup.iff_card.mpr ⟨3, by norm_num [hcard]⟩
  obtain ⟨H, hHcard⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two hpGroup
      (n := 2) (by norm_num [hcard])
  have hindex : H.index = 2 := by
    have hmul := H.card_mul_index
    rw [hHcard, hnat] at hmul
    norm_num at hmul ⊢
    omega
  have hcomm : ∀ a b : H, a * b = b * a :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := H) (p := 2)
      hHcard).is_comm.comm
  exact IndexTwoEmbedding.heightOne_of_commutative_index_two H hindex hcomm

private theorem heightOne_of_card_ten (G : Type v) [Group G] [Fintype G]
    (hcard : Fintype.card G = 10) : HeightOneForGroup.{u, v} G := by
  have hnat : Nat.card G = 10 := by simpa [Nat.card_eq_fintype_card] using hcard
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 G := default
  have hPcard : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, hnat]
    rw [show 10 = 5 * 2 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)]
    have hp5 : Nat.Prime 5 := (inferInstance : Fact (Nat.Prime 5)).out
    rw [hp5.factorization, Nat.prime_two.factorization]
    norm_num
  have hindex : P.1.index = 2 := by
    have hmul := P.1.card_mul_index
    rw [hPcard, hnat] at hmul
    omega
  have hcomm : ∀ a b : P.1, a * b = b * a := by
    letI := isCyclic_of_prime_card (α := P.1) (p := 5) hPcard
    exact (inferInstance : IsMulCommutative P.1).is_comm.comm
  exact IndexTwoEmbedding.heightOne_of_commutative_index_two P.1 hindex hcomm

/-- **The ladder holds up to order eleven.**  The only noncommutative cases
are handled uniformly through a commutative subgroup of index two. -/
theorem heightOneUpTo_eleven : HeightOneUpTo.{u, v} 11 := by
  intro G _ _ hle
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  interval_cases h : Fintype.card G
  all_goals try { exact heightOne_of_mul_comm G (mul_comm_of_card_le_five G (by omega)) }
  · exact heightOne_of_card_six G h
  · haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
    haveI := isCyclic_of_prime_card (α := G) (p := 7)
      (by simpa [Nat.card_eq_fintype_card] using h)
    exact heightOne_of_mul_comm G (inferInstance : IsMulCommutative G).is_comm.comm
  · exact heightOne_of_card_eight G h
  · letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact heightOne_of_mul_comm G
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := G) (p := 3)
        (by simpa [Nat.card_eq_fintype_card] using h)).is_comm.comm
  · exact heightOne_of_card_ten G h
  · haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
    haveI := isCyclic_of_prime_card (α := G) (p := 11)
      (by simpa [Nat.card_eq_fintype_card] using h)
    exact heightOne_of_mul_comm G (inferInstance : IsMulCommutative G).is_comm.comm

/-- Monotonicity of the ladder in the order bound. -/
theorem HeightOneUpTo.mono {m n : Nat} (hmn : m ≤ n) (h : HeightOneUpTo.{u, v} n) :
    HeightOneUpTo.{u, v} m :=
  fun G _ _ hG => h G (hG.trans hmn)

/-! ### Target above the proved bound -/

/-- Target: the ladder up to order 19.  This remains only a named proposition;
the order-12 theorem and the `A₄` input are already proved. -/
def HeightOneUpToNineteenTarget : Prop := HeightOneUpTo.{u, v} 19

end GSH
