import GSH.Groups.Abelian
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.PGroup

/-!
# The finite-group ladder indexed by order

`HeightOneUpTo n` is the statement "every language recognized by a group of
order at most `n` has generalized star height at most one".

**Proved here: `n = 5`** (obligation `L-ORD5-001`), because every group of order
at most five is commutative — orders 1, 2, 3, 5 by primality and order 4 by the
`p²` theorem — and `heightOne_of_mul_comm` settles the commutative case.  The
bound is sharp for this argument: `S_3` has order six and is not commutative.

## Where the ladder goes next, and what blocks it

Every group of order at most 19 **except `A_4`** has a commutative subgroup of
index at most two:

* odd order (1, 3, 5, 7, 9, 11, 13, 15, 17, 19): commutative outright;
* 2-groups (2, 4, 8, 16): non-cyclic ⇒ `|Φ(G)| ≤ |G|/4 ≤ 4` by the Burnside
  basis theorem, so `Φ(G) = G²[G,G]` is commutative; order 16 also has a
  commutative maximal subgroup as a group of order `p⁴`;
* order `2p` (6, 10, 14): the Sylow `p`-subgroup is normal, cyclic, of index 2;
* order 12: `D_6` and `Dic_3` contain `C_6` with index 2; **`A_4` has no
  subgroup of index 2 at all**;
* order 18: the Sylow 3-subgroup (`C_9` or `C_3²`) is commutative of index 2.

Such a `G` is **not** in general isomorphic to `H ⋊ C_2`: the extension
`1 → H → G → C_2 → 1` need not split, and among the orders listed it often does
not (`C_4` over `C_2`, `Q_8` over `C_4`, `Dic_3` over `C_6`).  What repairs this
is the Krasner–Kaloujnine universal embedding (obligation `L-KK-001`), which
holds for *every* extension, split or not: fixing any transversal `t : Q → G`,

  `g ↦ (f_g, ḡ)`,  `f_g(q) = t(ḡq)⁻¹ * g * t(q) ∈ H`

is an injective morphism `G ↪ H ≀ Q`.  Failure of `t` to be a morphism is
absorbed by the base `H^Q`, not by the quotient.  At `Q = C_2` the host is
`H ≀ C_2 = (H × H) ⋊ C_2`, a genuinely split semidirect product of the
commutative group `H × H` by `C_2`.

So with that embedding and the divisor transfer of `GSH/Transfer.lean`, the
whole non-commutative part of `n ≤ 19` reduces to the **single** theorem
"`A ⋊ C_2` has the height-one property for commutative `A`" (`L-ABC2-001`,
mathematically `M-PST-003`), plus `A_4` (`L-A4-001`).

`A_4` is the genuinely open one.  The repository's evidence for it is `EMPIRICAL`
(ledger rows `A4-FULL-01` / `A4-ALLLANG-01`): a Python search whose reconstruction
step is exhaustive only to word length 4 plus random words, so it is a finite
sample of an infinite claim, not a decided computation.  Research rules 1 and 4
forbid importing that as a proved fact, and here there is nothing to import.  The targets
below are therefore `def`s of type `Prop`: named statements, deliberately
carrying **no** proof and **no** `sorry`.
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

/-- Monotonicity of the ladder in the order bound. -/
theorem HeightOneUpTo.mono {m n : Nat} (hmn : m ≤ n) (h : HeightOneUpTo.{u, v} n) :
    HeightOneUpTo.{u, v} m :=
  fun G _ _ hG => h G (hG.trans hmn)

/-! ### Targets above the current frontier

These are named statements only.  Nothing below asserts that they hold. -/

/-- Target: the ladder up to order 11.  Needs `L-ABC2-001` (`A ⋊ C_2`) and
`L-KK-001` (Krasner–Kaloujnine); the non-commutative groups involved are
`S_3`, `D_4`, `Q_8`, `D_5`. -/
def HeightOneUpToElevenTarget : Prop := HeightOneUpTo.{u, v} 11

/-- Target: the ladder up to order 19.  Needs, in addition to the order-11
inputs, the group-theoretic classification step `L-ORD19-GRP-001` and the
currently unproved `L-A4-001`. -/
def HeightOneUpToNineteenTarget : Prop := HeightOneUpTo.{u, v} 19

end GSH
