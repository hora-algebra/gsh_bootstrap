import GSH.Challenges.GeneralizedStarHeight
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.CompleteLattice.Finset

/-!
# Closure properties of bounded generalized star height

Everything in this file is elementary: the generalized-expression syntax of
`GSH/Challenges/GeneralizedStarHeight.lean` has `union` and `compl` as
height-preserving constructors, so the class of languages of generalized star
height at most `n` is a Boolean algebra for every fixed `n`.  These are the
closure facts consumed by the finite-group ladder.

The only non-immediate item is `GRegex.pow`, the iterated concatenation used to
build counting expressions in `GSH/Height/Counting.lean`; its star height is
bounded by that of the base expression, *including* the exponent-zero case,
because `epsilon` has height zero.

Obligation `L-CNT-001` in `PROOF_OBLIGATIONS.md` covers this file together with
`GSH/Height/Counting.lean`.
-/

set_option autoImplicit false

namespace GSH

universe u v

/-! ### Iterated concatenation of expressions -/

namespace GRegex

variable {α : Type u}

/-- `pow r k` is the `k`-fold concatenation `r · r · … · r`, with `pow r 0 = ε`.
It mirrors `Language.power` on the semantic side. -/
def pow (r : GRegex α) : Nat → GRegex α
  | 0 => GRegex.epsilon
  | k + 1 => GRegex.concat (pow r k) r

@[simp] theorem pow_zero (r : GRegex α) : pow r 0 = GRegex.epsilon := rfl

@[simp] theorem pow_succ (r : GRegex α) (k : Nat) :
    pow r (k + 1) = GRegex.concat (pow r k) r := rfl

@[simp] theorem denote_pow (r : GRegex α) (k : Nat) :
    denote (pow r k) = Language.power (denote r) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pow, denote, Language.power, ih]

/-- Iterated concatenation does not increase star height. -/
theorem starHeight_pow_le (r : GRegex α) (k : Nat) :
    starHeight (pow r k) ≤ starHeight r := by
  induction k with
  | zero => simp [pow]
  | succ k ih =>
      simp only [pow, starHeight]
      exact max_le ih le_rfl

end GRegex

/-! ### Boolean closure at a fixed height bound -/

namespace HasHeightAtMost

variable {α : Type u}

theorem mono {L : Language α} {m n : Nat} (h : HasHeightAtMost L m) (hmn : m ≤ n) :
    HasHeightAtMost L n := by
  obtain ⟨r, hr, hh⟩ := h
  exact ⟨r, hr, hh.trans hmn⟩

theorem union {L K : Language α} {n : Nat}
    (hL : HasHeightAtMost L n) (hK : HasHeightAtMost K n) :
    HasHeightAtMost (L ∪ K) n := by
  obtain ⟨r, hr, hrh⟩ := hL
  obtain ⟨s, hs, hsh⟩ := hK
  refine ⟨GRegex.union r s, ?_, ?_⟩
  · simp [GRegex.denote, hr, hs]
  · simpa [GRegex.starHeight] using max_le hrh hsh

theorem compl {L : Language α} {n : Nat} (hL : HasHeightAtMost L n) :
    HasHeightAtMost Lᶜ n := by
  obtain ⟨r, hr, hrh⟩ := hL
  refine ⟨GRegex.compl r, ?_, ?_⟩
  · simp [GRegex.denote, Language.compl, hr]
  · simpa [GRegex.starHeight] using hrh

theorem inter {L K : Language α} {n : Nat}
    (hL : HasHeightAtMost L n) (hK : HasHeightAtMost K n) :
    HasHeightAtMost (L ∩ K) n := by
  have h := (hL.compl.union hK.compl).compl
  simpa [Set.compl_union, compl_compl] using h

theorem empty {n : Nat} : HasHeightAtMost (∅ : Language α) n :=
  ⟨GRegex.zero, rfl, Nat.zero_le n⟩

theorem univ {n : Nat} : HasHeightAtMost (Set.univ : Language α) n := by
  have h := (empty (α := α) (n := n)).compl
  simpa using h

/-- A language equal to one of bounded height has bounded height. -/
theorem congr {L K : Language α} {n : Nat} (h : HasHeightAtMost L n) (hLK : L = K) :
    HasHeightAtMost K n := hLK ▸ h

/-! ### Finite unions and intersections -/

theorem finset_biUnion {ι : Type v} {n : Nat} (s : Finset ι) (L : ι → Language α)
    (h : ∀ i, HasHeightAtMost (L i) n) :
    HasHeightAtMost (⋃ i ∈ s, L i) n := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using (empty (α := α) (n := n))
  · intro a t _ ih
    rw [Finset.set_biUnion_insert]
    exact (h a).union ih

theorem finset_biInter {ι : Type v} {n : Nat} (s : Finset ι) (L : ι → Language α)
    (h : ∀ i, HasHeightAtMost (L i) n) :
    HasHeightAtMost (⋂ i ∈ s, L i) n := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using (univ (α := α) (n := n))
  · intro a t _ ih
    rw [Finset.set_biInter_insert]
    exact (h a).inter ih

theorem iUnion {ι : Type v} [Fintype ι] {n : Nat} (L : ι → Language α)
    (h : ∀ i, HasHeightAtMost (L i) n) :
    HasHeightAtMost (⋃ i, L i) n := by
  have h' := finset_biUnion (α := α) (Finset.univ : Finset ι) L h
  simpa using h'

theorem iInter {ι : Type v} [Fintype ι] {n : Nat} (L : ι → Language α)
    (h : ∀ i, HasHeightAtMost (L i) n) :
    HasHeightAtMost (⋂ i, L i) n := by
  have h' := finset_biInter (α := α) (Finset.univ : Finset ι) L h
  simpa using h'

end HasHeightAtMost

end GSH
