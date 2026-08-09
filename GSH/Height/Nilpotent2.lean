import GSH.Height.Counting
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring

/-!
# Modular counting of the two-letter scattered subword `ab`

`binom2 a b w` is the generalized binomial coefficient `binom(w, ab)` of
Eilenberg: the number of pairs of positions `i < j` with `w[i] = a` and
`w[j] = b`.  By Thérien's theorem a language is recognized by a finite
nilpotent group of class at most two exactly when it is a Boolean combination
of the languages `{w | binom(w,u) % n = r}` with `|u| ≤ 2`, so the height-one
status of these languages is the class-two rung of the height-one ladder.

## What is proved here

* `binom2_append` — the cocycle
  `binom(uv, ab) = binom(u, ab) + binom(v, ab) + |u|_a · |v|_b`.
  This is why the single-letter block decomposition of
  `GSH/Height/Counting.lean` does not transpose: the cross term couples blocks,
  so a block's contribution is not determined by the block.
* `hasHeightAtMost_binom2_self` — **the case `a = b`, complete.**
  `binom(w, aa) = tri |w|_a` is a function of `|w|_a % (2m)`, so the language is
  a finite union of single-letter counting languages and
  `GSH.Counting.hasHeightAtMost_count` applies.
* `hasHeightAtMost_binom2_of_stage` — **the case `a ≠ b`, reduced.**  The
  target is a finite Boolean combination of the *stage* languages
  `{w | stage a b m k 0 w % m = c}`, where `stage a b n k s w` counts the
  occurrences of `b` in `w` whose number of preceding `a`s (offset by `s`) is
  congruent to `k` modulo `n`.  This is the reduction used inside the proof of
  Pin–Straubing–Thérien Theorem 7.3, via the identity
  `binom(w, ab) ≡ Σ_{k<n} k · stage_k(w) (mod n)` (`binom2_mod_eq_sum`).

## What is NOT proved here

`HasHeightAtMost {w | stage a b m k 0 w % m = c} 1` for `a ≠ b` is **open in
this repository**.  It is Pin–Straubing–Thérien 1992, Proposition 6.6, and it
is the whole remaining gap: with it, `hasHeightAtMost_binom2_of_stage` closes
the `a ≠ b` case immediately.  No statement in this file is weakened to make
Lean accept it; the missing input is isolated as a hypothesis.

### The remaining gap, stated precisely

Fix letters `a ≠ b` and `n > 0`.  Let `A_n` be the deterministic automaton on
`Z/nZ` in which `a` acts as `+1` and every other letter acts as the identity;
then `stage a b n k 0 w` is the number of times the path of `w` in `A_n` uses
the edge `(k, b)`.  PST prove `h ≤ 1` for those edge-count languages by:

1. reducing to `k = 0` and residue `0` using left and right quotients
   (their Propositions 6.3 and 6.4; the repository has
   `HasHeightAtMost.leftQuotient` and `HasHeightAtMost.reverse`, which together
   give right quotients, so this step is within reach);
2. writing the loops at `0` that avoid the edge `(0,b)` as the star-free
   language `P = D ∪ (a·(A∖{a})^*)^(n-1)·a`, where `D = A ∖ {a,b}` is a set of
   single letters, so that `T = {b} ∪ P` is a **prefix code** with
   `T^* = {w | |w|_a ≡ 0 mod n}`;
3. observing that `stage a b n 0 0 w` is the number of `{b}`-factors in the
   unique `T`-factorization of `w ∈ T^*`, and applying their **Transfer Lemma**
   6.1.  The naive expression `P^*[(b P^*)^m]^*` has star height *two* because
   `P^*` is not star-free; the Transfer Lemma removes one level using the
   identity `t_b = t - t_P` on factor counts,
   `{t_b ≡ 0} = ⋃_{r<m} [{t ≡ r} ∩ {t_P ≡ r}]`, with `{t ≡ r} = (T^m)^* T^r`
   and `{t_P ≡ r} = (b^* P)^r (b ∪ (P b^*)^(m-1) P)^*`.  Each has a single star
   over a star-free base, because `b^*` is star-free (a single letter) even
   though `P^*` is not.

Step 3 needs unique factorization over a prefix code together with the two
factor-counting identities; none of that machinery exists in this repository.

## Reference

J.-E. Pin, H. Straubing, D. Thérien, *Some results on the generalized
star-height problem*, Inform. and Comput. 101 (1992) 219–250.  The `|u| ≤ 2`
statement is inside the proof of Theorem 7.3 (p. 24); the automaton input is
Proposition 6.6 (pp. 15–16) and the Transfer Lemma is Lemma 6.1 (p. 13).
Preprint: `https://www.irif.fr/~jep/PDF/StarHeight.pdf`.
-/

set_option autoImplicit false

namespace GSH

universe u

namespace Nilpotent2

variable {α : Type u} [DecidableEq α]

/-! ### The scattered subword count -/

/-- `binom2 a b w` is the number of pairs of positions `i < j` in `w` with
`w[i] = a` and `w[j] = b`; the generalized binomial coefficient `binom(w, ab)`. -/
def binom2 (a b : α) : Word α → Nat
  | [] => 0
  | c :: w => (if c = a then w.count b else 0) + binom2 a b w

@[simp] theorem binom2_nil (a b : α) : binom2 a b ([] : Word α) = 0 := rfl

theorem binom2_cons (a b c : α) (w : Word α) :
    binom2 a b (c :: w) = (if c = a then w.count b else 0) + binom2 a b w := rfl

/-- **The cocycle.**  `binom(·, ab)` is not additive over concatenation: the
cross term `|u|_a · |v|_b` couples the two factors.  This is exactly why the
single-letter block decomposition of `GSH/Height/Counting.lean` does not
transpose to a two-letter pattern. -/
theorem binom2_append (a b : α) (u v : Word α) :
    binom2 a b (u ++ v) = binom2 a b u + binom2 a b v + u.count a * v.count b := by
  induction u with
  | nil => simp
  | cons c u ih =>
      simp only [List.cons_append, binom2_cons, ih, List.count_append, List.count_cons,
        beq_iff_eq]
      split_ifs <;> ring

/-! ### Stage counts

`stage a b n k s w` counts the occurrences of `b` in `w` whose number of
preceding `a`s, offset by the initial value `s`, is congruent to `k` modulo
`n`.  Equivalently it counts the uses of the edge `(k, b)` on the path of `w`
in the `Z/nZ`-automaton that increments on `a` and fixes every other letter. -/

/-- The offset-weighted sum: each occurrence of `b` contributes the current
number of preceding `a`s, offset by `s`. -/
def wsum (a b : α) : Nat → Word α → Nat
  | _, [] => 0
  | s, c :: w => (if c = b then s else 0) + wsum a b (if c = a then s + 1 else s) w

/-- Occurrences of `b` at `a`-offset congruent to `k` modulo `n`. -/
def stage (a b : α) (n k : Nat) : Nat → Word α → Nat
  | _, [] => 0
  | s, c :: w =>
      (if c = b ∧ s % n = k then 1 else 0) +
        stage a b n k (if c = a then s + 1 else s) w

@[simp] theorem wsum_nil (a b : α) (s : Nat) : wsum a b s ([] : Word α) = 0 := rfl

theorem wsum_cons (a b c : α) (s : Nat) (w : Word α) :
    wsum a b s (c :: w) =
      (if c = b then s else 0) + wsum a b (if c = a then s + 1 else s) w := rfl

@[simp] theorem stage_nil (a b : α) (n k s : Nat) :
    stage a b n k s ([] : Word α) = 0 := rfl

theorem stage_cons (a b c : α) (n k s : Nat) (w : Word α) :
    stage a b n k s (c :: w) =
      (if c = b ∧ s % n = k then 1 else 0) +
        stage a b n k (if c = a then s + 1 else s) w := rfl

/-- The offset-weighted sum differs from `binom2` by `s` per occurrence of `b`. -/
theorem wsum_eq (a b : α) (s : Nat) (w : Word α) :
    wsum a b s w = s * w.count b + binom2 a b w := by
  induction w generalizing s with
  | nil => simp
  | cons c w ih =>
      simp only [wsum_cons, ih, binom2_cons, List.count_cons, beq_iff_eq]
      split_ifs <;> ring

theorem wsum_zero (a b : α) (w : Word α) : wsum a b 0 w = binom2 a b w := by
  simp [wsum_eq]

/-- The head contribution to the weighted stage sum. -/
theorem sum_stage_head (b c : α) {n : Nat} (hn : 0 < n) (s : Nat) :
    ∑ k ∈ Finset.range n, k * (if c = b ∧ s % n = k then 1 else 0)
      = if c = b then s % n else 0 := by
  by_cases hcb : c = b
  · rw [if_pos hcb]
    have hmem : s % n ∈ Finset.range n := Finset.mem_range.mpr (Nat.mod_lt _ hn)
    rw [Finset.sum_eq_single_of_mem (s % n) hmem
      (fun k _ hk => by simp [hcb, Ne.symm hk])]
    simp [hcb]
  · rw [if_neg hcb]
    simp [hcb]

/-- **The stage decomposition.**  Modulo `n`, the offset-weighted sum is the
`k`-weighted sum of the stage counts.  This is the identity
`binom(w,ab) = Σ_{i<n} i · |p(w)|_{(i,b)}` used inside the proof of
Pin–Straubing–Thérien Theorem 7.3. -/
theorem wsum_modEq_sum_stage (a b : α) {n : Nat} (hn : 0 < n) (s : Nat)
    (w : Word α) :
    wsum a b s w ≡ ∑ k ∈ Finset.range n, k * stage a b n k s w [MOD n] := by
  induction w generalizing s with
  | nil => simp [Nat.ModEq]
  | cons c w ih =>
      have hsplit :
          ∑ k ∈ Finset.range n, k * stage a b n k s (c :: w)
            = (if c = b then s % n else 0)
              + ∑ k ∈ Finset.range n,
                  k * stage a b n k (if c = a then s + 1 else s) w := by
        simp only [stage_cons, Nat.mul_add, Finset.sum_add_distrib]
        rw [sum_stage_head b c hn s]
      rw [hsplit, wsum_cons]
      by_cases hcb : c = b
      · rw [if_pos hcb, if_pos hcb]
        exact Nat.ModEq.add (Nat.mod_modEq s n).symm (ih _)
      · rw [if_neg hcb, if_neg hcb]
        exact Nat.ModEq.add (Nat.ModEq.refl 0) (ih _)

/-- The subword count modulo `m`, as a weighted sum of stage residues. -/
theorem binom2_mod_eq_sum (a b : α) {m : Nat} (hm : 0 < m) (w : Word α) :
    binom2 a b w % m
      = (∑ k : Fin m, (k : Nat) * (stage a b m (k : Nat) 0 w % m)) % m := by
  classical
  have h1 : binom2 a b w ≡ ∑ k ∈ Finset.range m, k * stage a b m k 0 w [MOD m] := by
    rw [← wsum_zero]
    exact wsum_modEq_sum_stage a b hm 0 w
  have h2 : ∀ t : Finset Nat,
      (∑ k ∈ t, k * stage a b m k 0 w) ≡
        (∑ k ∈ t, k * (stage a b m k 0 w % m)) [MOD m] := by
    intro t
    refine Finset.induction_on t (by simp [Nat.ModEq]) ?_
    intro x t' hx ih
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact Nat.ModEq.add (Nat.ModEq.mul_left x (Nat.mod_modEq _ m).symm) ih
  have h3 : binom2 a b w % m
      = (∑ k ∈ Finset.range m, k * (stage a b m k 0 w % m)) % m :=
    h1.trans (h2 (Finset.range m))
  rw [h3, Fin.sum_univ_eq_sum_range (fun k => k * (stage a b m k 0 w % m)) m]

/-! ### The case `a = b`

`binom(w, aa)` is the triangular number of `|w|_a`, whose residue modulo `m`
depends only on `|w|_a` modulo `2m`.  So the language is a finite union of
single-letter counting languages. -/

/-- `tri n = 0 + 1 + ⋯ + (n-1)`, i.e. `C(n, 2)`. -/
def tri : Nat → Nat
  | 0 => 0
  | n + 1 => n + tri n

@[simp] theorem tri_zero : tri 0 = 0 := rfl

theorem tri_succ (n : Nat) : tri (n + 1) = n + tri n := rfl

theorem binom2_self (a : α) (w : Word α) : binom2 a a w = tri (w.count a) := by
  induction w with
  | nil => simp
  | cons c w ih =>
      simp only [binom2_cons, ih, List.count_cons, beq_iff_eq]
      split_ifs with hc
      · rw [tri_succ]
      · simp

/-- `tri` is quadratic: `tri (x+y) = tri x + x·y + tri y`. -/
theorem tri_add (x y : Nat) : tri (x + y) = tri x + x * y + tri y := by
  induction y with
  | zero => simp
  | succ j ih =>
      have hx : x + (j + 1) = (x + j) + 1 := by omega
      rw [hx, tri_succ, ih, tri_succ]
      ring

theorem two_mul_tri (n : Nat) : 2 * tri n = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [tri_succ, Nat.mul_add, ih, Nat.add_sub_cancel]
      cases k with
      | zero => simp
      | succ j => simp only [Nat.add_sub_cancel]; ring

theorem tri_two_mul (m : Nat) : tri (2 * m) = m * (m - 1 + m) := by
  have h : tri (m + m) = tri m + m * m + tri m := tri_add m m
  have h2 : 2 * tri m = m * (m - 1) := two_mul_tri m
  have hm : 2 * m = m + m := by ring
  rw [hm, h, Nat.mul_add]
  omega

/-- Shifting the letter count by a multiple of `2m` leaves `tri` unchanged
modulo `m`. -/
theorem tri_shift (x m t : Nat) : tri (x + 2 * m * t) % m = tri x % m := by
  induction t with
  | zero => simp
  | succ j ih =>
      have hx : x + 2 * m * (j + 1) = (x + 2 * m * j) + 2 * m := by ring
      rw [hx, tri_add, tri_two_mul]
      have e1 : (x + 2 * m * j) * (2 * m) = m * (2 * (x + 2 * m * j)) := by ring
      rw [e1, Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left]
      exact ih

theorem tri_mod (n m : Nat) : tri n % m = tri (n % (2 * m)) % m := by
  conv_lhs => rw [← Nat.mod_add_div n (2 * m)]
  exact tri_shift _ _ _

/-- **The case `a = b` of the two-letter counting theorem.**  For every letter
`a`, every modulus `m` and every residue `r < m`, the language
`{w | binom(w, aa) % m = r}` has generalized star height at most one. -/
theorem hasHeightAtMost_binom2_self (a : α) {m r : Nat} (hr : r < m) :
    HasHeightAtMost {w : Word α | binom2 a a w % m = r} 1 := by
  classical
  have hM : 0 < 2 * m := by omega
  have hset :
      {w : Word α | binom2 a a w % m = r} =
        ⋃ j : {j : Fin (2 * m) // tri (j : Nat) % m = r},
          {w : Word α | w.count a % (2 * m) = ((j : Fin (2 * m)) : Nat)} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hw
      rw [binom2_self, tri_mod] at hw
      exact ⟨⟨⟨w.count a % (2 * m), Nat.mod_lt _ hM⟩, hw⟩, rfl⟩
    · rintro ⟨j, hj⟩
      rw [binom2_self, tri_mod, hj]
      exact j.2
  rw [hset]
  letI : Fintype {j : Fin (2 * m) // tri (j : Nat) % m = r} := Fintype.ofFinite _
  refine HasHeightAtMost.iUnion _ (fun j => ?_)
  exact Counting.hasHeightAtMost_count a (j.1).2

/-! ### The case `a ≠ b`, reduced to stage counts

The target language is a finite Boolean combination of the stage languages,
by `binom2_mod_eq_sum`.  What remains is Pin–Straubing–Thérien Proposition 6.6,
which is not proved in this repository. -/

/-- **Reduction of the two-letter counting theorem to stage counts.**  If every
stage-count language has generalized star height at most one, then so does
`{w | binom(w, ab) % m = r}`.  The hypothesis is exactly
Pin–Straubing–Thérien Proposition 6.6 for the `Z/mZ`-automaton that counts `a`. -/
theorem hasHeightAtMost_binom2_of_stage (a b : α) {m r : Nat} (hr : r < m)
    (hstage : ∀ k c : Nat, k < m → c < m →
      HasHeightAtMost {w : Word α | stage a b m k 0 w % m = c} 1) :
    HasHeightAtMost {w : Word α | binom2 a b w % m = r} 1 := by
  classical
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  have hset :
      {w : Word α | binom2 a b w % m = r} =
        ⋃ v : {v : Fin m → Fin m // (∑ k : Fin m, (k : Nat) * (v k : Nat)) % m = r},
          ⋂ k : Fin m,
            {w : Word α |
              stage a b m (k : Nat) 0 w % m = (((v : Fin m → Fin m) k : Fin m) : Nat)} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · intro hw
      have hval : (∑ k : Fin m, (k : Nat) * (stage a b m (k : Nat) 0 w % m)) % m = r := by
        rw [← binom2_mod_eq_sum a b hm w]; exact hw
      exact ⟨⟨fun k => ⟨stage a b m (k : Nat) 0 w % m, Nat.mod_lt _ hm⟩, hval⟩,
        fun k => rfl⟩
    · rintro ⟨v, hv⟩
      rw [binom2_mod_eq_sum a b hm w]
      have hcongr : (∑ k : Fin m, (k : Nat) * (stage a b m (k : Nat) 0 w % m))
          = ∑ k : Fin m, (k : Nat) * (((v : Fin m → Fin m) k : Fin m) : Nat) :=
        Finset.sum_congr rfl (fun k _ => by rw [hv k])
      rw [hcongr]
      exact v.2
  rw [hset]
  letI : Fintype {v : Fin m → Fin m // (∑ k : Fin m, (k : Nat) * (v k : Nat)) % m = r} :=
    Fintype.ofFinite _
  refine HasHeightAtMost.iUnion _ (fun v => ?_)
  refine HasHeightAtMost.iInter _ (fun k => ?_)
  exact hstage (k : Nat) (((v : Fin m → Fin m) k : Fin m) : Nat) k.2
    ((v : Fin m → Fin m) k).2

end Nilpotent2

end GSH
