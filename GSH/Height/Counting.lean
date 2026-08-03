import GSH.Height.Closure
import Mathlib.Data.List.Count

/-!
# Counting languages have generalized star height at most one

For a letter `a`, a modulus `m > 0` and a residue `r < m`, the language

  `{w | w.count a % m = r}`

has generalized star height at most one.  This is the single technical input
that the finite-abelian-group case of the height-one ladder needs; obligation
`L-CNT-001` in `PROOF_OBLIGATIONS.md`.

## The construction and why it stays at height one

The naive expression `((Σ∖a)* a)^r ((Σ∖a)* a)^m)* (Σ∖a)*` has star height **two**,
because `(Σ∖a)*` is already a star and the outer `( … )*` nests on top of it.
The point of the *generalized* setting is that complement is free, so the
letter-avoiding language is available at height zero:

  `univR = ¬∅`                          all words                      height 0
  `hasA  = univR · a · univR`           words containing `a`           height 0
  `noA   = ¬hasA`                       words avoiding `a`             height 0
  `blk   = noA · a`                     exactly one `a`, at the end    height 0
  `cnt   = blk^r · (blk^m)* · noA`                                     height 1

so the single `star` in `cnt` is the only one in the whole expression.

## Proof skeleton

`Blocks a k` is the set of words with exactly `k` occurrences of `a` that are
empty or end in `a`; it is what a `k`-fold power of `blk` denotes.  The two
facts that drive everything are `concat_blocks` (`Blocks i · Blocks j =
Blocks (i+j)`, the ⊇ direction being the splitting lemma `exists_split`) and
`concat_blocks_zeroCount` (`Blocks k · {count = 0} = {count = k}`).
-/

set_option autoImplicit false

namespace GSH

universe u

namespace Counting

variable {α : Type u}

/-! ### Words that are empty or end in `a` -/

/-- `w` is empty or ends in the letter `a`. -/
def ATerm (a : α) (w : Word α) : Prop := w = [] ∨ ∃ u : Word α, w = u ++ [a]

theorem aTerm_nil (a : α) : ATerm a ([] : Word α) := Or.inl rfl

theorem aTerm_append_singleton (a : α) (u : Word α) : ATerm a (u ++ [a]) :=
  Or.inr ⟨u, rfl⟩

/-- Appending an `a`-terminated word to an `a`-terminated word keeps the property. -/
theorem ATerm.append {a : α} {u v : Word α} (hu : ATerm a u) (hv : ATerm a v) :
    ATerm a (u ++ v) := by
  rcases hv with rfl | ⟨z, rfl⟩
  · simpa using hu
  · exact Or.inr ⟨u ++ z, by simp⟩

/-- Any suffix of an `a`-terminated word is `a`-terminated. -/
theorem ATerm.of_append_right {a : α} {x z : Word α} (h : ATerm a (x ++ z)) :
    ATerm a z := by
  rcases List.eq_nil_or_concat z with rfl | ⟨z', c, rfl⟩
  · exact aTerm_nil a
  · rw [List.concat_eq_append] at h ⊢
    rcases h with h | ⟨u, hu⟩
    · exact absurd h (by simp)
    · rw [← List.append_assoc] at hu
      have hlen : ([c] : Word α).length = ([a] : Word α).length := by simp
      have hc := (List.append_inj' hu hlen).2
      simp only [List.cons.injEq, and_true] at hc
      exact Or.inr ⟨z', by rw [hc]⟩

/-! ### The block languages -/

variable [DecidableEq α]

/-- Words with exactly `k` occurrences of `a` that are empty or end in `a`. -/
def Blocks (a : α) (k : Nat) : Language α := {w : Word α | w.count a = k ∧ ATerm a w}

theorem mem_blocks {a : α} {k : Nat} {w : Word α} :
    w ∈ Blocks a k ↔ w.count a = k ∧ ATerm a w := Iff.rfl

theorem blocks_zero (a : α) : Blocks a 0 = {([] : Word α)} := by
  ext w
  simp only [mem_blocks, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hcount, hterm⟩
    rcases hterm with rfl | ⟨u, rfl⟩
    · rfl
    · simp at hcount
  · rintro rfl
    exact ⟨by simp, aTerm_nil a⟩

/-- First occurrence of `a`: split off the shortest `a`-terminated prefix. -/
theorem exists_first_occ (a : α) :
    ∀ z : Word α, a ∈ z → ∃ z₁ z₂ : Word α, z = (z₁ ++ [a]) ++ z₂ ∧ z₁.count a = 0 := by
  intro z
  induction z with
  | nil => intro h; exact absurd h (by simp)
  | cons b z ih =>
      intro h
      by_cases hb : b = a
      · subst hb
        exact ⟨[], z, by simp, by simp⟩
      · have hz : a ∈ z := by
          rcases List.mem_cons.1 h with h' | h'
          · exact absurd h'.symm hb
          · exact h'
        obtain ⟨z₁, z₂, hsplit, hcount⟩ := ih hz
        exact ⟨b :: z₁, z₂, by rw [hsplit]; simp, by simp [hcount, hb]⟩

/-- **Splitting lemma.**  A word with at least `i` occurrences of `a` splits as an
`a`-terminated prefix carrying exactly `i` of them, followed by the rest. -/
theorem exists_split (a : α) (w : Word α) :
    ∀ i : Nat, i ≤ w.count a → ∃ x z : Word α, w = x ++ z ∧ x.count a = i ∧ ATerm a x := by
  intro i
  induction i with
  | zero => intro _; exact ⟨[], w, by simp, by simp, aTerm_nil a⟩
  | succ i ih =>
      intro hle
      obtain ⟨x, z, rfl, hx, hxterm⟩ := ih (Nat.le_of_succ_le hle)
      have hadd : (x ++ z).count a = x.count a + z.count a := List.count_append
      have hz : 0 < z.count a := by omega
      obtain ⟨z₁, z₂, rfl, hz₁⟩ := exists_first_occ a z (List.count_pos_iff.1 hz)
      refine ⟨x ++ (z₁ ++ [a]), z₂, by simp, ?_, hxterm.append (aTerm_append_singleton a z₁)⟩
      simp [hx, hz₁]

/-- Concatenating block languages adds the block counts. -/
theorem concat_blocks (a : α) (i j : Nat) :
    Language.concat (Blocks a i) (Blocks a j) = Blocks a (i + j) := by
  ext w
  constructor
  · rintro ⟨u, ⟨hu, huterm⟩, v, ⟨hv, hvterm⟩, rfl⟩
    exact ⟨by simp [hu, hv], huterm.append hvterm⟩
  · rintro ⟨hcount, hterm⟩
    obtain ⟨x, z, rfl, hx, hxterm⟩ := exists_split a w i (by omega)
    have hadd : (x ++ z).count a = x.count a + z.count a := List.count_append
    exact ⟨x, ⟨hx, hxterm⟩, z, ⟨by omega, hterm.of_append_right⟩, rfl⟩

/-- The tail after the last `a` contributes nothing to the count. -/
theorem concat_blocks_zeroCount (a : α) (k : Nat) :
    Language.concat (Blocks a k) {w : Word α | w.count a = 0} = {w : Word α | w.count a = k} := by
  ext w
  constructor
  · rintro ⟨u, ⟨hu, -⟩, v, hv, rfl⟩
    have hv' : v.count a = 0 := hv
    simp [hu, hv']
  · intro hw
    have hw' : w.count a = k := hw
    obtain ⟨x, z, rfl, hx, hxterm⟩ := exists_split a w k (by omega)
    have hadd : (x ++ z).count a = x.count a + z.count a := List.count_append
    exact ⟨x, ⟨hx, hxterm⟩, z, by simp only [Set.mem_setOf_eq]; omega, rfl⟩

/-- Powers of a block language multiply the block counts. -/
theorem power_blocks (a : α) (m n : Nat) :
    Language.power (Blocks a m) n = Blocks a (m * n) := by
  induction n with
  | zero => simpa [Language.power, Language.epsilon] using (blocks_zero a).symm
  | succ n ih =>
      rw [Language.power, ih, concat_blocks, Nat.mul_succ]

theorem star_blocks (a : α) (m : Nat) :
    Language.star (Blocks a m) = ⋃ n : Nat, Blocks a (m * n) := by
  ext w
  simp only [Language.star, Set.mem_setOf_eq, Set.mem_iUnion, power_blocks]

/-! ### Concatenation distributes over unions -/

omit [DecidableEq α] in
theorem concat_iUnion_left {ι : Type*} (L : ι → Language α) (K : Language α) :
    Language.concat (⋃ i, L i) K = ⋃ i, Language.concat (L i) K := by
  ext w
  simp only [Language.concat, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨u, ⟨i, hi⟩, v, hv, rfl⟩; exact ⟨i, u, hi, v, hv, rfl⟩
  · rintro ⟨i, u, hi, v, hv, rfl⟩; exact ⟨u, ⟨i, hi⟩, v, hv, rfl⟩

omit [DecidableEq α] in
theorem concat_iUnion_right (L : Language α) {ι : Type*} (K : ι → Language α) :
    Language.concat L (⋃ i, K i) = ⋃ i, Language.concat L (K i) := by
  ext w
  simp only [Language.concat, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨u, hu, v, ⟨i, hi⟩, rfl⟩; exact ⟨i, u, hu, v, hi, rfl⟩
  · rintro ⟨i, u, hu, v, hi, rfl⟩; exact ⟨u, hu, v, ⟨i, hi⟩, rfl⟩

/-! ### The expressions -/

/-- All words, as a height-zero expression. -/
def univR : GRegex α := GRegex.compl GRegex.zero

/-- Words containing at least one `a`. -/
def hasA (a : α) : GRegex α :=
  GRegex.concat (GRegex.concat univR (GRegex.atom a)) univR

/-- Words avoiding `a`, obtained by **complement** rather than by a star. -/
def noA (a : α) : GRegex α := GRegex.compl (hasA a)

/-- Exactly one `a`, occurring at the very end. -/
def blk (a : α) : GRegex α := GRegex.concat (noA a) (GRegex.atom a)

/-- `count a w % m = r` as a generalized expression of star height one. -/
def cnt (a : α) (m r : Nat) : GRegex α :=
  GRegex.concat
    (GRegex.concat (GRegex.pow (blk a) r) (GRegex.star (GRegex.pow (blk a) m)))
    (noA a)

omit [DecidableEq α] in
theorem denote_univR : GRegex.denote (univR : GRegex α) = Set.univ := by
  ext w
  simp [univR, GRegex.denote, Language.compl, Language.empty]

omit [DecidableEq α] in
theorem denote_hasA (a : α) : GRegex.denote (hasA a) = {w : Word α | a ∈ w} := by
  rw [hasA]
  show Language.concat (Language.concat (GRegex.denote univR) (Language.letter a))
      (GRegex.denote univR) = _
  rw [denote_univR]
  ext w
  constructor
  · rintro ⟨p, ⟨x, -, y, hy, rfl⟩, v, -, rfl⟩
    have hy' : y = [a] := hy
    subst hy'
    simp
  · intro hw
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hw
    exact ⟨s ++ [a], ⟨s, Set.mem_univ _, [a], rfl, rfl⟩, t, Set.mem_univ _, by simp⟩

theorem denote_noA (a : α) : GRegex.denote (noA a) = {w : Word α | w.count a = 0} := by
  rw [noA]
  show Language.compl (GRegex.denote (hasA a)) = _
  rw [denote_hasA]
  ext w
  simp [Language.compl, List.count_eq_zero]

theorem denote_blk (a : α) : GRegex.denote (blk a) = Blocks a 1 := by
  rw [blk]
  show Language.concat (GRegex.denote (noA a)) (Language.letter a) = _
  rw [denote_noA]
  ext w
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    have hu' : u.count a = 0 := hu
    have hv' : v = [a] := hv
    subst hv'
    exact ⟨by simp [hu'], aTerm_append_singleton a u⟩
  · rintro ⟨hcount, hterm⟩
    rcases hterm with rfl | ⟨u, rfl⟩
    · simp at hcount
    · refine ⟨u, ?_, [a], rfl, rfl⟩
      simp only [Set.mem_setOf_eq]
      simp at hcount
      omega

theorem denote_pow_blk (a : α) (k : Nat) :
    GRegex.denote (GRegex.pow (blk a) k) = Blocks a k := by
  rw [GRegex.denote_pow, denote_blk, power_blocks, Nat.one_mul]

/-! ### The counting language -/

theorem count_mod_iff {k m r : Nat} (hr : r < m) :
    k % m = r ↔ ∃ n : Nat, k = r + m * n := by
  constructor
  · intro h
    refine ⟨k / m, ?_⟩
    have := Nat.div_add_mod k m
    omega
  · rintro ⟨n, rfl⟩
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

theorem denote_cnt (a : α) {m r : Nat} (hr : r < m) :
    GRegex.denote (cnt a m r) = {w : Word α | w.count a % m = r} := by
  simp only [cnt, GRegex.denote, denote_pow_blk, denote_noA, star_blocks]
  rw [concat_iUnion_right]
  rw [show (⋃ n : Nat, Language.concat (Blocks a r) (Blocks a (m * n)))
        = ⋃ n : Nat, Blocks a (r + m * n) from
      Set.iUnion_congr fun n => concat_blocks a r (m * n)]
  rw [concat_iUnion_left]
  rw [show (⋃ n : Nat, Language.concat (Blocks a (r + m * n)) {w : Word α | w.count a = 0})
        = ⋃ n : Nat, {w : Word α | w.count a = r + m * n} from
      Set.iUnion_congr fun n => concat_blocks_zeroCount a (r + m * n)]
  ext w
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  exact (count_mod_iff hr).symm

/-- **The counting language has generalized star height at most one.** -/
theorem hasHeightAtMost_count (a : α) {m r : Nat} (hr : r < m) :
    HasHeightAtMost {w : Word α | w.count a % m = r} 1 := by
  refine ⟨cnt a m r, denote_cnt a hr, ?_⟩
  have hblk : GRegex.starHeight (blk a) = 0 := by
    simp [blk, noA, hasA, univR, GRegex.starHeight]
  have hr' : GRegex.starHeight (GRegex.pow (blk a) r) ≤ 0 := by
    simpa [hblk] using GRegex.starHeight_pow_le (blk a) r
  have hm' : GRegex.starHeight (GRegex.pow (blk a) m) ≤ 0 := by
    simpa [hblk] using GRegex.starHeight_pow_le (blk a) m
  have hnoA : GRegex.starHeight (noA a) = 0 := by
    simp [noA, hasA, univR, GRegex.starHeight]
  simp only [cnt, GRegex.starHeight, hnoA]
  omega

end Counting

end GSH
