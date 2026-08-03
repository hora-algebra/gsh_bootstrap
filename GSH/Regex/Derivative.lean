import GSH.Regex.HeightClosure

/-!
# Brzozowski derivatives for `GRegex`

Brzozowski derivatives for the generalized regular expressions `GRegex`:
`deriv a r` denotes the left quotient `{w | a :: w ∈ denote r}`
(`denote_deriv`) and never increases the star height (`starHeight_deriv`).
Hence `HasHeightAtMost` is closed under left-letter quotients
(`hasHeightAtMost_deriv`) and, iterating along a word, under left-word
quotients (`hasHeightAtMost_derivWord`).  Used to rebuild the phase-`q` cut
features (obligation `N-A4-FULL-034`) from the phase-0 feature.

`Language.power` recurses on the right (`power L (n+1) = concat (power L n) L`),
so the star case needs left-peeling lemmas (`mem_power_succ_iff_left`,
`cons_mem_star_iff`); the first reuses `concat_power_comm` from
`GSH.Regex.HeightClosure` instead of redoing its induction.

This file contains no `sorry` and no `axiom`.
-/

set_option autoImplicit false

namespace GSH

universe u
variable {α : Type u}

/-! ## Left-peeling lemmas for `power`, `star`, and `concat` -/

/-- Left-recursive form of `Language.power_succ`, via `concat_power_comm`. -/
theorem mem_power_succ_iff_left (L : Language α) (n : Nat) (w : Word α) :
    w ∈ Language.power L (n + 1) ↔
      ∃ u ∈ L, ∃ v ∈ Language.power L n, u ++ v = w := by
  rw [Language.power_succ, concat_power_comm]
  exact Language.mem_concat_iff _ _ _

/-- Peeling the leftmost letter of a nonempty word of `power L n`: empty
leading blocks contribute nothing and are discarded, so the remainder is
only known to lie in `star L`, not in a fixed power. -/
theorem cons_mem_power_exists (L : Language α) :
    ∀ (n : Nat) (a : α) (w : Word α), a :: w ∈ Language.power L n →
      ∃ u v, w = u ++ v ∧ a :: u ∈ L ∧ v ∈ Language.star L
  | 0, a, w, h => by
    simp [Language.power_zero] at h
  | n + 1, a, w, h => by
    obtain ⟨u, hu, v, hv, huv⟩ := (mem_power_succ_iff_left L n (a :: w)).1 h
    cases u with
    | nil =>
      simp only [List.nil_append] at huv
      subst huv
      exact cons_mem_power_exists L n a w hv
    | cons x u' =>
      rw [List.cons_append] at huv
      injection huv with hx hw
      subst hx
      exact ⟨u', v, hw.symm, hu, (Language.mem_star_iff L v).2 ⟨n, hv⟩⟩

/-- Splitting off the first letter of a nonempty word of `star L`. -/
theorem cons_mem_star_iff (L : Language α) (a : α) (w : Word α) :
    a :: w ∈ Language.star L ↔
      ∃ u v, w = u ++ v ∧ a :: u ∈ L ∧ v ∈ Language.star L := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (Language.mem_star_iff L (a :: w)).1 h
    exact cons_mem_power_exists L n a w hn
  · rintro ⟨u, v, rfl, hu, hv⟩
    obtain ⟨n, hn⟩ := (Language.mem_star_iff L v).1 hv
    exact (Language.mem_star_iff L _).2
      ⟨n + 1, (mem_power_succ_iff_left L n _).2 ⟨a :: u, hu, v, hn, rfl⟩⟩

/-- Splitting a concatenation at its first letter, according to whether the
left factor is empty. -/
theorem cons_mem_concat_iff (L K : Language α) (a : α) (w : Word α) :
    a :: w ∈ Language.concat L K ↔
      ([] ∈ L ∧ a :: w ∈ K) ∨ ∃ u v, w = u ++ v ∧ a :: u ∈ L ∧ v ∈ K := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    cases u with
    | nil =>
      simp only [List.nil_append] at huv
      exact Or.inl ⟨hu, huv ▸ hv⟩
    | cons x u' =>
      rw [List.cons_append] at huv
      injection huv with hx hw
      subst hx
      exact Or.inr ⟨u', v, hw.symm, hu, hv⟩
  · rintro (⟨h0, hK⟩ | ⟨u, v, rfl, hu, hv⟩)
    · exact ⟨[], h0, a :: w, hK, rfl⟩
    · exact ⟨a :: u, hu, v, hv, rfl⟩

namespace GRegex

/-! ## Nullability

`GRegex.nullable` itself is defined in `GSH/Height/FullAlphabet.lean`; only the
spelling of its correctness lemma used below is restated here. -/

theorem nullable_iff (r : GRegex α) : nullable r = true ↔ [] ∈ denote r :=
  nullable_eq_true_iff r

/-! ## The derivative and its correctness -/

/-- Brzozowski derivative by a single letter: `deriv a r` denotes
`{w | a :: w ∈ denote r}` (`denote_deriv`). -/
def deriv [DecidableEq α] (a : α) : GRegex α → GRegex α
  | zero => zero
  | epsilon => zero
  | atom b => if a = b then epsilon else zero
  | union r s => union (deriv a r) (deriv a s)
  | concat r s =>
      if nullable r then union (concat (deriv a r) s) (deriv a s)
      else concat (deriv a r) s
  | compl r => compl (deriv a r)
  | star r => concat (deriv a r) (star r)

theorem denote_deriv [DecidableEq α] (a : α) :
    ∀ r : GRegex α, denote (deriv a r) = {w | a :: w ∈ denote r}
  | zero => by
    ext w
    simp [deriv, denote]
  | epsilon => by
    ext w
    simp [deriv, denote]
  | atom b => by
    by_cases h : a = b
    · subst h
      ext w
      simp [deriv, denote]
    · ext w
      simp [deriv, denote, h]
  | union r s => by
    ext w
    simp [deriv, denote, denote_deriv a r, denote_deriv a s]
  | concat r s => by
    by_cases hn : nullable r
    · have h0 : [] ∈ denote r := (nullable_iff r).1 hn
      have hd : deriv a (concat r s) = union (concat (deriv a r) s) (deriv a s) := by
        simp [deriv, hn]
      rw [hd]
      ext w
      simp only [denote, Set.mem_union, Language.mem_concat_iff, Set.mem_setOf_eq,
        denote_deriv a r, denote_deriv a s]
      constructor
      · rintro (⟨u, hu, v, hv, rfl⟩ | hw)
        · exact ⟨a :: u, hu, v, hv, rfl⟩
        · exact ⟨[], h0, a :: w, hw, rfl⟩
      · rintro ⟨u, hu, v, hv, huv⟩
        cases u with
        | nil =>
          simp only [List.nil_append] at huv
          subst huv
          exact Or.inr hv
        | cons x u' =>
          rw [List.cons_append] at huv
          injection huv with hx hw'
          subst hx
          exact Or.inl ⟨u', hu, v, hv, hw'⟩
    · have h0 : [] ∉ denote r := fun h => hn ((nullable_iff r).2 h)
      have hd : deriv a (concat r s) = concat (deriv a r) s := by
        simp [deriv, hn]
      rw [hd]
      ext w
      simp only [denote, Language.mem_concat_iff, Set.mem_setOf_eq,
        denote_deriv a r]
      constructor
      · rintro ⟨u, hu, v, hv, rfl⟩
        exact ⟨a :: u, hu, v, hv, rfl⟩
      · rintro ⟨u, hu, v, hv, huv⟩
        cases u with
        | nil => exact absurd hu h0
        | cons x u' =>
          rw [List.cons_append] at huv
          injection huv with hx hw'
          subst hx
          exact ⟨u', hu, v, hv, hw'⟩
  | compl r => by
    ext w
    simp [deriv, denote, denote_deriv a r]
  | star r => by
    ext w
    simp only [deriv, denote, Language.mem_concat_iff, Set.mem_setOf_eq,
      denote_deriv a r, cons_mem_star_iff]
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      exact ⟨u, v, rfl, hu, hv⟩
    · rintro ⟨u, v, rfl, hu, hv⟩
      exact ⟨u, hu, v, hv, rfl⟩

/-! ## Height preservation -/

theorem starHeight_deriv [DecidableEq α] (a : α) :
    ∀ r : GRegex α, starHeight (deriv a r) ≤ starHeight r
  | zero => Nat.le_refl _
  | epsilon => Nat.le_refl _
  | atom b => by
    by_cases h : a = b <;> simp [deriv, h]
  | union r s => by
    have hr := starHeight_deriv a r
    have hs := starHeight_deriv a s
    simp only [deriv, starHeight]
    omega
  | concat r s => by
    have hr := starHeight_deriv a r
    have hs := starHeight_deriv a s
    by_cases hn : nullable r
    · have hd : deriv a (concat r s) = union (concat (deriv a r) s) (deriv a s) := by
        simp [deriv, hn]
      rw [hd]
      simp only [starHeight]
      omega
    · have hd : deriv a (concat r s) = concat (deriv a r) s := by
        simp [deriv, hn]
      rw [hd]
      simp only [starHeight]
      omega
  | compl r => by
    simpa [deriv] using starHeight_deriv a r
  | star r => by
    have hr := starHeight_deriv a r
    simp only [deriv, starHeight]
    omega

/-! ## Iterated (word-level) derivative -/

/-- Iterated derivative along a word, leftmost letter first:
`derivWord u r` denotes `{w | u ++ w ∈ denote r}` (`denote_derivWord`). -/
def derivWord [DecidableEq α] : Word α → GRegex α → GRegex α
  | [], r => r
  | a :: u, r => derivWord u (deriv a r)

@[simp] theorem derivWord_nil [DecidableEq α] (r : GRegex α) :
    derivWord [] r = r := rfl

@[simp] theorem derivWord_cons [DecidableEq α] (a : α) (u : Word α) (r : GRegex α) :
    derivWord (a :: u) r = derivWord u (deriv a r) := rfl

theorem denote_derivWord [DecidableEq α] :
    ∀ (u : Word α) (r : GRegex α), denote (derivWord u r) = {w | u ++ w ∈ denote r}
  | [], r => by
    ext w
    simp [derivWord]
  | a :: u, r => by
    rw [derivWord_cons, denote_derivWord u (deriv a r), denote_deriv a r]
    ext w
    simp

theorem starHeight_derivWord [DecidableEq α] :
    ∀ (u : Word α) (r : GRegex α), starHeight (derivWord u r) ≤ starHeight r
  | [], _ => Nat.le_refl _
  | a :: u, r =>
    Nat.le_trans (starHeight_derivWord u (deriv a r)) (starHeight_deriv a r)

end GRegex

/-! ## Semantic corollaries: `HasHeightAtMost` is closed under left quotients -/

theorem hasHeightAtMost_deriv [DecidableEq α] {L : Language α} {n : Nat} (a : α)
    (h : HasHeightAtMost L n) : HasHeightAtMost {w | a :: w ∈ L} n := by
  obtain ⟨r, hr, hh⟩ := h
  refine ⟨GRegex.deriv a r, ?_, Nat.le_trans (GRegex.starHeight_deriv a r) hh⟩
  rw [GRegex.denote_deriv, hr]

theorem hasHeightAtMost_derivWord [DecidableEq α] {L : Language α} {n : Nat} (u : Word α)
    (h : HasHeightAtMost L n) : HasHeightAtMost {w | u ++ w ∈ L} n := by
  obtain ⟨r, hr, hh⟩ := h
  refine ⟨GRegex.derivWord u r, ?_, Nat.le_trans (GRegex.starHeight_derivWord u r) hh⟩
  rw [GRegex.denote_derivWord, hr]

end GSH
