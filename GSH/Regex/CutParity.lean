import GSH.Regex.HeightClosure

/-!
# Parity of cut counts is height ≤ 1

Every height-one feature used by the `A₄` programme has the same shape: a
deterministic scan of the word fires an *event* finitely often, the scanner
returns to a fixed reset state after each event, and the feature is the
**parity of the number of events**.  This file proves once and for all that
such a parity language has generalized star height at most one, given
star-free tokens.

The data is packaged as a `CutSystem`:

* `cnt0 w` — number of events when scanning `w` from the initial state;
* `cnt1 w` — number of events when scanning `w` from the reset state;
* `opener` — expression for "the first event happens at the last letter,
  scanning from the initial state";
* `token` — the same, scanning from the reset state.

Two axioms tie them together: appending after an opener/token adds exactly
one event (`opener_append`, `token_append`), and a word with at least one
event has an opener/token prefix (`opener_peel`, `token_peel`).  From this,

    { w | cnt0 w even }
      = ¬(opener·Σ*)  ∪  opener · token · (token·token)* · ¬(token·Σ*)

so the feature has height ≤ 1 as soon as `opener` and `token` are star-free
(`CutSystem.hasHeightAtMost_one`).

The concrete cut features of `GSH/Results/A4CutFeature.lean` are instances:
the token is the first-return language `frToken` and the opener is the
first-arrival language `opener q`.

This file contains no `sorry` and no `axiom`.
-/

set_option autoImplicit false

namespace GSH

universe u

variable {α : Type u}

/-! ## Powers of a language -/

theorem power_add (L : Language α) : ∀ m n : Nat,
    Language.power L (m + n)
      = Language.concat (Language.power L m) (Language.power L n)
  | _, 0 => by
    rw [Nat.add_zero, Language.power_zero, concat_epsilon]
  | m, n + 1 => by
    rw [← Nat.add_assoc, Language.power_succ, Language.power_succ,
      power_add L m n, concat_assoc]

theorem power_two (L : Language α) :
    Language.power L 2 = Language.concat L L := by
  rw [show (2 : Nat) = 1 + 1 from rfl, Language.power_succ, Language.power_succ,
    Language.power_zero, epsilon_concat]

theorem power_concat_self (L : Language α) : ∀ n : Nat,
    Language.power (Language.concat L L) n = Language.power L (2 * n)
  | 0 => rfl
  | n + 1 => by
    rw [Language.power_succ, power_concat_self L n,
      show 2 * (n + 1) = 2 * n + 2 from by omega, power_add L (2 * n) 2, power_two]

/-! ## Cut systems -/

/--
An event counter with a reset state, presented by the two counting functions
and the two "exactly one event, at the last letter" token expressions.
-/
structure CutSystem (α : Type u) where
  /-- number of events scanning from the initial state -/
  cnt0 : Word α → Nat
  /-- number of events scanning from the reset state -/
  cnt1 : Word α → Nat
  /-- first-event token from the initial state -/
  opener : GRegex α
  /-- first-event token from the reset state -/
  token : GRegex α
  /-- an opener contributes exactly one event and resets the scan -/
  opener_append : ∀ u ∈ GRegex.denote opener, ∀ v, cnt0 (u ++ v) = 1 + cnt1 v
  /-- a token contributes exactly one event and resets the scan -/
  token_append : ∀ u ∈ GRegex.denote token, ∀ v, cnt1 (u ++ v) = 1 + cnt1 v
  /-- if the scan from the initial state fires, an opener prefix exists -/
  opener_peel : ∀ w : Word α, 0 < cnt0 w →
    ∃ u v, w = u ++ v ∧ u ∈ GRegex.denote opener
  /-- if the scan from the reset state fires, a token prefix exists -/
  token_peel : ∀ w : Word α, 0 < cnt1 w →
    ∃ u v, w = u ++ v ∧ u ∈ GRegex.denote token

namespace CutSystem

open GRegex

variable (S : CutSystem α)

/-- No event from the reset state iff no token prefix. -/
theorem cnt1_eq_zero_iff (w : Word α) :
    S.cnt1 w = 0 ↔ w ∉ denote (concat S.token univ) := by
  constructor
  · intro h hmem
    obtain ⟨u, hu, v, _, rfl⟩ := hmem
    rw [S.token_append u hu v] at h
    omega
  · intro h
    by_contra hne
    obtain ⟨u, v, rfl, hu⟩ := S.token_peel w (Nat.pos_of_ne_zero hne)
    exact h ⟨u, hu, v, by rw [denote_univ]; exact Set.mem_univ v, rfl⟩

/-- No event from the initial state iff no opener prefix. -/
theorem cnt0_eq_zero_iff (w : Word α) :
    S.cnt0 w = 0 ↔ w ∉ denote (concat S.opener univ) := by
  constructor
  · intro h hmem
    obtain ⟨u, hu, v, _, rfl⟩ := hmem
    rw [S.opener_append u hu v] at h
    omega
  · intro h
    by_contra hne
    obtain ⟨u, v, rfl, hu⟩ := S.opener_peel w (Nat.pos_of_ne_zero hne)
    exact h ⟨u, hu, v, by rw [denote_univ]; exact Set.mem_univ v, rfl⟩

/-- A power of tokens contributes exactly that many events. -/
theorem cnt1_append_of_mem_power : ∀ (n : Nat) (u : Word α),
    u ∈ Language.power (denote S.token) n → ∀ v, S.cnt1 (u ++ v) = n + S.cnt1 v
  | 0, u, h, v => by
    rw [show u = [] from h, List.nil_append, Nat.zero_add]
  | n + 1, u, h, v => by
    rw [Language.power_succ, concat_power_comm] at h
    obtain ⟨t, ht, x, hx, rfl⟩ := h
    have hx' := cnt1_append_of_mem_power n x hx v
    rw [List.append_assoc, S.token_append t ht (x ++ v), hx']
    omega

theorem cnt1_of_mem_power (n : Nat) (u : Word α)
    (h : u ∈ Language.power (denote S.token) n) : S.cnt1 u = n := by
  have := S.cnt1_append_of_mem_power n u h []
  rw [List.append_nil] at this
  rw [this]
  have hnil : S.cnt1 ([] : Word α) = 0 := by
    rcases Nat.eq_zero_or_pos (S.cnt1 []) with h0 | hpos
    · exact h0
    · obtain ⟨x, y, hxy, hx⟩ := S.token_peel [] hpos
      have hx0 : x = [] := (List.append_eq_nil_iff.1 hxy.symm).1
      have hy0 : y = [] := (List.append_eq_nil_iff.1 hxy.symm).2
      have := S.token_append x hx y
      rw [hx0, hy0] at this
      simp only [List.nil_append] at this
      omega
  omega

/-- Factorisation into `cnt1` tokens plus an event-free tail. -/
theorem exists_token_factorization : ∀ (n : Nat) (w : Word α), S.cnt1 w = n →
    ∃ u pref : Word α, u ∈ Language.power (denote S.token) n ∧ w = u ++ pref ∧
      S.cnt1 pref = 0
  | 0, w, h => ⟨[], w, rfl, rfl, h⟩
  | n + 1, w, h => by
    obtain ⟨t, v, rfl, ht⟩ := S.token_peel w (by omega)
    have hv : S.cnt1 v = n := by
      have := S.token_append t ht v
      omega
    obtain ⟨u, pref, hu, hveq, hpref⟩ := exists_token_factorization n v hv
    refine ⟨t ++ u, pref, ?_, by rw [hveq, List.append_assoc], hpref⟩
    rw [Language.power_succ, concat_power_comm]
    exact ⟨t, ht, u, hu, rfl⟩

/-- Even number of events from the reset state. -/
def evenTail : GRegex α :=
  concat (star (concat S.token S.token)) (compl (concat S.token univ))

/-- Odd number of events from the reset state. -/
def oddTail : GRegex α := concat S.token S.evenTail

theorem denote_evenTail : denote S.evenTail = {w : Word α | S.cnt1 w % 2 = 0} := by
  ext w
  constructor
  · rintro ⟨u, ⟨m, hm⟩, pref, hpref, rfl⟩
    have hm' : u ∈ Language.power (denote S.token) (2 * m) := by
      have heq : Language.power (denote (concat S.token S.token)) m
          = Language.power (denote S.token) (2 * m) :=
        power_concat_self (denote S.token) m
      rwa [heq] at hm
    have hz : S.cnt1 pref = 0 := (S.cnt1_eq_zero_iff pref).2 hpref
    have := S.cnt1_append_of_mem_power (2 * m) u hm' pref
    show S.cnt1 (u ++ pref) % 2 = 0
    omega
  · intro hw
    have hev : S.cnt1 w % 2 = 0 := hw
    obtain ⟨u, pref, hu, rfl, hpref⟩ :=
      S.exists_token_factorization (S.cnt1 w) w rfl
    obtain ⟨m, hm⟩ : ∃ m, S.cnt1 (u ++ pref) = 2 * m := ⟨S.cnt1 (u ++ pref) / 2, by omega⟩
    refine ⟨u, ⟨m, ?_⟩, pref, (S.cnt1_eq_zero_iff pref).1 hpref, rfl⟩
    show u ∈ Language.power (Language.concat (denote S.token) (denote S.token)) m
    rw [power_concat_self]
    rw [← hm]
    exact hu

theorem denote_oddTail : denote S.oddTail = {w : Word α | S.cnt1 w % 2 = 1} := by
  ext w
  constructor
  · rintro ⟨t, ht, v, hv, rfl⟩
    have h1 := S.token_append t ht v
    have h2 : S.cnt1 v % 2 = 0 := by rw [S.denote_evenTail] at hv; exact hv
    show S.cnt1 (t ++ v) % 2 = 1
    omega
  · intro hw
    have hodd : S.cnt1 w % 2 = 1 := hw
    obtain ⟨t, v, rfl, ht⟩ := S.token_peel w (by omega)
    have h1 := S.token_append t ht v
    refine ⟨t, ht, v, ?_, rfl⟩
    rw [S.denote_evenTail]
    show S.cnt1 v % 2 = 0
    omega

/-- Even number of events from the initial state. -/
def evenFeature : GRegex α :=
  union (compl (concat S.opener univ)) (concat S.opener S.oddTail)

/-- **Main theorem.**  The parity feature of a cut system is denoted by
`evenFeature`. -/
theorem denote_evenFeature :
    denote S.evenFeature = {w : Word α | S.cnt0 w % 2 = 0} := by
  ext w
  simp only [evenFeature, denote, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (h | h)
    · rw [(S.cnt0_eq_zero_iff w).2 h]
    · obtain ⟨u, hu, v, hv, rfl⟩ := h
      have h1 := S.opener_append u hu v
      have h2 : S.cnt1 v % 2 = 1 := by rw [S.denote_oddTail] at hv; exact hv
      omega
  · intro hev
    rcases Nat.eq_zero_or_pos (S.cnt0 w) with h0 | hpos
    · exact Or.inl ((S.cnt0_eq_zero_iff w).1 h0)
    · right
      obtain ⟨u, v, rfl, hu⟩ := S.opener_peel w hpos
      have h1 := S.opener_append u hu v
      refine ⟨u, hu, v, ?_, rfl⟩
      rw [S.denote_oddTail]
      show S.cnt1 v % 2 = 1
      omega

theorem starHeight_evenTail (ht : starHeight S.token = 0) :
    starHeight S.evenTail ≤ 1 := by
  change max (max (starHeight S.token) (starHeight S.token) + 1)
    (max (starHeight S.token) (starHeight (univ : GRegex α))) ≤ 1
  rw [ht, starHeight_univ]
  decide

theorem starHeight_oddTail (ht : starHeight S.token = 0) :
    starHeight S.oddTail ≤ 1 := by
  change max (starHeight S.token) (starHeight S.evenTail) ≤ 1
  rw [ht]
  exact max_le (by decide) (S.starHeight_evenTail ht)

theorem starHeight_evenFeature (ho : starHeight S.opener = 0)
    (ht : starHeight S.token = 0) : starHeight S.evenFeature ≤ 1 := by
  change max (max (starHeight S.opener) (starHeight (univ : GRegex α)))
    (max (starHeight S.opener) (starHeight S.oddTail)) ≤ 1
  rw [ho, starHeight_univ]
  exact max_le (by decide) (max_le (by decide) (S.starHeight_oddTail ht))

/-- The parity of the event count of a cut system with star-free tokens has
generalized star height at most one. -/
theorem hasHeightAtMost_one (ho : starHeight S.opener = 0)
    (ht : starHeight S.token = 0) :
    HasHeightAtMost {w : Word α | S.cnt0 w % 2 = 0} 1 :=
  ⟨S.evenFeature, S.denote_evenFeature, S.starHeight_evenFeature ho ht⟩

end CutSystem
end GSH
