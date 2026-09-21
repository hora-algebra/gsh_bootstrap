import GSH.Regex.CountHeight
import Mathlib.Data.Fintype.Basic

/-!
# Inverse alphabetic morphisms preserve generalized star height

A *letter-to-letter* (alphabetic) morphism is induced by a map `σ : α → β`
on the alphabets, acting on words as `List.map σ`.  Its inverse image

    Language.comap σ L = { w | w.map σ ∈ L }

preserves generalized star height exactly: an expression for `L` is pulled
back constructor by constructor, replacing each `atom b` by the finite union
of the atoms of `σ⁻¹(b)`.  Because `σ` is length preserving, the pullback
commutes with concatenation and star as well as with the Boolean
constructors, and no star is added.

This is the easy half of the closure package `PST-CL-01` (Pin–Straubing–
Thérien) and the closure that turns the full-alphabet `A₄` theorem into a
statement about *every* morphism into `A₄` (`N-A4-ANYGEN-001`).

`GRegex.pullback` takes an explicit list `all` enumerating the source
alphabet, so the construction stays computable; the `Fintype` form
`hasHeightAtMost_comap` obtains such a list inside the proof.

This file contains no `sorry` and no `axiom`.
-/

set_option autoImplicit false

namespace GSH

universe u v

variable {α : Type u} {β : Type v}

/-- Inverse image of a language along a letter-to-letter map. -/
def Language.comap (σ : α → β) (L : Language β) : Language α :=
  {w : Word α | w.map σ ∈ L}

@[simp] theorem Language.mem_comap_iff (σ : α → β) (L : Language β) (w : Word α) :
    w ∈ Language.comap σ L ↔ w.map σ ∈ L := Iff.rfl

theorem Language.comap_concat (σ : α → β) (L K : Language β) :
    Language.comap σ (Language.concat L K)
      = Language.concat (Language.comap σ L) (Language.comap σ K) := by
  ext w
  simp only [Language.mem_comap_iff, Language.mem_concat_iff]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    have hlen : x.length ≤ w.length := by
      have hl : (w.map σ).length = x.length + y.length := by
        rw [← hxy]; simp
      simp only [List.length_map] at hl
      omega
    have hsplit : (w.take x.length).map σ ++ (w.drop x.length).map σ = x ++ y := by
      rw [← List.map_append, List.take_append_drop]; exact hxy.symm
    have hlen' : ((w.take x.length).map σ).length = x.length := by
      simp only [List.length_map, List.length_take]; omega
    obtain ⟨h1, h2⟩ := List.append_inj hsplit hlen'
    exact ⟨w.take x.length, by rw [h1]; exact hx,
      w.drop x.length, by rw [h2]; exact hy, by simp⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨u.map σ, hu, v.map σ, hv, by simp⟩

theorem Language.comap_power (σ : α → β) (L : Language β) :
    ∀ n : Nat,
      Language.comap σ (Language.power L n) = Language.power (Language.comap σ L) n
  | 0 => by
    ext w
    simp only [Language.power_zero, Language.mem_comap_iff, Language.mem_epsilon_iff]
    constructor
    · intro h; simpa using congrArg List.length h
    · rintro rfl; rfl
  | n + 1 => by
    rw [Language.power_succ, Language.power_succ, Language.comap_concat,
      Language.comap_power σ L n]

theorem Language.comap_star (σ : α → β) (L : Language β) :
    Language.comap σ (Language.star L) = Language.star (Language.comap σ L) := by
  ext w
  simp only [Language.mem_comap_iff, Language.mem_star_iff]
  exact exists_congr fun n => by
    rw [← Language.mem_comap_iff σ (Language.power L n) w, Language.comap_power]

namespace GRegex

/-- The letters of `all` that `σ` sends to `b`. -/
def preimageList [DecidableEq β] (σ : α → β) (all : List α) (b : β) : List α :=
  all.filter (fun a => decide (σ a = b))

theorem mem_preimageList [DecidableEq β] (σ : α → β) (all : List α) (b : β) (a : α) :
    a ∈ preimageList σ all b ↔ a ∈ all ∧ σ a = b := by
  simp [preimageList]

/-- Pullback of an expression along a letter-to-letter map. -/
def pullback [DecidableEq β] (σ : α → β) (all : List α) : GRegex β → GRegex α
  | zero => zero
  | epsilon => epsilon
  | atom b => CountHeight.atomsOf (preimageList σ all b)
  | union r s => union (pullback σ all r) (pullback σ all s)
  | concat r s => concat (pullback σ all r) (pullback σ all s)
  | compl r => compl (pullback σ all r)
  | star r => star (pullback σ all r)

theorem denote_pullback [DecidableEq α] [DecidableEq β] (σ : α → β) {all : List α}
    (hall : ∀ a : α, a ∈ all) :
    ∀ r : GRegex β, denote (pullback σ all r) = Language.comap σ (denote r)
  | zero => by
    ext w; simp [pullback, denote, Language.empty, Language.comap]
  | epsilon => by
    ext w
    simp only [pullback, denote, Language.mem_epsilon_iff, Language.mem_comap_iff]
    constructor
    · rintro rfl; rfl
    · intro h; simpa using congrArg List.length h
  | atom b => by
    ext w
    rw [pullback, CountHeight.denote_atomsOf]
    simp only [Set.mem_setOf_eq, Language.mem_comap_iff, denote,
      Language.mem_letter_iff, mem_preimageList]
    constructor
    · rintro ⟨a, ha, rfl⟩; simp [ha.2]
    · intro h
      match w with
      | [] => simp at h
      | [a] => exact ⟨a, ⟨hall a, by simpa using h⟩, rfl⟩
      | _ :: _ :: _ => simp at h
  | union r s => by
    ext w
    simp [pullback, denote, denote_pullback σ hall r, denote_pullback σ hall s,
      Language.comap]
  | concat r s => by
    rw [pullback, show denote (concat (pullback σ all r) (pullback σ all s))
        = Language.concat (denote (pullback σ all r)) (denote (pullback σ all s)) from rfl,
      denote_pullback σ hall r, denote_pullback σ hall s, ← Language.comap_concat]
    rfl
  | compl r => by
    ext w
    simp [pullback, denote, Language.compl, denote_pullback σ hall r, Language.comap]
  | star r => by
    rw [pullback, show denote (star (pullback σ all r))
        = Language.star (denote (pullback σ all r)) from rfl,
      denote_pullback σ hall r, ← Language.comap_star]
    rfl

theorem starHeight_pullback [DecidableEq α] [DecidableEq β] (σ : α → β) (all : List α) :
    ∀ r : GRegex β, starHeight (pullback σ all r) = starHeight r
  | zero | epsilon => rfl
  | atom b => by
    rw [pullback]
    exact CountHeight.starHeight_atomsOf _
  | union r s => by
    simp [pullback, starHeight, starHeight_pullback σ all r, starHeight_pullback σ all s]
  | concat r s => by
    simp [pullback, starHeight, starHeight_pullback σ all r, starHeight_pullback σ all s]
  | compl r => by
    simp [pullback, starHeight, starHeight_pullback σ all r]
  | star r => by
    simp [pullback, starHeight, starHeight_pullback σ all r]

end GRegex

/-- **Inverse alphabetic morphisms preserve generalized star height**
(list form). -/
theorem hasHeightAtMost_comap_of_list [DecidableEq α] [DecidableEq β]
    (σ : α → β) {all : List α} (hall : ∀ a : α, a ∈ all)
    {L : Language β} {n : Nat} (h : HasHeightAtMost L n) :
    HasHeightAtMost (Language.comap σ L) n := by
  obtain ⟨r, hr, hh⟩ := h
  exact ⟨GRegex.pullback σ all r, by rw [GRegex.denote_pullback σ hall, hr],
    by rwa [GRegex.starHeight_pullback]⟩

/-- **Inverse alphabetic morphisms preserve generalized star height**
(finite-alphabet form). -/
theorem hasHeightAtMost_comap [Fintype α] [DecidableEq α] [DecidableEq β]
    (σ : α → β) {L : Language β} {n : Nat} (h : HasHeightAtMost L n) :
    HasHeightAtMost (Language.comap σ L) n :=
  hasHeightAtMost_comap_of_list σ
    (all := (Finset.univ : Finset α).toList) (fun a => by simp) h

end GSH
