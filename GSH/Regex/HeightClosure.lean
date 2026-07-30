import GSH.Regex.Sugar

/-!
# Closure properties of `HasHeightAtMost`

Boolean operations and “star of a star-free language” stay within height ≤ 1.
-/

set_option autoImplicit false

namespace GSH

universe u
variable {α : Type u}

open GRegex

theorem hasHeightAtMost_of_le {L : Language α} {m n : Nat}
    (h : HasHeightAtMost L m) (hle : m ≤ n) : HasHeightAtMost L n := by
  obtain ⟨r, hr, hh⟩ := h
  exact ⟨r, hr, Nat.le_trans hh hle⟩

theorem hasHeightAtMost_univ : HasHeightAtMost (Set.univ : Language α) 0 :=
  ⟨univ, denote_univ, by simp⟩

theorem hasHeightAtMost_empty : HasHeightAtMost (∅ : Language α) 0 :=
  ⟨zero, rfl, by simp [starHeight]⟩

theorem hasHeightAtMost_compl {L : Language α} {n : Nat}
    (h : HasHeightAtMost L n) : HasHeightAtMost Lᶜ n := by
  obtain ⟨r, hr, hh⟩ := h
  refine ⟨compl r, ?_, by simpa [starHeight] using hh⟩
  simp [denote, Language.compl, hr]

theorem hasHeightAtMost_union {L K : Language α} {n : Nat}
    (hL : HasHeightAtMost L n) (hK : HasHeightAtMost K n) :
    HasHeightAtMost (L ∪ K) n := by
  obtain ⟨r, hr, hhr⟩ := hL
  obtain ⟨s, hs, hhs⟩ := hK
  refine ⟨union r s, ?_, ?_⟩
  · simp [denote, hr, hs]
  · exact max_le hhr hhs

theorem hasHeightAtMost_inter {L K : Language α} {n : Nat}
    (hL : HasHeightAtMost L n) (hK : HasHeightAtMost K n) :
    HasHeightAtMost (L ∩ K) n := by
  -- L ∩ K = (Lᶜ ∪ Kᶜ)ᶜ
  simpa using
    hasHeightAtMost_compl
      (hasHeightAtMost_union (hasHeightAtMost_compl hL) (hasHeightAtMost_compl hK))

/-- Star of a height-0 expression has height ≤ 1. -/
theorem hasHeightAtMost_star_of_starFree {L : Language α}
    (h : HasHeightAtMost L 0) : HasHeightAtMost (Language.star L) 1 := by
  obtain ⟨r, hr, hh⟩ := h
  have hz : starHeight r = 0 := Nat.le_zero.mp hh
  refine ⟨star r, ?_, ?_⟩
  · simp [denote, hr]
  · simp [starHeight, hz]

/-- Concatenation does not raise a uniform height bound. -/
theorem hasHeightAtMost_concat {L K : Language α} {n : Nat}
    (hL : HasHeightAtMost L n) (hK : HasHeightAtMost K n) :
    HasHeightAtMost (Language.concat L K) n := by
  obtain ⟨r, hr, hhr⟩ := hL
  obtain ⟨s, hs, hhs⟩ := hK
  refine ⟨concat r s, ?_, ?_⟩
  · simp [denote, hr, hs]
  · exact max_le hhr hhs

/-- Parity of a sum of two word features is a Boolean combination of the
individual parities (GF(2) additivity). -/
theorem hasHeightAtMost_parity_add {f g : Word α → Nat} {n : Nat}
    (hf : HasHeightAtMost {w : Word α | f w % 2 = 0} n)
    (hg : HasHeightAtMost {w : Word α | g w % 2 = 0} n) :
    HasHeightAtMost {w : Word α | (f w + g w) % 2 = 0} n := by
  have hset : {w : Word α | (f w + g w) % 2 = 0} =
      ({w : Word α | f w % 2 = 0} ∩ {w : Word α | g w % 2 = 0}) ∪
        ({w : Word α | f w % 2 = 0}ᶜ ∩ {w : Word α | g w % 2 = 0}ᶜ) := by
    ext w
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq]
    omega
  rw [hset]
  exact hasHeightAtMost_union
    (hasHeightAtMost_inter hf hg)
    (hasHeightAtMost_inter (hasHeightAtMost_compl hf) (hasHeightAtMost_compl hg))

/-! ## Closure under word reversal

`RESULTS.md` §5.5 key 2: generalized star height is invariant under
reversal, because every constructor of `GRegex` commutes with reversal
(concatenation flips its arguments) without touching star nesting. -/

/-- Reversal of a language: `w ∈ reverseLang L ↔ w.reverse ∈ L`. -/
def reverseLang (L : Language α) : Language α := {w | w.reverse ∈ L}

@[simp] theorem mem_reverseLang_iff (L : Language α) (w : Word α) :
    w ∈ reverseLang L ↔ w.reverse ∈ L := Iff.rfl

theorem reverseLang_reverseLang (L : Language α) :
    reverseLang (reverseLang L) = L := by
  ext w
  simp

theorem concat_assoc (L K M : Language α) :
    Language.concat (Language.concat L K) M
      = Language.concat L (Language.concat K M) := by
  ext w
  constructor
  · rintro ⟨uv, ⟨u, hu, v, hv, rfl⟩, m, hm, rfl⟩
    exact ⟨u, hu, v ++ m, ⟨v, hv, m, hm, rfl⟩, by simp⟩
  · rintro ⟨u, hu, vm, ⟨v, hv, m, hm, rfl⟩, rfl⟩
    exact ⟨u ++ v, ⟨u, hu, v, hv, rfl⟩, m, hm, by simp⟩

theorem concat_epsilon (L : Language α) :
    Language.concat L Language.epsilon = L := by
  ext w
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    have : v = [] := hv
    simpa [this] using hu
  · intro hw
    exact ⟨w, hw, [], rfl, by simp⟩

theorem epsilon_concat (L : Language α) :
    Language.concat Language.epsilon L = L := by
  ext w
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    have : u = [] := hu
    simpa [this] using hv
  · intro hw
    exact ⟨[], rfl, w, hw, rfl⟩

/-- The two one-sided products with a power coincide. -/
theorem concat_power_comm (L : Language α) :
    ∀ n : Nat, Language.concat (Language.power L n) L
      = Language.concat L (Language.power L n)
  | 0 => by rw [Language.power_zero, epsilon_concat, concat_epsilon]
  | n + 1 => by
    calc Language.concat (Language.power L (n + 1)) L
        = Language.concat (Language.concat (Language.power L n) L) L := by
          rw [Language.power_succ]
      _ = Language.concat (Language.concat L (Language.power L n)) L := by
          rw [concat_power_comm L n]
      _ = Language.concat L (Language.concat (Language.power L n) L) := by
          rw [concat_assoc]
      _ = Language.concat L (Language.power L (n + 1)) := by
          rw [Language.power_succ]

theorem mem_power_reverse (L : Language α) :
    ∀ (n : Nat) (w : Word α),
      w ∈ Language.power (reverseLang L) n ↔ w.reverse ∈ Language.power L n
  | 0, w => by
    simp only [Language.power_zero, Language.mem_epsilon_iff]
    constructor
    · rintro rfl; rfl
    · intro h
      have := congrArg List.reverse h
      simpa using this
  | n + 1, w => by
    rw [Language.power_succ, Language.power_succ, concat_power_comm L n]
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      refine ⟨v.reverse, hv, u.reverse, (mem_power_reverse L n u).1 hu, by simp⟩
    · rintro ⟨b, hb, a, ha, hba⟩
      refine ⟨a.reverse, ?_, b.reverse, ?_, ?_⟩
      · exact (mem_power_reverse L n a.reverse).2 (by simpa using ha)
      · simpa using hb
      · have := congrArg List.reverse hba
        simpa using this

theorem star_reverseLang (L : Language α) :
    Language.star (reverseLang L) = reverseLang (Language.star L) := by
  ext w
  simp only [Language.mem_star_iff, mem_reverseLang_iff]
  exact exists_congr fun n => mem_power_reverse L n w

namespace GRegex

/-- Syntactic reversal of a generalized expression. -/
def reverse : GRegex α → GRegex α
  | zero => zero
  | epsilon => epsilon
  | atom a => atom a
  | union r s => union (reverse r) (reverse s)
  | concat r s => concat (reverse s) (reverse r)
  | compl r => compl (reverse r)
  | star r => star (reverse r)

theorem starHeight_reverse : ∀ r : GRegex α, starHeight (reverse r) = starHeight r
  | zero | epsilon | atom _ => rfl
  | union r s => by
    simp [reverse, starHeight, starHeight_reverse r, starHeight_reverse s]
  | concat r s => by
    simp [reverse, starHeight, starHeight_reverse r, starHeight_reverse s,
      Nat.max_comm]
  | compl r => by
    simp [reverse, starHeight, starHeight_reverse r]
  | star r => by
    simp [reverse, starHeight, starHeight_reverse r]

theorem denote_reverse : ∀ r : GRegex α, denote (reverse r) = reverseLang (denote r)
  | zero => by
    ext w
    simp [reverse, denote, Language.empty]
  | epsilon => by
    ext w
    simp only [reverse, denote, Language.mem_epsilon_iff, mem_reverseLang_iff]
    constructor
    · rintro rfl; rfl
    · intro h
      have := congrArg List.reverse h
      simpa using this
  | atom a => by
    ext w
    simp only [reverse, denote, Language.mem_letter_iff, mem_reverseLang_iff]
    constructor
    · rintro rfl; rfl
    · intro h
      have := congrArg List.reverse h
      simpa using this
  | union r s => by
    ext w
    simp [reverse, denote, denote_reverse r, denote_reverse s]
  | concat r s => by
    ext w
    simp only [reverse, denote, denote_reverse r, denote_reverse s,
      Language.mem_concat_iff, mem_reverseLang_iff]
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      exact ⟨v.reverse, hv, u.reverse, hu, by simp⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      refine ⟨b.reverse, by simpa using hb, a.reverse, by simpa using ha, ?_⟩
      have := congrArg List.reverse hab
      simpa using this
  | compl r => by
    ext w
    simp [reverse, denote, Language.compl, denote_reverse r]
  | star r => by
    show denote (star (reverse r)) = reverseLang (Language.star (denote r))
    rw [show denote (star (reverse r)) = Language.star (denote (reverse r)) from rfl,
      denote_reverse r, star_reverseLang]

end GRegex

/-- `HasHeightAtMost` is closed under reversal at every height. -/
theorem hasHeightAtMost_reverse {L : Language α} {n : Nat}
    (h : HasHeightAtMost L n) : HasHeightAtMost (reverseLang L) n := by
  obtain ⟨r, hr, hh⟩ := h
  refine ⟨GRegex.reverse r, ?_, ?_⟩
  · rw [GRegex.denote_reverse, hr]
  · rwa [GRegex.starHeight_reverse]

end GSH
