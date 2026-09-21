import GSH.Regex.Sugar
import GSH.Height.Reversal

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
reversal.  The syntactic reversal of expressions and the theorem itself are in
`GSH/Height/Reversal.lean`; what remains here is the `reverseLang` spelling
used by the A₄ development. -/

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

/-- `reverseLang` is the spelling used throughout the A₄ development; it is
definitionally `Language.reverse` of `GSH/Height/Reversal.lean`. -/
theorem reverseLang_eq (L : Language α) : reverseLang L = Language.reverse L := rfl

/-- `HasHeightAtMost` is closed under reversal at every height.  The syntactic
reversal of expressions lives in `GSH/Height/Reversal.lean`; this is only the
restatement in the `reverseLang` spelling. -/
theorem hasHeightAtMost_reverse {L : Language α} {n : Nat}
    (h : HasHeightAtMost L n) : HasHeightAtMost (reverseLang L) n :=
  HasHeightAtMost.reverse h

end GSH
