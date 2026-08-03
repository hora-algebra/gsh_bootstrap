import GSH.Height.FullAlphabet

/-!
# Reversal closure

Reversing every word in a language preserves generalized star height.  On
expressions, reversal fixes atoms, Boolean operations, and star, and reverses
the order of concatenation.

This is an elementary structural theorem.  It is separated from the
full-alphabet reduction because the all-element `A4` construction consumes it
directly.
-/

set_option autoImplicit false

namespace GSH

universe u

namespace Language

variable {α : Type u}

/-- Word reversal applied pointwise to a language. -/
def reverse (L : Language α) : Language α :=
  {word | word.reverse ∈ L}

@[simp] theorem mem_reverse_iff (L : Language α) (word : Word α) :
    word ∈ reverse L ↔ word.reverse ∈ L := by
  rfl

@[simp] theorem reverse_reverse (L : Language α) :
    reverse (reverse L) = L := by
  ext word
  simp [reverse]

theorem reverse_concat (L K : Language α) :
    reverse (concat L K) = concat (reverse K) (reverse L) := by
  ext word
  constructor
  · rintro ⟨left, hleft, right, hright, hsplit⟩
    refine ⟨right.reverse, ?_, left.reverse, ?_, ?_⟩
    · simpa [reverse] using hright
    · simpa [reverse] using hleft
    · simpa using congrArg List.reverse hsplit
  · rintro ⟨right, hright, left, hleft, hsplit⟩
    refine ⟨left.reverse, ?_, right.reverse, ?_, ?_⟩
    · simpa [reverse] using hleft
    · simpa [reverse] using hright
    · simpa using congrArg List.reverse hsplit

theorem reverse_power (L : Language α) (n : Nat) :
    reverse (power L n) = power (reverse L) n := by
  induction n with
  | zero =>
      ext word
      simp [reverse, power, epsilon]
  | succ n ih =>
      rw [power_succ, reverse_concat, ih, power_succ_left]

theorem reverse_star (L : Language α) :
    reverse (star L) = star (reverse L) := by
  ext word
  simp only [mem_reverse_iff, mem_star_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hmem : word ∈ reverse (power L n) := hn
    rw [reverse_power] at hmem
    exact hmem
  · rintro ⟨n, hn⟩
    have hmem : word ∈ reverse (power L n) := by
      rw [reverse_power]
      exact hn
    exact ⟨n, hmem⟩

end Language

namespace GRegex

variable {α : Type u}

/-- Reverse a generalized expression, swapping the operands of every
concatenation node. -/
def reverse : GRegex α → GRegex α
  | zero => zero
  | epsilon => epsilon
  | atom a => atom a
  | union r s => union (reverse r) (reverse s)
  | concat r s => concat (reverse s) (reverse r)
  | compl r => compl (reverse r)
  | star r => star (reverse r)

theorem denote_reverse (r : GRegex α) :
    denote (reverse r) = Language.reverse (denote r) := by
  induction r with
  | zero =>
      ext word
      simp [reverse, denote, Language.reverse, Language.empty]
  | epsilon =>
      ext word
      simp [reverse, denote, Language.reverse, Language.epsilon]
  | atom a =>
      ext word
      simp [reverse, denote, Language.reverse, Language.letter]
  | union r s ihr ihs =>
      ext word
      simp [reverse, denote, Language.reverse, ihr, ihs]
  | concat r s ihr ihs =>
      simp only [reverse, denote, ihr, ihs]
      exact (Language.reverse_concat (denote r) (denote s)).symm
  | compl r ihr =>
      ext word
      simp [reverse, denote, Language.reverse, Language.compl, ihr]
  | star r ihr =>
      simp only [reverse, denote, ihr]
      exact (Language.reverse_star (denote r)).symm

@[simp] theorem starHeight_reverse (r : GRegex α) :
    starHeight (reverse r) = starHeight r := by
  induction r with
  | zero => rfl
  | epsilon => rfl
  | atom _ => rfl
  | union r s ihr ihs => simp [reverse, starHeight, ihr, ihs]
  | concat r s ihr ihs => simp [reverse, starHeight, ihr, ihs, max_comm]
  | compl r ihr => simp [reverse, starHeight, ihr]
  | star r ihr => simp [reverse, starHeight, ihr]

end GRegex

namespace HasHeightAtMost

variable {α : Type u}

/-- Reversing every word of a language preserves its generalized
star-height bound. -/
theorem reverse {L : Language α} {n : Nat} (hL : HasHeightAtMost L n) :
    HasHeightAtMost (Language.reverse L) n := by
  obtain ⟨r, hr, hh⟩ := hL
  exact ⟨GRegex.reverse r,
    (GRegex.denote_reverse r).trans (congrArg Language.reverse hr),
    by simpa using hh⟩

end HasHeightAtMost

end GSH
