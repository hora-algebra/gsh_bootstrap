import GSH.Height.Counting
import GSH.Height.C2SelfLoopCode
import GSH.Height.FullAlphabet
import GSH.Height.TransferCore

/-!
# Star-free pieces for the a `C₂`-phase self-loop arrow language

This file supplies the star-free languages used by the self-loop branch of
PST Proposition 6.6.  The alphabet is finite, so "every letter satisfies a
predicate" is expressed without a Kleene star: take the complement of the
words containing one of the finitely many forbidden letters.
-/

set_option autoImplicit false

namespace GSH

universe u

namespace Language

variable {alpha : Type u}

/-- Powers of a singleton letter language are singleton constant words. -/
theorem power_letter (a : alpha) (n : Nat) :
    power (letter a) n = {List.replicate n a} := by
  induction n with
  | zero => ext word; simp [power, epsilon]
  | succ n ih =>
      rw [power, ih]
      ext word
      constructor
      · rintro ⟨left, rfl, right, hright, rfl⟩
        have : right = [a] := hright
        subst right
        simpa using (List.replicate_add n 1 a).symm
      · intro h
        have hw : word = List.replicate (n + 1) a := h
        subst word
        refine ⟨List.replicate n a, rfl, [a], ?_, ?_⟩
        · rfl
        · simpa using (List.replicate_add n 1 a).symm

/-- A word belongs to the star of one letter iff all its letters are that
letter. -/
theorem mem_star_letter_iff (a : alpha) (word : Word alpha) :
    word ∈ star (letter a) ↔ ∀ b ∈ word, b = a := by
  constructor
  · rintro ⟨n, hn⟩
    rw [power_letter] at hn
    have hw : word = List.replicate n a := hn
    subst word
    intro b hb
    exact List.eq_of_mem_replicate hb
  · intro hall
    refine ⟨word.length, ?_⟩
    rw [power_letter]
    exact (List.eq_replicate_length.mpr hall)

end Language

namespace FiniteAlphabet

variable {alpha : Type u} [Fintype alpha]

/-- The finite union of one-letter words satisfying `predicate`. -/
noncomputable def atomWhere (predicate : alpha → Prop) [DecidablePred predicate] :
    GRegex alpha :=
  GRegex.atomUnion ((Finset.univ.filter predicate).toList)

@[simp]
theorem mem_denote_atomWhere_iff (predicate : alpha → Prop)
    [DecidablePred predicate] (word : Word alpha) :
    word ∈ GRegex.denote (atomWhere predicate) ↔
      ∃ a, predicate a ∧ word = [a] := by
  classical
  simp [atomWhere, GRegex.mem_denote_atomUnion_iff]

/-- Words containing at least one letter satisfying `predicate`. -/
noncomputable def containsWhere (predicate : alpha → Prop)
    [DecidablePred predicate] : GRegex alpha :=
  GRegex.concat
    (GRegex.concat Counting.univR (atomWhere predicate)) Counting.univR

@[simp]
theorem mem_denote_containsWhere_iff (predicate : alpha → Prop)
    [DecidablePred predicate] (word : Word alpha) :
    word ∈ GRegex.denote (containsWhere predicate) ↔
      ∃ a ∈ word, predicate a := by
  classical
  rw [containsWhere]
  simp only [GRegex.denote, Language.mem_concat_iff, Counting.denote_univR,
    Set.mem_univ, mem_denote_atomWhere_iff]
  constructor
  · rintro ⟨pre, ⟨left, -, middle, ⟨a, ha, rfl⟩, rfl⟩, suffix, -, rfl⟩
    exact ⟨a, by simp, ha⟩
  · rintro ⟨a, ha, hpredicate⟩
    obtain ⟨pre, suffix, rfl⟩ := List.append_of_mem ha
    exact ⟨pre ++ [a], ⟨pre, by simp, [a],
      ⟨a, hpredicate, rfl⟩, rfl⟩, suffix, by simp, by simp⟩

/-- A height-zero expression for words all of whose letters satisfy
`predicate`. -/
noncomputable def onlyWhere (predicate : alpha → Prop)
    [DecidablePred predicate] : GRegex alpha :=
  GRegex.compl (containsWhere fun a => ¬ predicate a)

@[simp]
theorem mem_denote_onlyWhere_iff (predicate : alpha → Prop)
    [DecidablePred predicate] (word : Word alpha) :
    word ∈ GRegex.denote (onlyWhere predicate) ↔
      ∀ a ∈ word, predicate a := by
  classical
  simp [onlyWhere, GRegex.denote, Language.compl]

@[simp]
theorem starHeight_atomWhere (predicate : alpha → Prop)
    [DecidablePred predicate] :
    GRegex.starHeight (atomWhere predicate) = 0 := by
  classical
  simp [atomWhere]

@[simp]
theorem starHeight_containsWhere (predicate : alpha → Prop)
    [DecidablePred predicate] :
    GRegex.starHeight (containsWhere predicate) = 0 := by
  classical
  simp [containsWhere, Counting.univR, GRegex.starHeight]

@[simp]
theorem starHeight_onlyWhere (predicate : alpha → Prop)
    [DecidablePred predicate] :
    GRegex.starHeight (onlyWhere predicate) = 0 := by
  classical
  simp [onlyWhere]

end FiniteAlphabet

namespace C2SelfLoopHeight

variable {α : Type u} [Fintype α] [DecidableEq α]


/-- A height-zero expression for the one-letter language `{label}`. -/
def labelR (label : α) : GRegex α := GRegex.atom label

/-- A height-zero expression for all constant words over `label`. -/
noncomputable def labelStarR (label : α) : GRegex α :=
  FiniteAlphabet.onlyWhere fun a => a = label

/-- The neutral letters other than the counted label. -/
noncomputable def neutralOtherR (phase : α → ZMod 2) (label : α) : GRegex α :=
  FiniteAlphabet.atomWhere fun a => phase a = 0 ∧ a ≠ label

/-- The phase-flipping one-letter words. -/
noncomputable def flipR (phase : α → ZMod 2) : GRegex α :=
  FiniteAlphabet.atomWhere fun a => phase a = 1

/-- All words made only of phase-zero letters, obtained at height zero by
complementing the occurrence of a phase-one letter. -/
noncomputable def neutralWordsR (phase : α → ZMod 2) : GRegex α :=
  FiniteAlphabet.onlyWhere fun a => phase a = 0

/-- The PST return block `P = D ∪ C B* C`, with `B*` represented at height
zero. -/
noncomputable def returnBlockR (phase : α → ZMod 2) (label : α) : GRegex α :=
  GRegex.union (neutralOtherR phase label)
    (GRegex.concat (GRegex.concat (flipR phase) (neutralWordsR phase)) (flipR phase))

@[simp]
theorem denote_labelR (label : α) :
    GRegex.denote (labelR label) = Language.letter label := rfl

@[simp]
theorem denote_labelStarR (label : α) :
    GRegex.denote (labelStarR label) = Language.star (Language.letter label) := by
  ext word
  change word ∈ GRegex.denote (FiniteAlphabet.onlyWhere fun a => a = label) ↔ _
  rw [FiniteAlphabet.mem_denote_onlyWhere_iff, Language.mem_star_letter_iff]

@[simp]
theorem denote_returnBlockR (phase : α → ZMod 2) (label : α) :
    GRegex.denote (returnBlockR phase label) =
      {word | C2SelfLoopCode.SelfLoopReturnBlock phase label word} := by
  classical
  ext word
  simp only [returnBlockR, neutralOtherR, flipR, neutralWordsR, GRegex.denote,
    Set.mem_union,
    FiniteAlphabet.mem_denote_atomWhere_iff, Language.mem_concat_iff,
    FiniteAlphabet.mem_denote_onlyWhere_iff, Set.mem_setOf_eq]
  constructor
  · rintro (⟨d, ⟨hd, hdl⟩, rfl⟩ |
        ⟨left, ⟨cword₁, hcword₁, middle, hmiddle, rfl⟩,
          cword₂, hcword₂, rfl⟩)
    · exact Or.inl ⟨d, hd, hdl, rfl⟩
    · obtain ⟨c₁, hc₁, rfl⟩ := hcword₁
      obtain ⟨c₂, hc₂, rfl⟩ := hcword₂
      exact Or.inr ⟨c₁, middle, c₂, hc₁,
        (by simpa [C2SelfLoopCode.IsPhaseZeroWord] using hmiddle), hc₂, by simp⟩
  · rintro (⟨d, hd, hdl, rfl⟩ | ⟨c₁, middle, c₂, hc₁, hmiddle, hc₂, rfl⟩)
    · exact Or.inl ⟨d, ⟨hd, hdl⟩, rfl⟩
    · exact Or.inr ⟨[c₁] ++ middle,
        ⟨[c₁], ⟨c₁, hc₁, rfl⟩, middle,
          (by simpa [C2SelfLoopCode.IsPhaseZeroWord] using hmiddle), rfl⟩,
        [c₂], ⟨c₂, hc₂, rfl⟩, by simp⟩

@[simp]
theorem starHeight_labelR (label : α) :
    GRegex.starHeight (labelR label) = 0 := rfl

@[simp]
theorem starHeight_labelStarR (label : α) :
    GRegex.starHeight (labelStarR label) = 0 := by
  simp [labelStarR]

@[simp]
theorem starHeight_returnBlockR (phase : α → ZMod 2) (label : α) :
    GRegex.starHeight (returnBlockR phase label) = 0 := by
  simp [returnBlockR, neutralOtherR, flipR, neutralWordsR, GRegex.starHeight]

end C2SelfLoopHeight

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- A one-letter language is star-free. -/
theorem isStarFree_letter (label : α) :
    IsStarFree (Language.letter label) :=
  ⟨C2SelfLoopHeight.labelR label, C2SelfLoopHeight.denote_labelR label,
    by simp⟩

/-- The star of a singleton letter is star-free in the generalized sense. -/
theorem isStarFree_letterStar (label : α) :
    IsStarFree (Language.star (Language.letter label)) :=
  ⟨C2SelfLoopHeight.labelStarR label,
    C2SelfLoopHeight.denote_labelStarR label, by simp⟩

/-- The concrete two-state return-block language is star-free. -/
theorem isStarFree_selfLoopReturnBlock (phase : α → ZMod 2) (label : α) :
    IsStarFree
      {word | C2SelfLoopCode.SelfLoopReturnBlock phase label word} :=
  ⟨C2SelfLoopHeight.returnBlockR phase label,
    C2SelfLoopHeight.denote_returnBlockR phase label, by simp⟩

end GSH
