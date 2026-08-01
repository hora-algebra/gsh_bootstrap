import GSH.Height.S3ArrowAssembly
import GSH.Height.TransferSemantics

/-!
# The completed `S₃` self-loop transfer

This file instantiates the modulus-three PST transfer semantics with the
concrete return code `{[label]} ∪ P`.  It closes the even-final self-loop
branch for both source states and every residue.
-/

set_option autoImplicit false

namespace GSH

private theorem selfLoopCodeBlock_iff (label : S3Alphabet)
    (word : Word S3Alphabet) :
    word ∈ Language.letter label ∪
        {word | S3ArrowResidue.SelfLoopReturnBlock s3Phase label word} ↔
      S3ArrowResidue.SelfLoopCodeBlock s3Phase label word := by
  rfl

/-- The even-final, source-zero, zero-residue self-loop language is exactly
the modulus-three Transfer formula. -/
theorem s3SelfLoopEven_zero_eq_formula (label : S3Alphabet)
    (hlabel : s3Phase label = 0) :
    S3SelfLoopQuotients.evenResidue label 0 =
      TransferCore.formula (Language.letter label)
        {word | S3ArrowResidue.SelfLoopReturnBlock s3Phase label word} 3 := by
  let returns : Language S3Alphabet :=
    {word | S3ArrowResidue.SelfLoopReturnBlock s3Phase label word}
  have hdisjoint : ∀ word ∈ returns, word ≠ [label] := by
    intro word hword
    exact S3ArrowResidue.selfLoopReturnBlock_ne_singleton
      s3Phase label word hlabel hword
  have hUnique : ∀ left right : List (Word S3Alphabet),
      TransferSemantics.Factorizes
          (Language.letter label ∪ returns) left left.flatten →
      TransferSemantics.Factorizes
          (Language.letter label ∪ returns) right right.flatten →
      left.flatten = right.flatten → left = right := by
    intro left right hleft hright hflat
    apply S3ArrowResidue.codeBlockFactorization_unique
      s3Phase label left right hlabel
    · intro piece hpiece
      exact (selfLoopCodeBlock_iff label piece).mp
        (hleft.1 piece hpiece)
    · intro piece hpiece
      exact (selfLoopCodeBlock_iff label piece).mp
        (hright.1 piece hpiece)
    · exact hflat
  ext word
  rw [TransferSemantics.mem_formula_letter_three_iff
    returns label hdisjoint hUnique word]
  change
    ((word.map s3Phase).sum = 0 ∧
        s3ArrowCountFrom 0 0 label word % 3 = 0) ↔
      ∃ pieces : List (Word S3Alphabet),
        TransferSemantics.Factorizes
          (Language.letter label ∪ returns) pieces word ∧
          pieces.count [label] % 3 = 0
  constructor
  · rintro ⟨hphase, hcount⟩
    have hrun :
        ArrowCounting.runFrom (ArrowCounting.c2Step s3Phase) 0 word = 0 := by
      have hr := ArrowCounting.c2RunFrom_eq s3Phase 0 word
      rw [hphase] at hr
      simpa [ArrowCounting.c2RunFrom] using hr
    obtain ⟨pieces, hpieces, hflat⟩ :=
      S3ArrowResidue.exists_codeBlockFactorization
        s3Phase label word hlabel hrun
    refine ⟨pieces, ⟨?_, hflat⟩, ?_⟩
    · intro piece hpiece
      exact (selfLoopCodeBlock_iff label piece).mpr
        (hpieces piece hpiece)
    · have hc := S3ArrowResidue.count_join_codeBlocks
        s3Phase label pieces hlabel hpieces
      rw [hflat] at hc
      rw [← hc]
      exact hcount
  · rintro ⟨pieces, hpieces, hcount⟩
    have hcode : ∀ piece ∈ pieces,
        S3ArrowResidue.SelfLoopCodeBlock s3Phase label piece := by
      intro piece hpiece
      exact (selfLoopCodeBlock_iff label piece).mp
        (hpieces.1 piece hpiece)
    have hrun := S3ArrowResidue.run_join_codeBlocks
      s3Phase label pieces hlabel hcode
    have hrun' : ArrowCounting.c2RunFrom s3Phase 0 word = 0 := by
      simpa [ArrowCounting.c2RunFrom, hpieces.2] using hrun
    rw [ArrowCounting.c2RunFrom_eq] at hrun'
    have hphase : (word.map s3Phase).sum = 0 := by simpa using hrun'
    have hc := S3ArrowResidue.count_join_codeBlocks
      s3Phase label pieces hlabel hcode
    rw [hpieces.2] at hc
    refine ⟨hphase, ?_⟩
    simpa [s3ArrowCountFrom, hc] using hcount

/-- The first load-bearing height theorem: the even-final source-zero
zero-residue self-loop language has generalized star height at most one. -/
theorem hasHeightAtMost_s3SelfLoopEven_zero (label : S3Alphabet)
    (hlabel : s3Phase label = 0) :
    HasHeightAtMost (S3SelfLoopQuotients.evenResidue label 0) 1 := by
  have hformula := TransferCore.hasHeightAtMost_formula
    (Language.letter label)
    {word | S3ArrowResidue.SelfLoopReturnBlock s3Phase label word}
    3 (isStarFree_s3Letter label)
      (isStarFree_s3SelfLoopReturnBlock label)
      (isStarFree_s3LetterStar label)
  exact hformula.congr (s3SelfLoopEven_zero_eq_formula label hlabel).symm

/-- All even-final self-loop residues, for either source state. -/
theorem hasHeightAtMost_s3SelfLoopEven (label : S3Alphabet)
    (hlabel : s3Phase label = 0) (source : ZMod 2)
    (residue : Fin 3) :
    HasHeightAtMost
      {word : Word S3Alphabet |
        (word.map s3Phase).sum = 0 ∧
          s3ArrowCountFrom 0 source label word % 3 = residue.1} 1 := by
  have hzero := hasHeightAtMost_s3SelfLoopEven_zero label hlabel
  have hsource : source = 0 ∨ source = 1 := by
    revert source
    decide
  rcases hsource with rfl | rfl
  · exact S3SelfLoopQuotients.hasHeightAtMost_evenResidue_of_zero
      label hlabel hzero residue
  · exact hasHeightAtMost_s3SelfLoopEvenSourceOne_of_zero
      label hlabel hzero residue

/-- A fixed phase-one letter used to turn odd-final words into even-final
words by prefixing. -/
def s3OddPrefix : S3Alphabet := Equiv.swap (0 : Fin 3) 1

@[simp]
theorem s3Phase_s3OddPrefix : s3Phase s3OddPrefix = 1 := by
  decide

/-- Odd-final words with a fixed self-loop arrow residue. -/
def s3SelfLoopOddResidue (source : ZMod 2) (label : S3Alphabet)
    (residue : Nat) : Language S3Alphabet :=
  {word | (word.map s3Phase).sum = 1 ∧
    s3ArrowCountFrom 0 source label word % 3 = residue}

/-- Prefixing `s3OddPrefix` swaps the source state and converts odd final
phase to even final phase without reading the phase-zero counted label. -/
theorem leftQuotient_s3SelfLoopEven_eq_odd (label : S3Alphabet)
    (hlabel : s3Phase label = 0) (source : ZMod 2)
    (residue : Nat) :
    Language.leftQuotient s3OddPrefix
        {word : Word S3Alphabet |
          (word.map s3Phase).sum = 0 ∧
            s3ArrowCountFrom 0 (source + 1) label word % 3 = residue} =
      s3SelfLoopOddResidue source label residue := by
  have hprefixNe : s3OddPrefix ≠ label := by
    intro h
    have := hlabel
    rw [← h, s3Phase_s3OddPrefix] at this
    exact one_ne_zero this
  ext word
  simp only [Language.mem_leftQuotient_iff, Set.mem_setOf_eq,
    s3SelfLoopOddResidue, List.map_cons, List.sum_cons,
    s3Phase_s3OddPrefix]
  have hshift := s3ArrowCount_shift 1 0 source label word
  have hshift' : s3ArrowCountFrom 1 (source + 1) label word =
      s3ArrowCountFrom 0 source label word := by
    simpa using hshift
  have hcount :
      s3ArrowCountFrom 0 (source + 1) label (s3OddPrefix :: word) =
        s3ArrowCountFrom 0 source label word := by
    change
      (if 0 = source + 1 ∧ s3OddPrefix = label then 1 else 0) +
          s3ArrowCountFrom 1 (source + 1) label word =
        s3ArrowCountFrom 0 source label word
    simp [hprefixNe, hshift']
  rw [hcount]
  have hphase : ∀ phase : ZMod 2, 1 + phase = 0 ↔ phase = 1 := by
    decide
  rw [hphase]

/-- Every odd-final self-loop residue language has height at most one. -/
theorem hasHeightAtMost_s3SelfLoopOdd (label : S3Alphabet)
    (hlabel : s3Phase label = 0) (source : ZMod 2)
    (residue : Fin 3) :
    HasHeightAtMost (s3SelfLoopOddResidue source label residue.1) 1 := by
  have heven := hasHeightAtMost_s3SelfLoopEven
    label hlabel (source + 1) residue
  exact (heven.leftQuotient s3OddPrefix).congr
    (leftQuotient_s3SelfLoopEven_eq_odd
      label hlabel source residue.1)

/-- Complete self-loop branch: for a phase-zero label, every source-state
arrow residue language over all words has generalized star height at most
one. -/
theorem hasHeightAtMost_s3SelfLoopArrowResidue (label : S3Alphabet)
    (hlabel : s3Phase label = 0) (source : ZMod 2)
    (residue : Fin 3) :
    HasHeightAtMost
      {word : Word S3Alphabet |
        s3ArrowCountFrom 0 source label word % 3 = residue.1} 1 := by
  have heven := hasHeightAtMost_s3SelfLoopEven
    label hlabel source residue
  have hodd := hasHeightAtMost_s3SelfLoopOdd
    label hlabel source residue
  refine (heven.union hodd).congr ?_
  ext word
  simp only [Set.mem_union, Set.mem_setOf_eq, s3SelfLoopOddResidue]
  constructor
  · rintro (⟨-, hcount⟩ | ⟨-, hcount⟩) <;> exact hcount
  · intro hcount
    have phaseCases : ∀ phase : ZMod 2, phase = 0 ∨ phase = 1 := by
      decide
    rcases phaseCases (word.map s3Phase).sum with hphase | hphase
    · exact Or.inl ⟨hphase, hcount⟩
    · exact Or.inr ⟨hphase, hcount⟩

end GSH
