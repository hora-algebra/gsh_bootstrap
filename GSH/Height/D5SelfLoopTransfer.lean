import GSH.Height.D5ArrowCoordinates
import GSH.Height.S3SelfLoopHeight
import GSH.Height.TransferModulusSemantics

/-!
# The phase-zero `D₅` self-loop transfer modulo five

The counted codeword is the singleton phase-zero label.  The uncounted return
blocks are exactly `D ∪ C B* C`; the generic code-factorization lemmas are
instantiated at the `D₅` phase map without changing their quantifiers.
-/

set_option autoImplicit false

namespace GSH

namespace D5SelfLoopTransfer

open TransferSemantics

/-- Phase-zero words with a fixed source-zero self-loop arrow residue. -/
def d5SelfLoopEvenResidue (label : D5Alphabet) (residue : Fin 5) :
    Language D5Alphabet :=
  {word | (word.map d5Phase).sum = 0 ∧
    d5ArrowCountFrom 0 0 label word % 5 = residue.1}

private theorem selfLoopCodeBlock_iff (label : D5Alphabet)
    (word : Word D5Alphabet) :
    word ∈ Language.letter label ∪
        {word | S3ArrowResidue.SelfLoopReturnBlock d5Phase label word} ↔
      S3ArrowResidue.SelfLoopCodeBlock d5Phase label word := by
  rfl

private noncomputable def labelStarR (label : D5Alphabet) :
    GRegex D5Alphabet :=
  FiniteAlphabet.onlyWhere fun a => a = label

private noncomputable def neutralOtherR (label : D5Alphabet) :
    GRegex D5Alphabet :=
  FiniteAlphabet.atomWhere fun a => d5Phase a = 0 ∧ a ≠ label

private noncomputable def flipR : GRegex D5Alphabet :=
  FiniteAlphabet.atomWhere fun a => d5Phase a = 1

private noncomputable def neutralWordsR : GRegex D5Alphabet :=
  FiniteAlphabet.onlyWhere fun a => d5Phase a = 0

private noncomputable def returnBlockR (label : D5Alphabet) :
    GRegex D5Alphabet :=
  GRegex.union (neutralOtherR label)
    (GRegex.concat (GRegex.concat flipR neutralWordsR) flipR)

private theorem denote_labelStarR (label : D5Alphabet) :
    GRegex.denote (labelStarR label) =
      Language.star (Language.letter label) := by
  ext word
  change word ∈ GRegex.denote
    (FiniteAlphabet.onlyWhere fun a => a = label) ↔ _
  rw [FiniteAlphabet.mem_denote_onlyWhere_iff,
    Language.mem_star_letter_iff]

private theorem denote_returnBlockR (label : D5Alphabet) :
    GRegex.denote (returnBlockR label) =
      {word | S3ArrowResidue.SelfLoopReturnBlock d5Phase label word} := by
  classical
  ext word
  simp only [returnBlockR, neutralOtherR, flipR, neutralWordsR,
    GRegex.denote, Set.mem_union,
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
        (by simpa [S3ArrowResidue.IsPhaseZeroWord] using hmiddle),
        hc₂, by simp⟩
  · rintro (⟨d, hd, hdl, rfl⟩ |
        ⟨c₁, middle, c₂, hc₁, hmiddle, hc₂, rfl⟩)
    · exact Or.inl ⟨d, ⟨hd, hdl⟩, rfl⟩
    · exact Or.inr ⟨[c₁] ++ middle,
        ⟨[c₁], ⟨c₁, hc₁, rfl⟩, middle,
          (by simpa [S3ArrowResidue.IsPhaseZeroWord] using hmiddle), rfl⟩,
        [c₂], ⟨c₂, hc₂, rfl⟩, by simp⟩

private theorem isStarFree_d5Letter (label : D5Alphabet) :
    IsStarFree (Language.letter label) :=
  ⟨GRegex.atom label, rfl, by simp⟩

private theorem isStarFree_d5LetterStar (label : D5Alphabet) :
    IsStarFree (Language.star (Language.letter label)) :=
  ⟨labelStarR label, denote_labelStarR label, by simp [labelStarR]⟩

private theorem isStarFree_d5SelfLoopReturnBlock (label : D5Alphabet) :
    IsStarFree
      {word | S3ArrowResidue.SelfLoopReturnBlock d5Phase label word} :=
  ⟨returnBlockR label, denote_returnBlockR label,
    by simp [returnBlockR, neutralOtherR, flipR, neutralWordsR,
      GRegex.starHeight]⟩

/-- Exact zero-residue semantics of the concrete phase-zero `D₅`
self-loop code. -/
theorem d5SelfLoopEven_zero_eq_formula (label : D5Alphabet)
    (hlabel : d5Phase label = 0) :
    d5SelfLoopEvenResidue label 0 =
      TransferCore.formula (Language.letter label)
        {word | S3ArrowResidue.SelfLoopReturnBlock d5Phase label word} 5 := by
  let returns : Language D5Alphabet :=
    {word | S3ArrowResidue.SelfLoopReturnBlock d5Phase label word}
  have hdisjoint : ∀ word ∈ returns, word ≠ [label] := by
    intro word hword
    exact S3ArrowResidue.selfLoopReturnBlock_ne_singleton
      d5Phase label word hlabel hword
  have hUnique : ∀ left right : List (Word D5Alphabet),
      Factorizes (Language.letter label ∪ returns) left left.flatten →
      Factorizes (Language.letter label ∪ returns) right right.flatten →
      left.flatten = right.flatten → left = right := by
    intro left right hleft hright hflat
    apply S3ArrowResidue.codeBlockFactorization_unique
      d5Phase label left right hlabel
    · intro piece hpiece
      exact (selfLoopCodeBlock_iff label piece).mp (hleft.1 piece hpiece)
    · intro piece hpiece
      exact (selfLoopCodeBlock_iff label piece).mp (hright.1 piece hpiece)
    · exact hflat
  ext word
  rw [mem_formula_letter_iff returns label 5 (by omega)
    hdisjoint hUnique word]
  change
    ((word.map d5Phase).sum = 0 ∧
        d5ArrowCountFrom 0 0 label word % 5 = 0) ↔
      ∃ pieces : List (Word D5Alphabet),
        Factorizes (Language.letter label ∪ returns) pieces word ∧
          pieces.count [label] % 5 = 0
  constructor
  · rintro ⟨hphase, hcount⟩
    have hrun : ArrowCounting.runFrom
        (ArrowCounting.c2Step d5Phase) 0 word = 0 := by
      have hr := ArrowCounting.c2RunFrom_eq d5Phase 0 word
      rw [hphase] at hr
      simpa [ArrowCounting.c2RunFrom] using hr
    obtain ⟨pieces, hpieces, hflat⟩ :=
      S3ArrowResidue.exists_codeBlockFactorization
        d5Phase label word hlabel hrun
    refine ⟨pieces, ⟨?_, hflat⟩, ?_⟩
    · intro piece hpiece
      exact (selfLoopCodeBlock_iff label piece).mpr
        (hpieces piece hpiece)
    · have hc := S3ArrowResidue.count_join_codeBlocks
        d5Phase label pieces hlabel hpieces
      rw [hflat] at hc
      rw [← hc]
      exact hcount
  · rintro ⟨pieces, hpieces, hcount⟩
    have hcode : ∀ piece ∈ pieces,
        S3ArrowResidue.SelfLoopCodeBlock d5Phase label piece := by
      intro piece hpiece
      exact (selfLoopCodeBlock_iff label piece).mp
        (hpieces.1 piece hpiece)
    have hrun := S3ArrowResidue.run_join_codeBlocks
      d5Phase label pieces hlabel hcode
    have hrun' : ArrowCounting.c2RunFrom d5Phase 0 word = 0 := by
      simpa [ArrowCounting.c2RunFrom, hpieces.2] using hrun
    rw [ArrowCounting.c2RunFrom_eq] at hrun'
    have hphase : (word.map d5Phase).sum = 0 := by simpa using hrun'
    have hc := S3ArrowResidue.count_join_codeBlocks
      d5Phase label pieces hlabel hcode
    rw [hpieces.2] at hc
    refine ⟨hphase, ?_⟩
    simpa [d5ArrowCountFrom, hc] using hcount

private theorem hasHeightAtMost_zero (label : D5Alphabet)
    (hlabel : d5Phase label = 0) :
    HasHeightAtMost (d5SelfLoopEvenResidue label 0) 1 := by
  have hformula := TransferCore.hasHeightAtMost_formula
    (Language.letter label)
    {word | S3ArrowResidue.SelfLoopReturnBlock d5Phase label word}
    5 (isStarFree_d5Letter label)
      (isStarFree_d5SelfLoopReturnBlock label)
      (isStarFree_d5LetterStar label)
  exact hformula.congr (d5SelfLoopEven_zero_eq_formula label hlabel).symm

private theorem add_one_mod_five_eq_iff (n residue : Nat)
    (hresidue : residue < 5) :
    (1 + n) % 5 = residue ↔ n % 5 = (residue + 4) % 5 := by
  rw [Nat.add_mod]
  have hn := Nat.mod_lt n (by omega : 0 < 5)
  omega

private theorem leftQuotient_eq_pred (label : D5Alphabet)
    (hlabel : d5Phase label = 0) (residue : Fin 5) :
    Language.leftQuotient label
        (d5SelfLoopEvenResidue label residue) =
      d5SelfLoopEvenResidue label
        ⟨(residue.1 + 4) % 5, Nat.mod_lt _ (by omega)⟩ := by
  ext word
  simp only [Language.mem_leftQuotient_iff, d5SelfLoopEvenResidue,
    Set.mem_setOf_eq, List.map_cons, List.sum_cons, hlabel, zero_add]
  rw [show d5ArrowCountFrom 0 0 label (label :: word) =
      1 + d5ArrowCountFrom 0 0 label word by
    simp [d5ArrowCountFrom, ArrowCounting.c2Step, hlabel]]
  rw [add_one_mod_five_eq_iff _ residue.1 residue.isLt]

/-- Every phase-zero source-zero self-loop residue modulo five has height at
most one. -/
theorem hasHeightAtMost_d5SelfLoopEvenSourceZero (label : D5Alphabet)
    (hlabel : d5Phase label = 0) (residue : Fin 5) :
    HasHeightAtMost (d5SelfLoopEvenResidue label residue) 1 := by
  have h0 := hasHeightAtMost_zero label hlabel
  have h4 : HasHeightAtMost (d5SelfLoopEvenResidue label 4) 1 :=
    (h0.leftQuotient label).congr
      (by simpa using leftQuotient_eq_pred label hlabel ⟨0, by omega⟩)
  have h3 : HasHeightAtMost (d5SelfLoopEvenResidue label 3) 1 :=
    (h4.leftQuotient label).congr
      (by simpa using leftQuotient_eq_pred label hlabel ⟨4, by omega⟩)
  have h2 : HasHeightAtMost (d5SelfLoopEvenResidue label 2) 1 :=
    (h3.leftQuotient label).congr
      (by simpa using leftQuotient_eq_pred label hlabel ⟨3, by omega⟩)
  have h1 : HasHeightAtMost (d5SelfLoopEvenResidue label 1) 1 :=
    (h2.leftQuotient label).congr
      (by simpa using leftQuotient_eq_pred label hlabel ⟨2, by omega⟩)
  rcases residue with ⟨residue, hresidue⟩
  interval_cases residue <;> assumption

end D5SelfLoopTransfer

end GSH
