import GSH.Height.C2SelfLoopHeight
import GSH.Height.TransferModulusSemantics

/-!
# Source-zero self-loop residues for a two-state quotient

For a letter of phase zero, words of total phase zero have a unique return-code
factorization into the counted singleton and uncounted return blocks.  The
generic PST transfer formula then gives every residue of the source-zero arrow
count at generalized star height at most one.
-/

set_option autoImplicit false

namespace GSH
namespace C2SelfLoop

universe u

open ArrowCounting

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- The source-zero arrow count for the additive `C₂` run. -/
def arrowCount (phase : α → ZMod 2) (label : α) (word : Word α) : Nat :=
  ArrowCounting.arrowCountFrom (ArrowCounting.c2Step phase) 0 0 label word

/-- Phase-zero words with a prescribed source-zero self-loop residue. -/
def evenResidue (phase : α → ZMod 2) (label : α)
    (modulus residue : Nat) : Language α :=
  {word | (word.map phase).sum = 0 ∧
    arrowCount phase label word % modulus = residue}

private theorem codeBlock_iff (phase : α → ZMod 2) (label : α)
    (word : Word α) :
    word ∈ Language.letter label ∪
        {word | C2SelfLoopCode.SelfLoopReturnBlock phase label word} ↔
      C2SelfLoopCode.SelfLoopCodeBlock phase label word := by
  rfl

/-- The zero-residue language is exactly the generic transfer formula. -/
theorem evenResidue_zero_eq_formula (phase : α → ZMod 2) (label : α)
    (hlabel : phase label = 0) (modulus : Nat) (hmodulus : 0 < modulus) :
    evenResidue phase label modulus 0 =
      TransferCore.formula (Language.letter label)
        {word | C2SelfLoopCode.SelfLoopReturnBlock phase label word} modulus := by
  let returns : Language α :=
    {word | C2SelfLoopCode.SelfLoopReturnBlock phase label word}
  have hdisjoint : ∀ word ∈ returns, word ≠ [label] := by
    intro word hword
    exact C2SelfLoopCode.selfLoopReturnBlock_ne_singleton
      phase label word hlabel hword
  have hUnique : ∀ left right : List (Word α),
      TransferSemantics.Factorizes
          (Language.letter label ∪ returns) left left.flatten →
      TransferSemantics.Factorizes
          (Language.letter label ∪ returns) right right.flatten →
      left.flatten = right.flatten → left = right := by
    intro left right hleft hright hflat
    apply C2SelfLoopCode.codeBlockFactorization_unique
      phase label left right hlabel
    · intro piece hpiece
      exact (codeBlock_iff phase label piece).mp (hleft.1 piece hpiece)
    · intro piece hpiece
      exact (codeBlock_iff phase label piece).mp (hright.1 piece hpiece)
    · exact hflat
  ext word
  rw [TransferSemantics.mem_formula_letter_iff
    returns label modulus hmodulus hdisjoint hUnique word]
  change
    ((word.map phase).sum = 0 ∧
        arrowCount phase label word % modulus = 0) ↔
      ∃ pieces : List (Word α),
        TransferSemantics.Factorizes
          (Language.letter label ∪ returns) pieces word ∧
          pieces.count [label] % modulus = 0
  constructor
  · rintro ⟨hphase, hcount⟩
    have hrun :
        ArrowCounting.runFrom (ArrowCounting.c2Step phase) 0 word = 0 := by
      have hr := ArrowCounting.c2RunFrom_eq phase 0 word
      rw [hphase] at hr
      simpa [ArrowCounting.c2RunFrom] using hr
    obtain ⟨pieces, hpieces, hflat⟩ :=
      C2SelfLoopCode.exists_codeBlockFactorization
        phase label word hlabel hrun
    refine ⟨pieces, ⟨?_, hflat⟩, ?_⟩
    · intro piece hpiece
      exact (codeBlock_iff phase label piece).mpr (hpieces piece hpiece)
    · have hc := C2SelfLoopCode.count_join_codeBlocks
        phase label pieces hlabel hpieces
      rw [hflat] at hc
      rw [← hc]
      exact hcount
  · rintro ⟨pieces, hpieces, hcount⟩
    have hcode : ∀ piece ∈ pieces,
        C2SelfLoopCode.SelfLoopCodeBlock phase label piece := by
      intro piece hpiece
      exact (codeBlock_iff phase label piece).mp (hpieces.1 piece hpiece)
    have hrun := C2SelfLoopCode.run_join_codeBlocks
      phase label pieces hlabel hcode
    have hrun' : ArrowCounting.c2RunFrom phase 0 word = 0 := by
      simpa [ArrowCounting.c2RunFrom, hpieces.2] using hrun
    rw [ArrowCounting.c2RunFrom_eq] at hrun'
    have hphase : (word.map phase).sum = 0 := by simpa using hrun'
    have hc := C2SelfLoopCode.count_join_codeBlocks
      phase label pieces hlabel hcode
    rw [hpieces.2] at hc
    refine ⟨hphase, ?_⟩
    simpa [arrowCount, hc] using hcount

/-- The even-phase zero residue has generalized star height at most one. -/
theorem hasHeightAtMost_evenResidue_zero (phase : α → ZMod 2) (label : α)
    (hlabel : phase label = 0) (modulus : Nat) (hmodulus : 0 < modulus) :
    HasHeightAtMost (evenResidue phase label modulus 0) 1 := by
  have hformula := TransferCore.hasHeightAtMost_formula
    (Language.letter label)
    {word | C2SelfLoopCode.SelfLoopReturnBlock phase label word}
    modulus (isStarFree_letter label)
      (isStarFree_selfLoopReturnBlock phase label)
      (isStarFree_letterStar label)
  exact hformula.congr
    (evenResidue_zero_eq_formula phase label hlabel modulus hmodulus).symm

/-! ## Residue shifts by a fixed prefix -/

/-- Iterated one-letter left quotient, with membership by a whole prefix. -/
def leftQuotientWord : Word α → Language α → Language α
  | [], language => language
  | letter :: rest, language =>
      leftQuotientWord rest (Language.leftQuotient letter language)

@[simp] theorem mem_leftQuotientWord (pre word : Word α)
    (language : Language α) :
    word ∈ leftQuotientWord pre language ↔ pre ++ word ∈ language := by
  induction pre generalizing language with
  | nil => rfl
  | cons letter rest ih =>
      simp [leftQuotientWord, ih, Language.mem_leftQuotient_iff]

theorem HasHeightAtMost.leftQuotientWord {language : Language α} {n : Nat}
    (h : HasHeightAtMost language n) (pre : Word α) :
    HasHeightAtMost (leftQuotientWord pre language) n := by
  induction pre generalizing language with
  | nil => exact h
  | cons letter rest ih =>
      exact ih (h.leftQuotient letter)

private theorem phase_replicate_zero (phase : α → ZMod 2) (label : α)
    (hlabel : phase label = 0) (amount : Nat) :
    ((List.replicate amount label).map phase).sum = 0 := by
  simp [hlabel]

private theorem arrowCount_replicate_append (phase : α → ZMod 2)
    (label : α) (hlabel : phase label = 0) (amount : Nat) (word : Word α) :
    arrowCount phase label (List.replicate amount label ++ word) =
      amount + arrowCount phase label word := by
  induction amount with
  | zero => simp [arrowCount]
  | succ amount ih =>
      rw [List.replicate_succ, List.cons_append]
      simp only [arrowCount, ArrowCounting.arrowCountFrom_cons,
        ArrowCounting.c2Step, hlabel, add_zero, true_and, ↓reduceIte]
      change 1 + arrowCount phase label (List.replicate amount label ++ word) =
        amount + 1 + arrowCount phase label word
      rw [ih]
      omega

/-- Adding `modulus - residue` shifts residue `residue` to zero. -/
theorem shifted_zero_iff (modulus residue amount count : Nat)
    (hmodulus : 0 < modulus) (hresidue : residue < modulus)
    (hamount : amount = modulus - residue) :
    (amount + count) % modulus = 0 ↔ count % modulus = residue := by
  subst amount
  have hcount : count % modulus < modulus := Nat.mod_lt _ hmodulus
  by_cases hresidueZero : residue = 0
  · subst residue
    simp [Nat.add_mod]
  · have hresiduePos : 0 < residue := Nat.pos_of_ne_zero hresidueZero
    have hsubPos : 0 < modulus - residue := by omega
    have hsubLt : modulus - residue < modulus := by omega
    constructor
    · intro hzero
      rw [Nat.add_mod, Nat.mod_eq_of_lt hsubLt] at hzero
      have hdvd : modulus ∣ modulus - residue + count % modulus :=
        Nat.dvd_of_mod_eq_zero hzero
      have hsumLt : modulus - residue + count % modulus < 2 * modulus := by omega
      have hsumPos : 0 < modulus - residue + count % modulus := by omega
      have hmle : modulus ≤ modulus - residue + count % modulus :=
        Nat.le_of_dvd hsumPos hdvd
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmle
      have hdLt : d < modulus := by omega
      have hdZero : d = 0 := by
        rw [hd, Nat.add_mod, Nat.mod_self, zero_add] at hzero
        have hzero' : d % modulus = 0 := by
          simpa [Nat.mod_mod] using hzero
        exact Nat.eq_zero_of_dvd_of_lt
          (Nat.dvd_of_mod_eq_zero hzero') hdLt
      omega
    · intro hcountEq
      rw [Nat.add_mod, Nat.mod_eq_of_lt hsubLt, hcountEq]
      have hsum : modulus - residue + residue = modulus := by omega
      rw [hsum, Nat.mod_self]

/-- Every even-phase source-zero self-loop residue has height at most one. -/
theorem hasHeightAtMost_evenResidue (phase : α → ZMod 2) (label : α)
    (hlabel : phase label = 0) (modulus : Nat) (hmodulus : 0 < modulus)
    (residue : Fin modulus) :
    HasHeightAtMost (evenResidue phase label modulus residue.1) 1 := by
  let amount := modulus - residue.1
  let pre := List.replicate amount label
  have hzero := hasHeightAtMost_evenResidue_zero
    phase label hlabel modulus hmodulus
  have hquot := GSH.C2SelfLoop.HasHeightAtMost.leftQuotientWord hzero pre
  exact hquot.congr (by
    ext word
    simp only [mem_leftQuotientWord, evenResidue, Set.mem_setOf_eq]
    rw [List.map_append, List.sum_append,
      phase_replicate_zero phase label hlabel amount, zero_add,
      arrowCount_replicate_append phase label hlabel amount word]
    exact and_congr_right (fun _ =>
      shifted_zero_iff modulus residue.1 amount
        (arrowCount phase label word) hmodulus residue.2 rfl))

end C2SelfLoop
end GSH
