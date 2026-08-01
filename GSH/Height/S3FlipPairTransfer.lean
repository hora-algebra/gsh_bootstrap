import GSH.Height.S3FlipPairCode
import GSH.Height.S3FlipPairHeight
import GSH.Height.TransferSemantics

/-!
# The zero-residue transfer for canonical `S₃` flip pairs

This file partitions the canonical phase-one pair code into one distinguished
ordered pair and the finite union of all other ordered pairs.  Its main
theorem identifies the exact zero-residue language with the modulus-three
transfer formula, followed by the canonical neutral suffix.
-/

set_option autoImplicit false

namespace GSH

namespace S3FlipPairTransfer

open S3ArrowArithmetic
open S3FlipPairCode
open S3FlipPairHeight
open S3SelfLoopHeight
open TransferSemantics

/-- The fixed block language belonging to the distinguished ordered pair. -/
def distinguishedPairBlock (x y : S3PhaseOne) : Language S3Alphabet :=
  pairBlock x.1 y.1

/-- The finite union of all ordered phase-one pair blocks other than `(x,y)`. -/
def otherPairBlocks (x y : S3PhaseOne) : Language S3Alphabet :=
  ⋃ pair : S3PhaseOne × S3PhaseOne,
    if pair = (x, y) then ∅ else pairBlock pair.1.1 pair.2.1

/-- Words containing no phase-one letters. -/
def neutralWords : Language S3Alphabet :=
  GRegex.denote neutralWordsR

/-- The exact even-phase language whose distinguished ordered pair count is
zero modulo three. -/
def s3PairResidueZero (x y : S3PhaseOne) : Language S3Alphabet :=
  {word | (word.map s3Phase).sum = 0 ∧
    pairCountOf x y (phaseOneSubword word) % 3 = 0}

private theorem mem_pairBlock_iff (x y : S3PhaseOne)
    (word : Word S3Alphabet) :
    word ∈ pairBlock x.1 y.1 ↔
      IsPairBlock word ∧ phaseOneSubword word = [x, y] := by
  classical
  constructor
  · intro hword
    rcases hword with ⟨leading, hleading, rest₁,
      ⟨xword, hxword, rest₂,
        ⟨middle, hmiddle, yword, hyword, rfl⟩, rfl⟩, rfl⟩
    have hxword' : xword = [x.1] := hxword
    have hyword' : yword = [y.1] := hyword
    subst xword
    subst yword
    have hleading' : IsNeutralWord leading := by
      change leading ∈ GRegex.denote
        (FiniteAlphabet.onlyWhere fun a : S3Alphabet => s3Phase a = 0) at hleading
      rw [FiniteAlphabet.mem_denote_onlyWhere_iff] at hleading
      exact hleading
    have hmiddle' : IsNeutralWord middle := by
      change middle ∈ GRegex.denote
        (FiniteAlphabet.onlyWhere fun a : S3Alphabet => s3Phase a = 0) at hmiddle
      rw [FiniteAlphabet.mem_denote_onlyWhere_iff] at hmiddle
      exact hmiddle
    constructor
    · exact ⟨leading, x.1, middle, y.1, hleading', x.2,
        hmiddle', y.2, by simp⟩
    · simp [phaseOneSubword, x.2, y.2, phaseOneSubword_append,
        phaseOneSubword_eq_nil_of_neutral leading hleading',
        phaseOneSubword_eq_nil_of_neutral middle hmiddle']
  · rintro ⟨hblock, hsubword⟩
    rcases hblock with ⟨leading, a, middle, b, hleading, ha,
      hmiddle, hb, rfl⟩
    have hlabels : [⟨a, ha⟩, ⟨b, hb⟩] = [x, y] := by
      simpa [phaseOneSubword, ha, hb, phaseOneSubword_append,
        phaseOneSubword_eq_nil_of_neutral leading hleading,
        phaseOneSubword_eq_nil_of_neutral middle hmiddle] using hsubword
    simp at hlabels
    have hax : a = x.1 := congrArg Subtype.val hlabels.1
    have hby : b = y.1 := congrArg Subtype.val hlabels.2
    subst a
    subst b
    refine ⟨leading, ?_, [x.1] ++ middle ++ [y.1], ?_, ?_⟩
    · change leading ∈ GRegex.denote
        (FiniteAlphabet.onlyWhere fun a : S3Alphabet => s3Phase a = 0)
      rw [FiniteAlphabet.mem_denote_onlyWhere_iff]
      exact hleading
    · refine ⟨[x.1], rfl, middle ++ [y.1], ?_, rfl⟩
      refine ⟨middle, ?_, [y.1], rfl, rfl⟩
      change middle ∈ GRegex.denote
        (FiniteAlphabet.onlyWhere fun a : S3Alphabet => s3Phase a = 0)
      rw [FiniteAlphabet.mem_denote_onlyWhere_iff]
      exact hmiddle
    · simp [List.append_assoc]

private theorem mem_otherPairBlocks_iff (x y : S3PhaseOne)
    (word : Word S3Alphabet) :
    word ∈ otherPairBlocks x y ↔
      IsPairBlock word ∧ phaseOneSubword word ≠ [x, y] := by
  classical
  simp only [otherPairBlocks, Set.mem_iUnion]
  constructor
  · rintro ⟨pair, hpair⟩
    by_cases hp : pair = (x, y)
    · rw [hp, if_pos rfl] at hpair
      simp at hpair
    · have hmem : word ∈ pairBlock pair.1.1 pair.2.1 := by
        simpa [hp] using hpair
      have hcode := (mem_pairBlock_iff pair.1 pair.2 word).mp hmem
      refine ⟨hcode.1, ?_⟩
      intro heq
      have hlabels : [pair.1, pair.2] = [x, y] := hcode.2.symm.trans heq
      simp at hlabels
      have hfst : pair.1 = x := hlabels.1
      have hsnd : pair.2 = y := hlabels.2
      exact hp (Prod.ext hfst hsnd)
  · rintro ⟨hblock, hne⟩
    obtain ⟨a, b, hab⟩ := phaseOneSubword_pairBlock word hblock
    refine ⟨(a, b), ?_⟩
    have hp : (a, b) ≠ (x, y) := by
      intro hp
      cases hp
      exact hne hab
    have hmem : word ∈ pairBlock a.1 b.1 :=
      (mem_pairBlock_iff a b word).mpr ⟨hblock, hab⟩
    simpa [hp] using hmem

private theorem mem_pairCode_iff (x y : S3PhaseOne)
    (word : Word S3Alphabet) :
    word ∈ distinguishedPairBlock x y ∪ otherPairBlocks x y ↔
      IsPairBlock word := by
  classical
  rw [Set.mem_union]
  simp only [distinguishedPairBlock, mem_pairBlock_iff,
    mem_otherPairBlocks_iff]
  constructor
  · rintro (⟨hblock, -⟩ | ⟨hblock, -⟩) <;> exact hblock
  · intro hblock
    by_cases hsub : phaseOneSubword word = [x, y]
    · exact Or.inl ⟨hblock, hsub⟩
    · exact Or.inr ⟨hblock, hsub⟩

private theorem pairLanguages_disjoint (x y : S3PhaseOne) :
    Disjoint (distinguishedPairBlock x y) (otherPairBlocks x y) := by
  rw [Set.disjoint_left]
  intro word hdist hother
  exact (mem_otherPairBlocks_iff x y word).mp hother |>.2
    ((mem_pairBlock_iff x y word).mp hdist).2

private theorem pairCode_unique (x y : S3PhaseOne) :
    ∀ left right : List (Word S3Alphabet),
      Factorizes (distinguishedPairBlock x y ∪ otherPairBlocks x y)
          left left.flatten →
      Factorizes (distinguishedPairBlock x y ∪ otherPairBlocks x y)
          right right.flatten →
      left.flatten = right.flatten → left = right := by
  intro left right hleft hright hflat
  have hleftFactor : IsPairFactorization left [] left.flatten := by
    refine ⟨?_, (by intro a ha; simp at ha), by simp⟩
    intro piece hpiece
    exact (mem_pairCode_iff x y piece).mp (hleft.1 piece hpiece)
  have hrightFactor : IsPairFactorization right [] left.flatten := by
    refine ⟨?_, (by intro a ha; simp at ha), ?_⟩
    · intro piece hpiece
      exact (mem_pairCode_iff x y piece).mp (hright.1 piece hpiece)
    · simpa using hflat.symm
  exact (pairFactorization_unique left right [] [] left.flatten
    hleftFactor hrightFactor).1

private theorem countIn_distinguished_eq_pairBlockCount
    (x y : S3PhaseOne) (pieces : List (Word S3Alphabet))
    (hpieces : ∀ piece ∈ pieces, IsPairBlock piece) :
    countIn (distinguishedPairBlock x y) pieces =
      pairBlockCount x y pieces := by
  classical
  induction pieces with
  | nil => simp [countIn, pairBlockCount]
  | cons piece pieces ih =>
      have hpiece := hpieces piece (by simp)
      have htail : ∀ other ∈ pieces, IsPairBlock other := by
        intro other hother
        exact hpieces other (by simp [hother])
      have hmem : piece ∈ distinguishedPairBlock x y ↔
          phaseOneSubword piece = [x, y] := by
        simpa [distinguishedPairBlock, hpiece] using
          (mem_pairBlock_iff x y piece)
      have hcountCons :
          countIn (distinguishedPairBlock x y) (piece :: pieces) =
            (if piece ∈ distinguishedPairBlock x y then 1 else 0) +
              countIn (distinguishedPairBlock x y) pieces := by
        unfold countIn
        rw [List.countP_cons]
        by_cases hm : piece ∈ distinguishedPairBlock x y <;>
          simp [hm, Nat.add_comm]
      rw [hcountCons]
      rw [ih htail]
      by_cases hm : piece ∈ distinguishedPairBlock x y
      · have hs := hmem.mp hm
        simp [pairBlockCount, hm, hs]
      · have hs : phaseOneSubword piece ≠ [x, y] := by
          exact fun hs => hm (hmem.mpr hs)
        simp [pairBlockCount, hm, hs]

private theorem phase_sum_zero_of_pairFactorization
    (pieces : List (Word S3Alphabet)) (suffix word : Word S3Alphabet)
    (hfactor : IsPairFactorization pieces suffix word) :
    (word.map s3Phase).sum = 0 := by
  apply (phaseOneSubword_even_iff_phase_sum_zero word).mp
  rw [← hfactor.2.2, phaseOneSubword_append,
    phaseOneSubword_eq_nil_of_neutral suffix hfactor.2.1]
  simp only [List.append_nil]
  have heven : ∀ blocks : List (Word S3Alphabet),
      (∀ piece ∈ blocks, IsPairBlock piece) →
        (phaseOneSubword blocks.flatten).length % 2 = 0 := by
    intro blocks hblocks
    induction blocks with
    | nil => simp [phaseOneSubword]
    | cons piece blocks ih =>
        have hpiece := hblocks piece (by simp)
        have htail : ∀ other ∈ blocks, IsPairBlock other := by
          intro other hother
          exact hblocks other (by simp [hother])
        obtain ⟨a, b, hab⟩ := phaseOneSubword_pairBlock piece hpiece
        rw [List.flatten_cons, phaseOneSubword_append, hab]
        simp only [List.length_append, List.length_cons, List.length_nil]
        have iht := ih htail
        omega
  exact heven pieces hfactor.1

/-- The exact even-phase, zero pair-residue language is the transfer formula
on canonical pair blocks, followed by its unique neutral suffix. -/
theorem s3PairResidue_zero_eq_formula (x y : S3PhaseOne) :
    s3PairResidueZero x y =
      Language.concat
        (TransferCore.formula (distinguishedPairBlock x y)
          (otherPairBlocks x y) 3)
        neutralWords := by
  classical
  ext word
  rw [Language.mem_concat_iff]
  change ((word.map s3Phase).sum = 0 ∧
      pairCountOf x y (phaseOneSubword word) % 3 = 0) ↔ _
  constructor
  · rintro ⟨hphase, hcount⟩
    obtain ⟨pieces, suffix, hfactor⟩ := exists_pairFactorization word hphase
    refine ⟨pieces.flatten, ?_, suffix, ?_, hfactor.2.2⟩
    · rw [mem_formula_partition_three_iff
          (distinguishedPairBlock x y) (otherPairBlocks x y)
          (pairLanguages_disjoint x y) (pairCode_unique x y)]
      refine ⟨pieces, ⟨?_, rfl⟩, ?_⟩
      · intro piece hpiece
        exact (mem_pairCode_iff x y piece).mpr (hfactor.1 piece hpiece)
      · rw [countIn_distinguished_eq_pairBlockCount x y pieces hfactor.1,
          pairBlockCount_eq_pairCountOf x y pieces suffix word hfactor]
        exact hcount
    · simpa only [neutralWords, neutralWordsR,
        FiniteAlphabet.mem_denote_onlyWhere_iff, IsNeutralWord,
        S3ArrowResidue.IsPhaseZeroWord] using hfactor.2.1
  · rintro ⟨pre, hpre, suffix, hsuffix, hword⟩
    rw [mem_formula_partition_three_iff
        (distinguishedPairBlock x y) (otherPairBlocks x y)
        (pairLanguages_disjoint x y) (pairCode_unique x y)] at hpre
    obtain ⟨pieces, hpieces, hcount⟩ := hpre
    have hblocks : ∀ piece ∈ pieces, IsPairBlock piece := by
      intro piece hpiece
      exact (mem_pairCode_iff x y piece).mp (hpieces.1 piece hpiece)
    have hneutral : IsNeutralWord suffix := by
      simpa only [neutralWords, neutralWordsR,
        FiniteAlphabet.mem_denote_onlyWhere_iff, IsNeutralWord,
        S3ArrowResidue.IsPhaseZeroWord] using hsuffix
    have hfactor : IsPairFactorization pieces suffix word := by
      refine ⟨hblocks, hneutral, ?_⟩
      rw [hpieces.2]
      exact hword
    refine ⟨phase_sum_zero_of_pairFactorization pieces suffix word hfactor, ?_⟩
    rw [← pairBlockCount_eq_pairCountOf x y pieces suffix word hfactor,
      ← countIn_distinguished_eq_pairBlockCount x y pieces hblocks]
    exact hcount

/-- The language of all non-distinguished ordered pair blocks is star-free,
because the phase-one alphabet is finite. -/
theorem isStarFree_otherPairBlocks (x y : S3PhaseOne) :
    IsStarFree (otherPairBlocks x y) := by
  classical
  unfold otherPairBlocks
  apply HasHeightAtMost.iUnion
  intro pair
  by_cases hp : pair = (x, y)
  · simpa [hp] using
      (HasHeightAtMost.empty (α := S3Alphabet) (n := 0))
  · simp only [hp, if_false]
    exact isStarFree_pairBlock pair.1.1 pair.2.1

private theorem isStarFree_neutralWords : IsStarFree neutralWords := by
  exact ⟨neutralWordsR, rfl, by simp [neutralWordsR]⟩

/-- Height-one consequence of the exact transfer equality for a distinct
phase-one pair. -/
theorem hasHeightAtMost_s3PairResidue_zero (x y : S3PhaseOne)
    (hne : x.1 ≠ y.1) :
    HasHeightAtMost (s3PairResidueZero x y) 1 := by
  have hstar : IsStarFree
      (Language.star (distinguishedPairBlock x y)) := by
    simpa [distinguishedPairBlock] using
      isStarFree_pairBlockStar x.1 y.1 x.2 y.2 hne
  have hformula := TransferCore.hasHeightAtMost_formula
    (distinguishedPairBlock x y) (otherPairBlocks x y) 3
    (by simpa [distinguishedPairBlock] using isStarFree_pairBlock x.1 y.1)
    (isStarFree_otherPairBlocks x y) hstar
  exact (hformula.concat (isStarFree_neutralWords.mono (by omega))).congr
    (s3PairResidue_zero_eq_formula x y).symm

end S3FlipPairTransfer

end GSH
