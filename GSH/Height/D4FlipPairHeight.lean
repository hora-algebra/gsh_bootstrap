import GSH.Height.D4ArrowArithmetic
import GSH.Height.S3FlipPairHeight
import GSH.Height.TransferCore

/-!
# Height of the modulus-eight transfer formula for one `D₄` flip pair

This file proves the height-theoretic half.  The semantic equality with the
actual pair-count residue language is proved separately in
`GSH.Height.D4FlipPairTransfer`.
-/

set_option autoImplicit false

namespace GSH

namespace D4FlipPairHeight

open D4ArrowArithmetic

private def sx : S3Alphabet := Equiv.swap (0 : Fin 3) 1
private def sy : S3Alphabet := Equiv.swap (0 : Fin 3) 2
private def sz : S3Alphabet := Equiv.swap (1 : Fin 3) 2

/-- Encode a selected ordered `D₄` reflection pair by two fixed `S₃` flips. -/
private def encodePair (x y : D4Alphabet) (a : D4Alphabet) : S3Alphabet :=
  if a = x then sx
  else if a = y then sy
  else if d4Phase a = 1 then sz
  else 1

private theorem encodePair_phase (x y : D4Alphabet)
    (hx : d4Phase x = 1) (hy : d4Phase y = 1) (hne : x ≠ y)
    (a : D4Alphabet) :
    s3Phase (encodePair x y a) = d4Phase a := by
  revert x y a
  decide

private theorem encodePair_eq_sx_iff (x y : D4Alphabet)
    (_hx : d4Phase x = 1) (_hy : d4Phase y = 1) (_hne : x ≠ y)
    (a : D4Alphabet) : encodePair x y a = sx ↔ a = x := by
  have hsy : sy ≠ sx := by decide
  have hsz : sz ≠ sx := by decide
  have hone : (1 : S3Alphabet) ≠ sx := by decide
  unfold encodePair
  split_ifs <;> simp_all

private theorem encodePair_eq_sy_iff (x y : D4Alphabet)
    (_hx : d4Phase x = 1) (_hy : d4Phase y = 1) (hne : x ≠ y)
    (a : D4Alphabet) : encodePair x y a = sy ↔ a = y := by
  have hsx : sx ≠ sy := by decide
  have hsz : sz ≠ sy := by decide
  have hone : (1 : S3Alphabet) ≠ sy := by decide
  unfold encodePair
  split_ifs <;> simp_all

/-- Words containing only phase-zero `D₄` letters. -/
def d4Neutral : Language D4Alphabet :=
  {word | ∀ a ∈ word, d4Phase a = 0}

/-- Canonical fixed pair block `Z* x Z* y`. -/
def d4PairBlock (x y : D4Alphabet) : Language D4Alphabet :=
  Language.concat d4Neutral
    (Language.concat (Language.letter x)
      (Language.concat d4Neutral (Language.letter y)))

private noncomputable def d4NeutralR : GRegex D4Alphabet :=
  FiniteAlphabet.onlyWhere fun a => d4Phase a = 0

@[simp]
private theorem denote_d4NeutralR :
    GRegex.denote d4NeutralR = d4Neutral := by
  ext word
  simp [d4NeutralR, d4Neutral]

/-- The language of phase-zero `D₄` words is star-free.  This is the
neutral suffix consumed by the canonical pair-transfer decomposition. -/
theorem d4Neutral_starFree : IsStarFree d4Neutral :=
  ⟨d4NeutralR, denote_d4NeutralR, by simp [d4NeutralR]⟩

private noncomputable def d4PairBlockR (x y : D4Alphabet) : GRegex D4Alphabet :=
  GRegex.concat d4NeutralR
    (GRegex.concat (GRegex.atom x)
      (GRegex.concat d4NeutralR (GRegex.atom y)))

@[simp]
private theorem denote_d4PairBlockR (x y : D4Alphabet) :
    GRegex.denote (d4PairBlockR x y) = d4PairBlock x y := by
  simp [d4PairBlockR, d4PairBlock, GRegex.denote]

@[simp]
private theorem starHeight_d4PairBlockR (x y : D4Alphabet) :
    GRegex.starHeight (d4PairBlockR x y) = 0 := by
  simp [d4PairBlockR, d4NeutralR, GRegex.starHeight]

private theorem inverse_neutral (x y : D4Alphabet)
    (hx : d4Phase x = 1) (hy : d4Phase y = 1) (hne : x ≠ y) :
    Language.inverseLetterMap (encodePair x y)
        (GRegex.denote S3SelfLoopHeight.neutralWordsR) =
      d4Neutral := by
  ext word
  simp only [Language.mem_inverseLetterMap_iff,
    S3SelfLoopHeight.neutralWordsR,
    FiniteAlphabet.mem_denote_onlyWhere_iff, d4Neutral, Set.mem_setOf_eq,
    List.mem_map]
  constructor
  · intro h a ha
    exact (encodePair_phase x y hx hy hne a).symm.trans
      (h (encodePair x y a) ⟨a, ha, rfl⟩)
  · rintro h b ⟨a, ha, rfl⟩
    rw [encodePair_phase x y hx hy hne]
    exact h a ha

private theorem inverse_letter_x (x y : D4Alphabet)
    (hx : d4Phase x = 1) (hy : d4Phase y = 1) (hne : x ≠ y) :
    Language.inverseLetterMap (encodePair x y) (Language.letter sx) =
      Language.letter x := by
  ext word
  simp only [Language.mem_inverseLetterMap_iff, Language.mem_letter_iff,
    List.map_eq_singleton_iff]
  constructor
  · rintro ⟨a, rfl, ha⟩
    exact congrArg (fun z => [z])
      ((encodePair_eq_sx_iff x y hx hy hne a).1 ha)
  · rintro rfl
    exact ⟨x, rfl, (encodePair_eq_sx_iff x y hx hy hne x).2 rfl⟩

private theorem inverse_letter_y (x y : D4Alphabet)
    (hx : d4Phase x = 1) (hy : d4Phase y = 1) (hne : x ≠ y) :
    Language.inverseLetterMap (encodePair x y) (Language.letter sy) =
      Language.letter y := by
  ext word
  simp only [Language.mem_inverseLetterMap_iff, Language.mem_letter_iff,
    List.map_eq_singleton_iff]
  constructor
  · rintro ⟨a, rfl, ha⟩
    exact congrArg (fun z => [z])
      ((encodePair_eq_sy_iff x y hx hy hne a).1 ha)
  · rintro rfl
    exact ⟨y, rfl, (encodePair_eq_sy_iff x y hx hy hne y).2 rfl⟩

private theorem inverse_s3PairBlock (x y : D4Alphabet)
    (hx : d4Phase x = 1) (hy : d4Phase y = 1) (hne : x ≠ y) :
    Language.inverseLetterMap (encodePair x y)
        (S3FlipPairHeight.pairBlock sx sy) = d4PairBlock x y := by
  unfold S3FlipPairHeight.pairBlock d4PairBlock
  rw [Language.inverseLetterMap_concat, inverse_neutral x y hx hy hne,
    Language.inverseLetterMap_concat, inverse_letter_x x y hx hy hne,
    Language.inverseLetterMap_concat, inverse_neutral x y hx hy hne,
    inverse_letter_y x y hx hy hne]

private theorem d4PairBlock_starFree (x y : D4Alphabet) :
    IsStarFree (d4PairBlock x y) :=
  ⟨d4PairBlockR x y, denote_d4PairBlockR x y, by simp⟩

/-- The star of one distinct fixed `D₄` phase-one pair block is star-free. -/
theorem d4PairBlockStar_starFree (x y : D4Alphabet)
    (hx : d4Phase x = 1) (hy : d4Phase y = 1) (hne : x ≠ y) :
    IsStarFree (Language.star (d4PairBlock x y)) := by
  have hs3 := S3FlipPairHeight.isStarFree_pairBlockStar sx sy
    (by decide) (by decide) (by decide)
  have hinv := hs3.inverseLetterMap (encodePair x y)
  rw [Language.inverseLetterMap_star,
    inverse_s3PairBlock x y hx hy hne] at hinv
  exact hinv

def d4DistinguishedPairBlock (x y : D4PhaseOne) : Language D4Alphabet :=
  d4PairBlock x.1 y.1

/-- Finite union of all ordered phase-one pair blocks except `(x,y)`. -/
def d4OtherPairBlocks (x y : D4PhaseOne) : Language D4Alphabet :=
  ⋃ pair : D4PhaseOne × D4PhaseOne,
    if pair = (x, y) then ∅ else d4PairBlock pair.1.1 pair.2.1

private theorem d4OtherPairBlocks_starFree (x y : D4PhaseOne) :
    IsStarFree (d4OtherPairBlocks x y) := by
  classical
  unfold d4OtherPairBlocks
  apply HasHeightAtMost.iUnion
  intro pair
  by_cases hp : pair = (x, y)
  · simpa [hp] using
      (HasHeightAtMost.empty (α := D4Alphabet) (n := 0))
  · simp only [hp, if_false]
    exact d4PairBlock_starFree pair.1.1 pair.2.1

/-- Height-one theorem for the modulus-eight PST formula.  No semantic
identification with the actual pair-residue language is asserted here. -/
theorem hasHeightAtMost_d4PairFormula (x y : D4PhaseOne)
    (hne : x.1 ≠ y.1) :
    HasHeightAtMost
      (TransferCore.formula (d4DistinguishedPairBlock x y)
        (d4OtherPairBlocks x y) 8) 1 := by
  apply TransferCore.hasHeightAtMost_formula
  · simpa [d4DistinguishedPairBlock] using d4PairBlock_starFree x.1 y.1
  · exact d4OtherPairBlocks_starFree x y
  · simpa [d4DistinguishedPairBlock] using
      d4PairBlockStar_starFree x.1 y.1 x.2 y.2 hne

end D4FlipPairHeight

end GSH
