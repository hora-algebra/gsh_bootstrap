import GSH.Height.D5ArrowCoordinates
import GSH.Height.S3FlipPairHeight
import GSH.Height.TransferCore

/-! # Height of the modulus-five transfer formula for one `D₅` flip pair -/

set_option autoImplicit false

namespace GSH

/-- The five reflections of `D₅`. -/
abbrev D5PhaseOne := {p : D5Alphabet // d5Phase p = 1}

namespace D5FlipPairHeight

private def sx : S3Alphabet := Equiv.swap (0 : Fin 3) 1
private def sy : S3Alphabet := Equiv.swap (0 : Fin 3) 2
private def sz : S3Alphabet := Equiv.swap (1 : Fin 3) 2

private def encodePair (x y : D5Alphabet) (a : D5Alphabet) : S3Alphabet :=
  if a = x then sx
  else if a = y then sy
  else if d5Phase a = 1 then sz
  else 1

private theorem encodePair_phase (x y : D5Alphabet)
    (hx : d5Phase x = 1) (hy : d5Phase y = 1) (hne : x ≠ y)
    (a : D5Alphabet) :
    s3Phase (encodePair x y a) = d5Phase a := by
  revert x y a
  decide

private theorem encodePair_eq_sx_iff (x y : D5Alphabet)
    (_hx : d5Phase x = 1) (_hy : d5Phase y = 1) (_hne : x ≠ y)
    (a : D5Alphabet) : encodePair x y a = sx ↔ a = x := by
  have hsy : sy ≠ sx := by decide
  have hsz : sz ≠ sx := by decide
  have hone : (1 : S3Alphabet) ≠ sx := by decide
  unfold encodePair
  split_ifs <;> simp_all

private theorem encodePair_eq_sy_iff (x y : D5Alphabet)
    (_hx : d5Phase x = 1) (_hy : d5Phase y = 1) (hne : x ≠ y)
    (a : D5Alphabet) : encodePair x y a = sy ↔ a = y := by
  have hsx : sx ≠ sy := by decide
  have hsz : sz ≠ sy := by decide
  have hone : (1 : S3Alphabet) ≠ sy := by decide
  unfold encodePair
  split_ifs <;> simp_all

/-- Words containing only rotations. -/
def d5Neutral : Language D5Alphabet :=
  {word | ∀ a ∈ word, d5Phase a = 0}

/-- Canonical block `Z* x Z* y`. -/
def d5PairBlock (x y : D5Alphabet) : Language D5Alphabet :=
  Language.concat d5Neutral
    (Language.concat (Language.letter x)
      (Language.concat d5Neutral (Language.letter y)))

private noncomputable def d5NeutralR : GRegex D5Alphabet :=
  FiniteAlphabet.onlyWhere fun a => d5Phase a = 0

@[simp] private theorem denote_d5NeutralR :
    GRegex.denote d5NeutralR = d5Neutral := by
  ext word
  simp [d5NeutralR, d5Neutral]

theorem d5Neutral_starFree : IsStarFree d5Neutral :=
  ⟨d5NeutralR, denote_d5NeutralR, by simp [d5NeutralR]⟩

private noncomputable def d5PairBlockR (x y : D5Alphabet) :
    GRegex D5Alphabet :=
  GRegex.concat d5NeutralR
    (GRegex.concat (GRegex.atom x)
      (GRegex.concat d5NeutralR (GRegex.atom y)))

@[simp] private theorem denote_d5PairBlockR (x y : D5Alphabet) :
    GRegex.denote (d5PairBlockR x y) = d5PairBlock x y := by
  simp [d5PairBlockR, d5PairBlock, GRegex.denote]

private theorem d5PairBlock_starFree (x y : D5Alphabet) :
    IsStarFree (d5PairBlock x y) :=
  ⟨d5PairBlockR x y, denote_d5PairBlockR x y, by
    simp [d5PairBlockR, d5NeutralR, GRegex.starHeight]⟩

private theorem inverse_neutral (x y : D5Alphabet)
    (hx : d5Phase x = 1) (hy : d5Phase y = 1) (hne : x ≠ y) :
    Language.inverseLetterMap (encodePair x y)
        (GRegex.denote S3SelfLoopHeight.neutralWordsR) = d5Neutral := by
  ext word
  simp only [Language.mem_inverseLetterMap_iff,
    S3SelfLoopHeight.neutralWordsR,
    FiniteAlphabet.mem_denote_onlyWhere_iff, d5Neutral, Set.mem_setOf_eq,
    List.mem_map]
  constructor
  · intro h a ha
    exact (encodePair_phase x y hx hy hne a).symm.trans
      (h (encodePair x y a) ⟨a, ha, rfl⟩)
  · rintro h b ⟨a, ha, rfl⟩
    rw [encodePair_phase x y hx hy hne]
    exact h a ha

private theorem inverse_letter_x (x y : D5Alphabet)
    (hx : d5Phase x = 1) (hy : d5Phase y = 1) (hne : x ≠ y) :
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

private theorem inverse_letter_y (x y : D5Alphabet)
    (hx : d5Phase x = 1) (hy : d5Phase y = 1) (hne : x ≠ y) :
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

private theorem inverse_s3PairBlock (x y : D5Alphabet)
    (hx : d5Phase x = 1) (hy : d5Phase y = 1) (hne : x ≠ y) :
    Language.inverseLetterMap (encodePair x y)
        (S3FlipPairHeight.pairBlock sx sy) = d5PairBlock x y := by
  unfold S3FlipPairHeight.pairBlock d5PairBlock
  rw [Language.inverseLetterMap_concat, inverse_neutral x y hx hy hne,
    Language.inverseLetterMap_concat, inverse_letter_x x y hx hy hne,
    Language.inverseLetterMap_concat, inverse_neutral x y hx hy hne,
    inverse_letter_y x y hx hy hne]

/-- The star of one distinct fixed pair block is star-free. -/
theorem d5PairBlockStar_starFree (x y : D5Alphabet)
    (hx : d5Phase x = 1) (hy : d5Phase y = 1) (hne : x ≠ y) :
    IsStarFree (Language.star (d5PairBlock x y)) := by
  have hs3 := S3FlipPairHeight.isStarFree_pairBlockStar sx sy
    (by decide) (by decide) (by decide)
  have hinv := hs3.inverseLetterMap (encodePair x y)
  rw [Language.inverseLetterMap_star,
    inverse_s3PairBlock x y hx hy hne] at hinv
  exact hinv

def d5DistinguishedPairBlock (x y : D5PhaseOne) : Language D5Alphabet :=
  d5PairBlock x.1 y.1

def d5OtherPairBlocks (x y : D5PhaseOne) : Language D5Alphabet :=
  ⋃ pair : D5PhaseOne × D5PhaseOne,
    if pair = (x, y) then ∅ else d5PairBlock pair.1.1 pair.2.1

private theorem d5OtherPairBlocks_starFree (x y : D5PhaseOne) :
    IsStarFree (d5OtherPairBlocks x y) := by
  classical
  unfold d5OtherPairBlocks
  apply HasHeightAtMost.iUnion
  intro pair
  by_cases hp : pair = (x, y)
  · simpa [hp] using
      (HasHeightAtMost.empty (α := D5Alphabet) (n := 0))
  · simp only [hp, if_false]
    exact d5PairBlock_starFree pair.1.1 pair.2.1

/-- Height-one theorem for the modulus-five PST formula. -/
theorem hasHeightAtMost_d5PairFormula (x y : D5PhaseOne)
    (hne : x.1 ≠ y.1) :
    HasHeightAtMost
      (TransferCore.formula (d5DistinguishedPairBlock x y)
        (d5OtherPairBlocks x y) 5) 1 := by
  apply TransferCore.hasHeightAtMost_formula
  · simpa [d5DistinguishedPairBlock] using d5PairBlock_starFree x.1 y.1
  · exact d5OtherPairBlocks_starFree x y
  · simpa [d5DistinguishedPairBlock] using
      d5PairBlockStar_starFree x.1 y.1 x.2 y.2 hne

end D5FlipPairHeight

end GSH
