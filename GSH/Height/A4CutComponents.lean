import GSH.Height.A4CutParity
import GSH.Height.S3FlipPairHeight

/-!
# Star-free infrastructure for the `A₄` base-cut return block

This file removes the irrelevant absolute target phase, records the exact
arrival trace and the two nonzero-state first-return recurrences, and constructs
a concrete height-zero expression for the first-return grammar.  The one
remaining semantic obligation is that this expression denotes the return block;
it is kept as an explicit premise of the final theorem below.
-/

set_option autoImplicit false

namespace GSH

/-- Translating both the start and target phases does not change the number
of arrivals. -/
theorem a4BaseCutCountFrom_shift (shift start target : ZMod 3)
    (word : Word A4) :
    a4BaseCutCountFrom (start + shift) (target + shift) word =
      a4BaseCutCountFrom start target word := by
  induction word generalizing start with
  | nil => rfl
  | cons g word ih =>
      simp only [a4BaseCutCountFrom]
      have harrival :
          ((start + shift) + a4PhaseValue g = target + shift) ↔
            (start + a4PhaseValue g = target) := by
        constructor <;> intro h
        · apply add_right_cancel (b := shift)
          simpa [add_assoc, add_comm, add_left_comm] using h
        · simpa [add_assoc, add_comm, add_left_comm] using
            congrArg (fun z => z + shift) h
      rw [if_congr harrival rfl rfl]
      simpa [add_assoc, add_comm, add_left_comm] using
        ih (start + a4PhaseValue g)

/-- Translating the initial phase translates the final phase by the same
amount. -/
theorem a4PhaseRunFrom_shift (shift start : ZMod 3) (word : Word A4) :
    a4PhaseRunFrom (start + shift) word =
      a4PhaseRunFrom start word + shift := by
  induction word generalizing start with
  | nil => rfl
  | cons g word ih =>
      simp only [a4PhaseRunFrom]
      simpa [add_assoc, add_comm, add_left_comm] using
        ih (start + a4PhaseValue g)

/-- A base-cut return block depends only on relative phase, not on the
absolute target. -/
theorem a4BaseCutReturnBlock_target_independent (target : ZMod 3) :
    a4BaseCutReturnBlock target = a4BaseCutReturnBlock 0 := by
  ext word
  simp only [a4BaseCutReturnBlock, Set.mem_setOf_eq]
  have hc := a4BaseCutCountFrom_shift (-target) target target word
  have hr := a4PhaseRunFrom_shift (-target) target word
  simp at hc hr
  rw [hc]
  constructor
  · rintro ⟨hcount, hrun⟩
    refine ⟨hcount, ?_⟩
    rw [hr, hrun]
    simp
  · rintro ⟨hcount, hrun⟩
    refine ⟨hcount, ?_⟩
    apply add_right_cancel (b := -target)
    rw [← hr, hrun]
    simp

/-- The sequence of phases reached after each successive letter. -/
def a4PhaseTraceFrom : ZMod 3 → Word A4 → List (ZMod 3)
  | _, [] => []
  | phase, g :: word =>
      let next := phase + a4PhaseValue g
      next :: a4PhaseTraceFrom next word

/-- The cut count is exactly the number of target occurrences in the phase
trace. -/
theorem a4BaseCutCountFrom_eq_traceCount (start target : ZMod 3)
    (word : Word A4) :
    a4BaseCutCountFrom start target word =
      (a4PhaseTraceFrom start word).count target := by
  induction word generalizing start with
  | nil => rfl
  | cons g word ih =>
      simp only [a4BaseCutCountFrom, a4PhaseTraceFrom, List.count_cons]
      rw [ih]
      by_cases h : start + a4PhaseValue g = target <;>
        simp [h, Nat.add_comm]

/-- On a nonempty word, the last reached phase is the final phase run. -/
theorem a4PhaseTraceFrom_getLast?_cons (start : ZMod 3) (g : A4)
    (word : Word A4) :
    (a4PhaseTraceFrom start (g :: word)).getLast? =
      some (a4PhaseRunFrom start (g :: word)) := by
  induction word generalizing start g with
  | nil => simp [a4PhaseTraceFrom, a4PhaseRunFrom]
  | cons h word ih =>
      simp only [a4PhaseTraceFrom, List.getLast?_cons_cons,
        a4PhaseRunFrom]
      exact ih (start + a4PhaseValue g) h

/-- Words making their first return to phase zero when started in `start`.
The two nonzero instances are the states of the concrete return grammar below. -/
def a4BaseCutFirstReturnFromZero (start : ZMod 3) : Language A4 :=
  {word | a4BaseCutCountFrom start 0 word = 1 ∧
    a4PhaseRunFrom start word = 0}

/-- A run from a different initial phase to its target contains at least one
arrival at that target. -/
theorem a4BaseCutCountFrom_pos_of_run_eq (start target : ZMod 3)
    (word : Word A4) (hne : start ≠ target)
    (hrun : a4PhaseRunFrom start word = target) :
    0 < a4BaseCutCountFrom start target word := by
  induction word generalizing start with
  | nil =>
      simp [a4PhaseRunFrom] at hrun
      exact False.elim (hne hrun)
  | cons g word ih =>
      simp only [a4PhaseRunFrom] at hrun
      simp only [a4BaseCutCountFrom]
      by_cases hnext : start + a4PhaseValue g = target
      · simp [hnext]
      · simp only [hnext, if_false, zero_add]
        exact ih (start + a4PhaseValue g) hnext hrun

/-- A run returning to its starting phase without recording an arrival must be
empty.  This supplies the terminal cases of the first-return grammar. -/
theorem a4BaseCutCountFrom_zero_run_same_iff_nil (start : ZMod 3)
    (word : Word A4) :
    (a4BaseCutCountFrom start start word = 0 ∧
      a4PhaseRunFrom start word = start) ↔ word = [] := by
  constructor
  · rintro ⟨hcount, hrun⟩
    cases word with
    | nil => rfl
    | cons g word =>
        simp only [a4BaseCutCountFrom, a4PhaseRunFrom] at hcount hrun
        by_cases hnext : start + a4PhaseValue g = start
        · simp [hnext] at hcount
        · have hpos := a4BaseCutCountFrom_pos_of_run_eq
            (start + a4PhaseValue g) start word hnext hrun
          simp [hnext] at hcount
          omega
  · rintro rfl
    simp [a4BaseCutCountFrom, a4PhaseRunFrom]

/-- Every `A₄` letter belongs to exactly one of the three phase classes. -/
theorem a4PhaseValue_trichotomy (g : A4) :
    a4PhaseValue g = 0 ∨ a4PhaseValue g = 1 ∨ a4PhaseValue g = 2 := by
  revert g
  decide

/-- Exact one-letter recurrence for the phase-one state of the first-return
grammar. -/
theorem a4BaseCutFirstReturnFromZero_one_cons (g : A4) (word : Word A4) :
    g :: word ∈ a4BaseCutFirstReturnFromZero 1 ↔
      (a4PhaseValue g = 0 ∧
        word ∈ a4BaseCutFirstReturnFromZero 1) ∨
      (a4PhaseValue g = 1 ∧
        word ∈ a4BaseCutFirstReturnFromZero 2) ∨
      (a4PhaseValue g = 2 ∧ word = []) := by
  rcases a4PhaseValue_trichotomy g with h | h | h
  · simp [a4BaseCutFirstReturnFromZero, a4BaseCutCountFrom,
      a4PhaseRunFrom, h, show (1 + 0 : ZMod 3) = 1 by decide,
      show (0 : ZMod 3) ≠ 2 by decide]
  · simp [a4BaseCutFirstReturnFromZero, a4BaseCutCountFrom,
      a4PhaseRunFrom, h, show (1 + 1 : ZMod 3) = 2 by decide,
      show (1 : ZMod 3) ≠ 2 by decide,
      show (2 : ZMod 3) ≠ 0 by decide]
  · simp [a4BaseCutFirstReturnFromZero, a4BaseCutCountFrom,
      a4PhaseRunFrom, h, show (1 + 2 : ZMod 3) = 0 by decide,
      show (2 : ZMod 3) ≠ 0 by decide,
      show (2 : ZMod 3) ≠ 1 by decide,
      a4BaseCutCountFrom_zero_run_same_iff_nil]

/-- Exact one-letter recurrence for the phase-two state of the first-return
grammar. -/
theorem a4BaseCutFirstReturnFromZero_two_cons (g : A4) (word : Word A4) :
    g :: word ∈ a4BaseCutFirstReturnFromZero 2 ↔
      (a4PhaseValue g = 0 ∧
        word ∈ a4BaseCutFirstReturnFromZero 2) ∨
      (a4PhaseValue g = 2 ∧
        word ∈ a4BaseCutFirstReturnFromZero 1) ∨
      (a4PhaseValue g = 1 ∧ word = []) := by
  rcases a4PhaseValue_trichotomy g with h | h | h
  · simp [a4BaseCutFirstReturnFromZero, a4BaseCutCountFrom,
      a4PhaseRunFrom, h, show (2 + 0 : ZMod 3) = 2 by decide,
      show (0 : ZMod 3) ≠ 2 by decide,
      show (2 : ZMod 3) ≠ 0 by decide]
  · simp [a4BaseCutFirstReturnFromZero, a4BaseCutCountFrom,
      a4PhaseRunFrom, h, show (2 + 1 : ZMod 3) = 0 by decide,
      show (1 : ZMod 3) ≠ 2 by decide,
      a4BaseCutCountFrom_zero_run_same_iff_nil]
  · simp [a4BaseCutFirstReturnFromZero, a4BaseCutCountFrom,
      a4PhaseRunFrom, h, show (2 + 2 : ZMod 3) = 1 by decide,
      show (2 : ZMod 3) ≠ 0 by decide,
      show (2 : ZMod 3) ≠ 1 by decide]

/-- The complete return block splits after its first letter into the immediate
phase-zero return or one of the two nonzero first-return states. -/
theorem a4BaseCutReturnBlock_zero_cons (g : A4) (word : Word A4) :
    g :: word ∈ a4BaseCutReturnBlock 0 ↔
      (a4PhaseValue g = 0 ∧ word = []) ∨
      (a4PhaseValue g = 1 ∧
        word ∈ a4BaseCutFirstReturnFromZero 1) ∨
      (a4PhaseValue g = 2 ∧
        word ∈ a4BaseCutFirstReturnFromZero 2) := by
  rcases a4PhaseValue_trichotomy g with h | h | h
  · simp [a4BaseCutReturnBlock, a4BaseCutCountFrom, a4PhaseRunFrom,
      a4BaseCutFirstReturnFromZero, h,
      a4BaseCutCountFrom_zero_run_same_iff_nil,
      show (0 : ZMod 3) ≠ 1 by decide,
      show (0 : ZMod 3) ≠ 2 by decide]
  · simp [a4BaseCutReturnBlock, a4BaseCutCountFrom, a4PhaseRunFrom,
      a4BaseCutFirstReturnFromZero, h,
      show (0 + 1 : ZMod 3) = 1 by decide,
      show (1 : ZMod 3) ≠ 0 by decide,
      show (1 : ZMod 3) ≠ 2 by decide]
  · simp [a4BaseCutReturnBlock, a4BaseCutCountFrom, a4PhaseRunFrom,
      a4BaseCutFirstReturnFromZero, h,
      show (0 + 2 : ZMod 3) = 2 by decide,
      show (2 : ZMod 3) ≠ 0 by decide,
      show (2 : ZMod 3) ≠ 1 by decide]

namespace A4CutComponents

private def sx : S3Alphabet := Equiv.swap (0 : Fin 3) 1
private def sy : S3Alphabet := Equiv.swap (0 : Fin 3) 2

/-- Collapse the three `A₄` phase classes to one neutral and two distinct
`S₃` letters.  This is only an alphabet map, not a group homomorphism. -/
private def encodePhase (g : A4) : S3Alphabet :=
  if a4PhaseValue g = 0 then 1
  else if a4PhaseValue g = 1 then sx else sy

/-- Words all of whose letters have phase zero. -/
def neutralL : Language A4 :=
  {word | ∀ g ∈ word, a4PhaseValue g = 0}

/-- The one-letter language of a fixed phase class. -/
def phaseLetterL (phase : ZMod 3) : Language A4 :=
  {word | ∃ g, a4PhaseValue g = phase ∧ word = [g]}

/-- One phase-pair block `Z* · P_p · Z* · P_q`. -/
def phasePairBlock (p q : ZMod 3) : Language A4 :=
  Language.concat neutralL
    (Language.concat (phaseLetterL p)
      (Language.concat neutralL (phaseLetterL q)))

private theorem encodePhase_phase (g : A4) :
    s3Phase (encodePhase g) =
      if a4PhaseValue g = 0 then 0 else 1 := by
  revert g
  decide

private theorem encodePhase_eq_sx_iff (g : A4) :
    encodePhase g = sx ↔ a4PhaseValue g = 1 := by
  revert g
  decide

private theorem encodePhase_eq_sy_iff (g : A4) :
    encodePhase g = sy ↔ a4PhaseValue g = 2 := by
  revert g
  decide

private theorem inverseLetterMap_neutral :
    Language.inverseLetterMap encodePhase
        (GRegex.denote S3SelfLoopHeight.neutralWordsR) = neutralL := by
  ext word
  simp only [Language.mem_inverseLetterMap_iff,
    S3SelfLoopHeight.neutralWordsR,
    FiniteAlphabet.mem_denote_onlyWhere_iff, neutralL, Set.mem_setOf_eq,
    List.mem_map]
  constructor
  · intro h g hg
    have hencoded := h (encodePhase g) ⟨g, hg, rfl⟩
    rw [encodePhase_phase] at hencoded
    split at hencoded
    · assumption
    · simp at hencoded
  · intro h b hb
    rcases hb with ⟨g, hg, rfl⟩
    rw [encodePhase_phase]
    simp [h g hg]

private theorem inverseLetterMap_sx :
    Language.inverseLetterMap encodePhase (Language.letter sx) =
      phaseLetterL 1 := by
  ext word
  simp only [Language.mem_inverseLetterMap_iff, Language.mem_letter_iff,
    List.map_eq_singleton_iff, phaseLetterL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, rfl, hg⟩
    exact ⟨g, (encodePhase_eq_sx_iff g).1 hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, rfl, (encodePhase_eq_sx_iff g).2 hg⟩

private theorem inverseLetterMap_sy :
    Language.inverseLetterMap encodePhase (Language.letter sy) =
      phaseLetterL 2 := by
  ext word
  simp only [Language.mem_inverseLetterMap_iff, Language.mem_letter_iff,
    List.map_eq_singleton_iff, phaseLetterL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, rfl, hg⟩
    exact ⟨g, (encodePhase_eq_sy_iff g).1 hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, rfl, (encodePhase_eq_sy_iff g).2 hg⟩

private theorem inverseLetterMap_pair12 :
    Language.inverseLetterMap encodePhase
        (S3FlipPairHeight.pairBlock sx sy) = phasePairBlock 1 2 := by
  unfold S3FlipPairHeight.pairBlock phasePairBlock
  rw [Language.inverseLetterMap_concat, inverseLetterMap_neutral,
    Language.inverseLetterMap_concat, inverseLetterMap_sx,
    Language.inverseLetterMap_concat, inverseLetterMap_neutral,
    inverseLetterMap_sy]

private theorem inverseLetterMap_pair21 :
    Language.inverseLetterMap encodePhase
        (S3FlipPairHeight.pairBlock sy sx) = phasePairBlock 2 1 := by
  unfold S3FlipPairHeight.pairBlock phasePairBlock
  rw [Language.inverseLetterMap_concat, inverseLetterMap_neutral,
    Language.inverseLetterMap_concat, inverseLetterMap_sy,
    Language.inverseLetterMap_concat, inverseLetterMap_neutral,
    inverseLetterMap_sx]

private noncomputable def neutralR : GRegex A4 :=
  FiniteAlphabet.onlyWhere fun g => a4PhaseValue g = 0

private noncomputable def phaseR (phase : ZMod 3) : GRegex A4 :=
  FiniteAlphabet.atomWhere fun g => a4PhaseValue g = phase

/-- Height-zero replacement for repetitions of `Z* · P₁ · Z* · P₂`. -/
noncomputable def cycle12StarR : GRegex A4 :=
  GRegex.inverseLetterMap encodePhase
    (S3FlipPairHeight.pairBlockStarR sx sy)

/-- Height-zero replacement for repetitions of `Z* · P₂ · Z* · P₁`. -/
noncomputable def cycle21StarR : GRegex A4 :=
  GRegex.inverseLetterMap encodePhase
    (S3FlipPairHeight.pairBlockStarR sy sx)

/-- The transported phase-one/two cycle denotes exactly
`(Z* · P₁ · Z* · P₂)*`. -/
theorem denote_cycle12StarR :
    GRegex.denote cycle12StarR = Language.star (phasePairBlock 1 2) := by
  rw [cycle12StarR, GRegex.denote_inverseLetterMap,
    S3FlipPairHeight.denote_pairBlockStarR sx sy (by decide) (by decide)
      (by decide), Language.inverseLetterMap_star, inverseLetterMap_pair12]

/-- The symmetric transported cycle denotes exactly
`(Z* · P₂ · Z* · P₁)*`. -/
theorem denote_cycle21StarR :
    GRegex.denote cycle21StarR = Language.star (phasePairBlock 2 1) := by
  rw [cycle21StarR, GRegex.denote_inverseLetterMap,
    S3FlipPairHeight.denote_pairBlockStarR sy sx (by decide) (by decide)
      (by decide), Language.inverseLetterMap_star, inverseLetterMap_pair21]

private noncomputable def exit1R : GRegex A4 :=
  GRegex.union
    (GRegex.concat neutralR (phaseR 2))
    (GRegex.concat neutralR
      (GRegex.concat (phaseR 1)
        (GRegex.concat neutralR (phaseR 1))))

private noncomputable def exit2R : GRegex A4 :=
  GRegex.union
    (GRegex.concat neutralR (phaseR 1))
    (GRegex.concat neutralR
      (GRegex.concat (phaseR 2)
        (GRegex.concat neutralR (phaseR 2))))

/-- Candidate height-zero expression for a complete base-cut first return:
one phase-zero letter, or one of the two alternating nonzero branches. -/
noncomputable def returnR : GRegex A4 :=
  GRegex.union (phaseR 0)
    (GRegex.union
      (GRegex.concat (phaseR 1)
        (GRegex.concat cycle12StarR exit1R))
      (GRegex.concat (phaseR 2)
        (GRegex.concat cycle21StarR exit2R)))

theorem starHeight_returnR : GRegex.starHeight returnR = 0 := by
  have h12 := GRegex.starHeight_inverseLetterMap_le encodePhase
    (S3FlipPairHeight.pairBlockStarR sx sy)
  have h21 := GRegex.starHeight_inverseLetterMap_le encodePhase
    (S3FlipPairHeight.pairBlockStarR sy sx)
  rw [S3FlipPairHeight.starHeight_pairBlockStarR] at h12 h21
  have h12zero : GRegex.starHeight cycle12StarR = 0 :=
    Nat.eq_zero_of_le_zero h12
  have h21zero : GRegex.starHeight cycle21StarR = 0 :=
    Nat.eq_zero_of_le_zero h21
  simp [returnR, exit1R, exit2R, neutralR, phaseR,
    GRegex.starHeight, h12zero, h21zero]

end A4CutComponents

/-- Once the remaining all-word grammar equality is supplied, the same
height-zero expression proves every absolute target phase at once. -/
theorem isStarFree_a4BaseCutReturnBlock_of_denote
    (hdenote : GRegex.denote A4CutComponents.returnR =
      a4BaseCutReturnBlock 0) (target : ZMod 3) :
    IsStarFree (a4BaseCutReturnBlock target) := by
  rw [a4BaseCutReturnBlock_target_independent]
  exact ⟨A4CutComponents.returnR, hdenote, by
    rw [A4CutComponents.starHeight_returnR]⟩

end GSH
