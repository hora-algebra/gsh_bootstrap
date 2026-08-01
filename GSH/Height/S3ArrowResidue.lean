import GSH.Height.S3FullFiber

/-!
# Return blocks for the self-loop part of the `C₂` arrow construction

This file isolates the word-level block `P` used in the proof of
Pin--Straubing--Thérien, Proposition 6.6, specialized to two states.  For a
self-loop letter `label`, a `P`-block is either

* one other phase-zero letter, or
* a phase-one letter, followed by phase-zero letters, followed by a
  phase-one letter.

Thus every `P`-block returns from state zero to state zero without using the
labelled self-loop at state zero.  A factorization into singleton `[label]`
blocks and `P`-blocks therefore counts exactly the required labelled arrows.

This is word-level bookkeeping only.  The height-one step still requires the
Transfer Lemma for the prefix code `{label} ∪ P`.
-/

set_option autoImplicit false

namespace GSH

universe u

namespace S3ArrowResidue

variable {α : Type u} [DecidableEq α]

/-- Every letter of the word fixes the two `C₂` states. -/
def IsPhaseZeroWord (phase : α → ZMod 2) (word : Word α) : Prop :=
  ∀ a ∈ word, phase a = 0

/-- The two-state specialization of PST Proposition 6.6's return-block
language `P = D ∪ C B* C`, where `D = B \ {label}`. -/
def SelfLoopReturnBlock (phase : α → ZMod 2) (label : α) (word : Word α) : Prop :=
  (∃ d, phase d = 0 ∧ d ≠ label ∧ word = [d]) ∨
    ∃ c₁ middle c₂, phase c₁ = 1 ∧ IsPhaseZeroWord phase middle ∧
      phase c₂ = 1 ∧ word = c₁ :: middle ++ [c₂]

/-- A code block is either the counted singleton or an uncounted return block. -/
def SelfLoopCodeBlock (phase : α → ZMod 2) (label : α) (word : Word α) : Prop :=
  word = [label] ∨ SelfLoopReturnBlock phase label word

omit [DecidableEq α] in
private theorem run_phaseZero (phase : α → ZMod 2) (start : ZMod 2)
    (word : Word α) (hword : IsPhaseZeroWord phase word) :
    ArrowCounting.runFrom (ArrowCounting.c2Step phase) start word = start := by
  induction word generalizing start with
  | nil => rfl
  | cons a word ih =>
      have ha : phase a = 0 := hword a (by simp)
      have hw : IsPhaseZeroWord phase word := by
        intro b hb
        exact hword b (by simp [hb])
      simp [ArrowCounting.runFrom_cons, ArrowCounting.c2Step, ha, ih start hw]

omit [DecidableEq α] in
private theorem zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

omit [DecidableEq α] in
private theorem exists_first_phaseOne (phase : α → ZMod 2) (word : Word α)
    (h : ∃ a ∈ word, phase a = 1) :
    ∃ middle c tail, word = middle ++ c :: tail ∧
      IsPhaseZeroWord phase middle ∧ phase c = 1 := by
  induction word with
  | nil => simp at h
  | cons a word ih =>
      by_cases ha : phase a = 1
      · exact ⟨[], a, word, by simp, by simp [IsPhaseZeroWord], ha⟩
      · have ha0 : phase a = 0 := (zmod2_eq_zero_or_one (phase a)).resolve_right ha
        have htail : ∃ b ∈ word, phase b = 1 := by
          rcases h with ⟨b, hb, hb1⟩
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact absurd hb1 ha
          · exact ⟨b, hb, hb1⟩
        obtain ⟨middle, c, tail, hsplit, hmiddle, hc⟩ := ih htail
        refine ⟨a :: middle, c, tail, ?_, ?_, hc⟩
        · simp [hsplit]
        · intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact ha0
          · exact hmiddle b hb

private theorem count_from_one_phaseZero (phase : α → ZMod 2) (label : α)
    (word : Word α) (hword : IsPhaseZeroWord phase word) :
    ArrowCounting.arrowCountFrom (ArrowCounting.c2Step phase) 1 0 label word = 0 := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      have ha : phase a = 0 := hword a (by simp)
      have hw : IsPhaseZeroWord phase word := by
        intro b hb
        exact hword b (by simp [hb])
      simp [ArrowCounting.arrowCountFrom_cons, ArrowCounting.c2Step, ha, ih hw,
        show (1 : ZMod 2) ≠ 0 by decide]

omit [DecidableEq α] in
/-- A `P`-block returns the phase run from zero to zero. -/
theorem run_selfLoopReturnBlock (phase : α → ZMod 2) (label : α) (word : Word α)
    (hword : SelfLoopReturnBlock phase label word) :
    ArrowCounting.runFrom (ArrowCounting.c2Step phase) 0 word = 0 := by
  rcases hword with ⟨d, hd, -, rfl⟩ | ⟨c₁, middle, c₂, hc₁, hmiddle, hc₂, rfl⟩
  · simp [ArrowCounting.runFrom_cons, ArrowCounting.c2Step, hd]
  · rw [show c₁ :: middle ++ [c₂] = [c₁] ++ middle ++ [c₂] by simp]
    rw [ArrowCounting.runFrom_append, ArrowCounting.runFrom_append]
    simp [ArrowCounting.c2Step, hc₁, hc₂, run_phaseZero phase 1 middle hmiddle,
      show (1 : ZMod 2) + 1 = 0 by decide]

/-- A `P`-block takes the labelled self-loop at source zero zero times. -/
theorem count_selfLoopReturnBlock (phase : α → ZMod 2) (label : α) (word : Word α)
    (hlabel : phase label = 0) (hword : SelfLoopReturnBlock phase label word) :
    ArrowCounting.arrowCountFrom (ArrowCounting.c2Step phase) 0 0 label word = 0 := by
  rcases hword with ⟨d, hd, hdl, rfl⟩ | ⟨c₁, middle, c₂, hc₁, hmiddle, hc₂, rfl⟩
  · simp [ArrowCounting.arrowCountFrom_cons, ArrowCounting.c2Step, hd, hdl]
  · have hc₁l : c₁ ≠ label := by
      intro h
      subst h
      rw [hlabel] at hc₁
      exact zero_ne_one hc₁
    rw [show c₁ :: middle ++ [c₂] = [c₁] ++ middle ++ [c₂] by simp]
    rw [ArrowCounting.arrowCountFrom_append, ArrowCounting.arrowCountFrom_append]
    simp [ArrowCounting.c2Step, hc₁, hc₂, hc₁l,
      run_phaseZero phase 1 middle hmiddle,
      count_from_one_phaseZero phase label middle hmiddle,
      show (1 : ZMod 2) ≠ 0 by decide]

omit [DecidableEq α] in
/-- A return block cannot be the counted singleton. -/
theorem selfLoopReturnBlock_ne_singleton (phase : α → ZMod 2) (label : α)
    (word : Word α) (hlabel : phase label = 0)
    (hword : SelfLoopReturnBlock phase label word) : word ≠ [label] := by
  rcases hword with ⟨d, -, hdl, rfl⟩ | ⟨c₁, middle, c₂, hc₁, -, -, rfl⟩
  · simpa using hdl
  · intro h
    have hc₁l : c₁ = label := by simpa using congrArg List.head? h
    subst c₁
    rw [hlabel] at hc₁
    exact zero_ne_one hc₁

omit [DecidableEq α] in
/-- Concatenating code blocks returns the phase run to zero. -/
theorem run_join_codeBlocks (phase : α → ZMod 2) (label : α)
    (pieces : List (Word α)) (hlabel : phase label = 0)
    (hpieces : ∀ piece ∈ pieces, SelfLoopCodeBlock phase label piece) :
    ArrowCounting.runFrom (ArrowCounting.c2Step phase) 0 pieces.flatten = 0 := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
      have hp := hpieces piece (by simp)
      have hps : ∀ p ∈ pieces, SelfLoopCodeBlock phase label p := by
        intro p hp'
        exact hpieces p (by simp [hp'])
      rw [List.flatten_cons, ArrowCounting.runFrom_append]
      rcases hp with rfl | hp
      · simpa [ArrowCounting.c2Step, hlabel] using ih hps
      · rw [run_selfLoopReturnBlock phase label piece hp]
        exact ih hps

/-- On a factorization by `{[label]} ∪ P`, the labelled-arrow count is
exactly the number of singleton `[label]` code blocks. -/
theorem count_join_codeBlocks (phase : α → ZMod 2) (label : α)
    (pieces : List (Word α)) (hlabel : phase label = 0)
    (hpieces : ∀ piece ∈ pieces, SelfLoopCodeBlock phase label piece) :
    ArrowCounting.arrowCountFrom (ArrowCounting.c2Step phase) 0 0 label pieces.flatten =
      pieces.count [label] := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
      have hp := hpieces piece (by simp)
      have hps : ∀ p ∈ pieces, SelfLoopCodeBlock phase label p := by
        intro p hp'
        exact hpieces p (by simp [hp'])
      rw [List.flatten_cons, ArrowCounting.arrowCountFrom_append]
      rcases hp with rfl | hp
      · simp [ArrowCounting.arrowCountFrom_cons, ArrowCounting.c2Step, hlabel,
          ih hps, Nat.add_comm]
      · have hne := selfLoopReturnBlock_ne_singleton phase label piece hlabel hp
        simp [count_selfLoopReturnBlock phase label piece hlabel hp,
          run_selfLoopReturnBlock phase label piece hp, ih hps, hne]

private theorem exists_codeBlockFactorization_of_length
    (phase : α → ZMod 2) (label : α) (_hlabel : phase label = 0) :
    ∀ n : Nat, ∀ word : Word α, word.length = n →
      ArrowCounting.runFrom (ArrowCounting.c2Step phase) 0 word = 0 →
      ∃ pieces : List (Word α),
        (∀ piece ∈ pieces, SelfLoopCodeBlock phase label piece) ∧
          pieces.flatten = word := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih word hlength hrun
  cases word with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons a rest =>
      by_cases ha0 : phase a = 0
      · have hrunRest :
            ArrowCounting.runFrom (ArrowCounting.c2Step phase) 0 rest = 0 := by
          simpa [ArrowCounting.runFrom_cons, ArrowCounting.c2Step, ha0] using hrun
        have hrestLength : rest.length < n := by
          rw [← hlength]
          simp
        obtain ⟨pieces, hpieces, hflat⟩ :=
          ih rest.length hrestLength rest rfl hrunRest
        by_cases halabel : a = label
        · subst a
          refine ⟨[label] :: pieces, ?_, ?_⟩
          · intro piece hpiece
            simp only [List.mem_cons] at hpiece
            rcases hpiece with rfl | hpiece
            · exact Or.inl rfl
            · exact hpieces piece hpiece
          · simp [hflat]
        · refine ⟨[a] :: pieces, ?_, ?_⟩
          · intro piece hpiece
            simp only [List.mem_cons] at hpiece
            rcases hpiece with rfl | hpiece
            · exact Or.inr (Or.inl ⟨a, ha0, halabel, rfl⟩)
            · exact hpieces piece hpiece
          · simp [hflat]
      · have ha1 : phase a = 1 := (zmod2_eq_zero_or_one (phase a)).resolve_left ha0
        have hrunRest :
            ArrowCounting.runFrom (ArrowCounting.c2Step phase) 1 rest = 0 := by
          simpa [ArrowCounting.runFrom_cons, ArrowCounting.c2Step, ha1] using hrun
        have hcontains : ∃ c ∈ rest, phase c = 1 := by
          by_contra hnone
          have hzero : IsPhaseZeroWord phase rest := by
            intro b hb
            rcases zmod2_eq_zero_or_one (phase b) with hb0 | hb1
            · exact hb0
            · exact False.elim (hnone ⟨b, hb, hb1⟩)
          have hone := run_phaseZero phase 1 rest hzero
          rw [hrunRest] at hone
          exact zero_ne_one hone
        obtain ⟨middle, c, tail, rfl, hmiddle, hc⟩ :=
          exists_first_phaseOne phase rest hcontains
        have hrunTail :
            ArrowCounting.runFrom (ArrowCounting.c2Step phase) 0 tail = 0 := by
          rw [ArrowCounting.runFrom_append] at hrunRest
          simp [run_phaseZero phase 1 middle hmiddle, ArrowCounting.c2Step, hc,
            show (1 : ZMod 2) + 1 = 0 by decide] at hrunRest
          exact hrunRest
        have htailLength : tail.length < n := by
          rw [← hlength]
          simp only [List.length_cons, List.length_append]
          omega
        obtain ⟨pieces, hpieces, hflat⟩ :=
          ih tail.length htailLength tail rfl hrunTail
        refine ⟨(a :: middle ++ [c]) :: pieces, ?_, ?_⟩
        · intro piece hpiece
          simp only [List.mem_cons] at hpiece
          rcases hpiece with rfl | hpiece
          · exact Or.inr (Or.inr ⟨a, middle, c, ha1, hmiddle, hc, rfl⟩)
          · exact hpieces piece hpiece
        · simp [hflat]

/-- Every word whose `C₂` run returns to zero admits the complete PST
factorization into counted singleton blocks and uncounted `P`-blocks. -/
theorem exists_codeBlockFactorization (phase : α → ZMod 2) (label : α)
    (word : Word α) (hlabel : phase label = 0)
    (hrun : ArrowCounting.runFrom (ArrowCounting.c2Step phase) 0 word = 0) :
    ∃ pieces : List (Word α),
      (∀ piece ∈ pieces, SelfLoopCodeBlock phase label piece) ∧
        pieces.flatten = word :=
  exists_codeBlockFactorization_of_length phase label hlabel word.length word rfl hrun

end S3ArrowResidue

end GSH
