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
language `P = D ∪ C B⁺ C`, where `D = B \ {label}`. -/
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

/-- A return block cannot be the counted singleton. -/
omit [DecidableEq α] in
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

end S3ArrowResidue

end GSH
