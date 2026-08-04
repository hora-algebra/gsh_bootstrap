import GSH.Challenges.GeneralizedStarHeight
import Mathlib.Data.ZMod.Basic

/-!
# Runs and labelled-arrow counts on words

This file isolates the word-level bookkeeping used by the two-state route in
Pin--Straubing--Thérien's construction.  Given a deterministic transition
function, `arrowCountFrom` counts occurrences of one labelled arrow: the
current state is `source` and the next input letter is `label`.

No generalized-star-height conclusion is made here.  The missing step is to
construct height-one expressions for residues of these counts in the relevant
two-state automaton.
-/

set_option autoImplicit false

namespace GSH

universe u v

namespace ArrowCounting

variable {α : Type u} {σ : Type v}

/-- State reached after reading a word from `start`. -/
def runFrom (step : σ → α → σ) (start : σ) (word : Word α) : σ :=
  word.foldl step start

@[simp]
theorem runFrom_nil (step : σ → α → σ) (start : σ) :
    runFrom step start [] = start := rfl

@[simp]
theorem runFrom_cons (step : σ → α → σ) (start : σ) (a : α) (word : Word α) :
    runFrom step start (a :: word) = runFrom step (step start a) word := rfl

/-- Running a concatenation first runs its left word, then its right word. -/
theorem runFrom_append (step : σ → α → σ) (start : σ) (u v : Word α) :
    runFrom step start (u ++ v) = runFrom step (runFrom step start u) v := by
  simp [runFrom, List.foldl_append]

section

variable [DecidableEq α] [DecidableEq σ]

/-- Number of times a run takes the arrow whose source is `source` and whose
input label is `label`.  The target is determined by `step`. -/
def arrowCountFrom (step : σ → α → σ) : σ → σ → α → Word α → Nat
  | _, _, _, [] => 0
  | current, source, label, a :: word =>
      (if current = source ∧ a = label then 1 else 0) +
        arrowCountFrom step (step current a) source label word

@[simp]
theorem arrowCountFrom_nil (step : σ → α → σ) (start source : σ) (label : α) :
    arrowCountFrom step start source label [] = 0 := rfl

@[simp]
theorem arrowCountFrom_cons (step : σ → α → σ) (start source : σ)
    (label a : α) (word : Word α) :
    arrowCountFrom step start source label (a :: word) =
      (if start = source ∧ a = label then 1 else 0) +
        arrowCountFrom step (step start a) source label word := rfl

/-- Arrow counts split over concatenation, with the run on the right starting
in the state reached after the left word. -/
theorem arrowCountFrom_append (step : σ → α → σ) (start source : σ)
    (label : α) (u v : Word α) :
    arrowCountFrom step start source label (u ++ v) =
      arrowCountFrom step start source label u +
        arrowCountFrom step (runFrom step start u) source label v := by
  induction u generalizing start with
  | nil => simp
  | cons a u ih =>
      simp [ih, Nat.add_assoc]

end

/-! ### The two-state quotient used for `S₃` -/

/-- Reading a letter adds its `C₂ = ZMod 2` phase to the current state. -/
def c2Step (phase : α → ZMod 2) (state : ZMod 2) (a : α) : ZMod 2 :=
  state + phase a

/-- Every one-letter transition of the `C₂` action is an involution.  This is
the first point in the word-level development that uses order two. -/
theorem c2Step_twice (phase : α → ZMod 2) (state : ZMod 2) (a : α) :
    c2Step phase (c2Step phase state a) a = state := by
  exact CharTwo.add_cancel_right state (phase a)

/-- State reached by the additive `C₂` action after reading a word. -/
def c2RunFrom (phase : α → ZMod 2) (start : ZMod 2) (word : Word α) : ZMod 2 :=
  runFrom (c2Step phase) start word

/-- The `C₂` run is exactly the starting state plus the sum of the phases of
the letters read. -/
theorem c2RunFrom_eq (phase : α → ZMod 2) (start : ZMod 2) (word : Word α) :
    c2RunFrom phase start word = start + (word.map phase).sum := by
  induction word generalizing start with
  | nil => simp [c2RunFrom]
  | cons a word ih =>
      change c2RunFrom phase (c2Step phase start a) word =
        start + (phase a + (word.map phase).sum)
      rw [ih]
      exact add_assoc start (phase a) (word.map phase).sum

end ArrowCounting

end GSH
