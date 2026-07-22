import GSH.Language.Basic

/-!
# Deterministic finite automata

The core definition does not assume finiteness; finiteness is added by typeclass
hypotheses in algorithms and theorems that need it.
-/

set_option autoImplicit false

namespace GSH

universe u v

structure DFA (α : Type u) (σ : Type v) where
  step : σ → α → σ
  start : σ
  accept : Set σ

namespace DFA

variable {α : Type u} {σ : Type v}

/-- Run an automaton from an arbitrary state. -/
def run (M : DFA α σ) : σ → Word α → σ
  | q, [] => q
  | q, a :: w => run M (M.step q a) w

@[simp] theorem run_nil (M : DFA α σ) (q : σ) : M.run q [] = q := rfl

@[simp] theorem run_cons (M : DFA α σ) (q : σ) (a : α) (w : Word α) :
    M.run q (a :: w) = M.run (M.step q a) w := rfl

/-- Running a concatenation factors through the state reached by the prefix. -/
theorem run_append (M : DFA α σ) (q : σ) (u v : Word α) :
    M.run q (u ++ v) = M.run (M.run q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
      simpa using ih (q := M.step q a)

/-- The language accepted from the designated start state. -/
def language (M : DFA α σ) : Language α :=
  {w | M.run M.start w ∈ M.accept}

@[simp] theorem mem_language_iff (M : DFA α σ) (w : Word α) :
    w ∈ M.language ↔ M.run M.start w ∈ M.accept := by
  rfl

end DFA
end GSH
