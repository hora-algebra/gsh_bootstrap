import GSH.Height.ArrowCounting

set_option autoImplicit false

namespace GSHTest

open GSH

universe u v

/-! The word-level arrow count composes across concatenation, with the second
word started in the state reached after the first. -/

example {α : Type u} {σ : Type v} [DecidableEq α] [DecidableEq σ]
    (step : σ → α → σ) (start source : σ) (label : α) (u v : Word α) :
    ArrowCounting.arrowCountFrom step start source label (u ++ v) =
      ArrowCounting.arrowCountFrom step start source label u +
        ArrowCounting.arrowCountFrom step
          (ArrowCounting.runFrom step start u) source label v :=
  ArrowCounting.arrowCountFrom_append step start source label u v

/-! In the `C₂` specialization, each letter transition is an involution and
the reached state is the sum of the input phases. -/

example {α : Type u} (phase : α → ZMod 2) (state : ZMod 2) (a : α) :
    ArrowCounting.c2Step phase (ArrowCounting.c2Step phase state a) a = state :=
  ArrowCounting.c2Step_twice phase state a

example {α : Type u} (phase : α → ZMod 2) (start : ZMod 2) (word : Word α) :
    ArrowCounting.c2RunFrom phase start word = start + (word.map phase).sum :=
  ArrowCounting.c2RunFrom_eq phase start word

end GSHTest
