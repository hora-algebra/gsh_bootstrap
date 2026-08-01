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

end GSHTest
