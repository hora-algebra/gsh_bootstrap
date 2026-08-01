import GSH.Height.A4PointReturn

/-! Consumer checks and ground route tests for the `A₄` point-return DFA. -/

set_option autoImplicit false

open GSH

example (g : A4) :
    a4VectorPart g = 1 ↔ g.1 (3 : Fin 4) = 3 :=
  a4VectorPart_eq_one_iff_fix3 g

example : a4V4CoordinateFiber = a4PointReturn :=
  a4V4CoordinateFiber_eq_pointReturn

example (q : Fin 4) (word : Word A4) :
    a4PointDFA.run q word = word.prod⁻¹.1 q :=
  a4PointDFA_run q word

example : a4PointDFA.language = a4PointReturn :=
  a4PointDFA_language

example : a4V4CoordinateFiber = a4PointDFA.language :=
  a4V4CoordinateFiber_eq_pointDFA

example (h : HasHeightAtMost a4PointDFA.language 1) :
    HeightOneForGroup A4 :=
  heightOne_A4_of_pointDFA h

/-! The following ground facts preserve two failed simplifications. -/

theorem a4T_cycle_off_base :
    a4T.1 (0 : Fin 4) = 1 ∧
    a4T.1 (1 : Fin 4) = 2 ∧
    a4T.1 (2 : Fin 4) = 0 ∧
    a4T.1 (3 : Fin 4) = 3 := by
  decide

def a4TestV : A4 :=
  ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3, by simp⟩

/-- Ordinary letter counts do not determine the return condition. -/
theorem a4_same_counts_different_return :
    ([a4TestV, a4T, a4TestV] : Word A4).count a4TestV =
        ([a4TestV, a4TestV, a4T] : Word A4).count a4TestV ∧
    ([a4TestV, a4T, a4TestV] : Word A4).count a4T =
        ([a4TestV, a4TestV, a4T] : Word A4).count a4T ∧
    ([a4TestV, a4T, a4TestV] : Word A4) ∉ a4PointReturn ∧
    ([a4TestV, a4TestV, a4T] : Word A4) ∈ a4PointReturn := by
  change
    ([a4TestV, a4T, a4TestV] : Word A4).count a4TestV =
        ([a4TestV, a4TestV, a4T] : Word A4).count a4TestV ∧
    ([a4TestV, a4T, a4TestV] : Word A4).count a4T =
        ([a4TestV, a4TestV, a4T] : Word A4).count a4T ∧
    ¬ (([a4TestV, a4T, a4TestV] : Word A4).prod.1 (3 : Fin 4) = 3) ∧
    (([a4TestV, a4TestV, a4T] : Word A4).prod.1 (3 : Fin 4) = 3)
  decide
