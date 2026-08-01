import GSH.Groups.A4

/-!
# The `A₄` residual fibre as a four-state return language

The residual `V₄` coordinate vanishes exactly when the product fixes the
fourth point.  This identifies the remaining full-alphabet obligation with
the language of an explicit four-state DFA.
-/

set_option autoImplicit false

namespace GSH

/-- The residual coordinate vanishes exactly when the permutation fixes the
fourth point, i.e. belongs to the chosen `C₃` complement. -/
theorem a4VectorPart_eq_one_iff_fix3 (g : A4) :
    a4VectorPart g = 1 ↔ g.1 (3 : Fin 4) = 3 := by
  revert g
  decide

/-- The residual language is the return language of the natural four-state
action of `A₄` on `Fin 4`. -/
def a4PointReturn : Language A4 :=
  {word | word.prod.1 (3 : Fin 4) = 3}

theorem a4V4CoordinateFiber_eq_pointReturn :
    a4V4CoordinateFiber = a4PointReturn := by
  ext word
  exact a4VectorPart_eq_one_iff_fix3 word.prod

/-- Four-state DFA whose state is the inverse image of the base point under
the prefix product. -/
def a4PointDFA : DFA A4 (Fin 4) where
  step q g := g.1.symm q
  start := 3
  accept := {3}

theorem a4PointDFA_run (q : Fin 4) (word : Word A4) :
    a4PointDFA.run q word = word.prod⁻¹.1 q := by
  induction word generalizing q with
  | nil => rfl
  | cons g word ih =>
      rw [DFA.run_cons]
      change a4PointDFA.run (g.1.symm q) word = _
      rw [ih]
      rfl

theorem a4PointDFA_language :
    a4PointDFA.language = a4PointReturn := by
  ext word
  rw [DFA.mem_language_iff, a4PointDFA_run]
  change word.prod⁻¹.1 (3 : Fin 4) = 3 ↔ word.prod.1 3 = 3
  constructor
  · intro h
    have := congrArg (word.prod.1) h
    simpa using this.symm
  · intro h
    have := congrArg (word.prod⁻¹.1) h
    simpa using this.symm

/-- Exact identification of the remaining `V₄` fibre with the explicit DFA
language. -/
theorem a4V4CoordinateFiber_eq_pointDFA :
    a4V4CoordinateFiber = a4PointDFA.language :=
  a4V4CoordinateFiber_eq_pointReturn.trans a4PointDFA_language.symm

/-- Exact consumer: a height-one certificate for the four-state return DFA
closes the full `A₄` theorem. -/
theorem heightOne_A4_of_pointDFA
    (h : HasHeightAtMost a4PointDFA.language 1) :
    HeightOneForGroup A4 := by
  apply heightOneForGroup_of_fullIdentityFiber
  apply heightOne_fullIdentityFiber_A4_of_v4
  exact h.congr a4V4CoordinateFiber_eq_pointDFA.symm

end GSH
