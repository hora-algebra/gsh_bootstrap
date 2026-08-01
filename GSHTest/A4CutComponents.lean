import GSH.Height.A4CutComponents

set_option autoImplicit false

open GSH

example (target : ZMod 3) :
    a4BaseCutReturnBlock target = a4BaseCutReturnBlock 0 :=
  a4BaseCutReturnBlock_target_independent target

example (start target : ZMod 3) (word : Word A4) :
    a4BaseCutCountFrom start target word =
      (a4PhaseTraceFrom start word).count target :=
  a4BaseCutCountFrom_eq_traceCount start target word

example : GRegex.starHeight A4CutComponents.returnR = 0 :=
  A4CutComponents.starHeight_returnR

example (g : A4) (word : Word A4) :
    g :: word ∈ a4BaseCutFirstReturnFromZero 1 ↔
      (a4PhaseValue g = 0 ∧
        word ∈ a4BaseCutFirstReturnFromZero 1) ∨
      (a4PhaseValue g = 1 ∧
        word ∈ a4BaseCutFirstReturnFromZero 2) ∨
      (a4PhaseValue g = 2 ∧ word = []) :=
  a4BaseCutFirstReturnFromZero_one_cons g word

example (g : A4) (word : Word A4) :
    g :: word ∈ a4BaseCutFirstReturnFromZero 2 ↔
      (a4PhaseValue g = 0 ∧
        word ∈ a4BaseCutFirstReturnFromZero 2) ∨
      (a4PhaseValue g = 2 ∧
        word ∈ a4BaseCutFirstReturnFromZero 1) ∨
      (a4PhaseValue g = 1 ∧ word = []) :=
  a4BaseCutFirstReturnFromZero_two_cons g word

example (g : A4) (word : Word A4) :
    g :: word ∈ a4BaseCutReturnBlock 0 ↔
      (a4PhaseValue g = 0 ∧ word = []) ∨
      (a4PhaseValue g = 1 ∧
        word ∈ a4BaseCutFirstReturnFromZero 1) ∨
      (a4PhaseValue g = 2 ∧
        word ∈ a4BaseCutFirstReturnFromZero 2) :=
  a4BaseCutReturnBlock_zero_cons g word

/-- Consumer-first boundary: the remaining all-word denotation equality is
the only premise between the concrete expression and all three targets. -/
example
    (hdenote : GRegex.denote A4CutComponents.returnR =
      a4BaseCutReturnBlock 0) (target : ZMod 3) :
    IsStarFree (a4BaseCutReturnBlock target) :=
  isStarFree_a4BaseCutReturnBlock_of_denote hdenote target
