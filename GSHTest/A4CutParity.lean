import GSH.Height.A4CutParity

set_option autoImplicit false

open GSH

example (target : ZMod 3) :
    a4BaseCutOdd target = a4BaseCutOddFormula target :=
  a4BaseCutOdd_eq_formula target

example (target : ZMod 3) :
    a4BaseCutEven target = a4BaseCutEvenFormula target :=
  a4BaseCutEven_eq_formula target

example (target : ZMod 3)
    (hO : IsStarFree (a4BaseCutInitialBlock target))
    (hX : IsStarFree (a4BaseCutReturnBlock target))
    (hV : IsStarFree (a4BaseCutTail target))
    (hV0 : IsStarFree (a4BaseCutInitialTail target)) :
    HasHeightAtMost (a4BaseCutOdd target) 1 ∧
      HasHeightAtMost (a4BaseCutEven target) 1 :=
  hasHeightAtMost_a4BaseCutParity target hO hX hV hV0
