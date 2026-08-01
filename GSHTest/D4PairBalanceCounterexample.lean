import GSH.Height.ArrowCounting
import GSH.Height.S3ArrowArithmetic

set_option autoImplicit false

namespace GSHTest.D4PairBalanceCounterexample

open GSH
open GSH.S3ArrowArithmetic

def flipPhase (_ : Bool) : ZMod 2 := 1

def sourceZeroCount (label : Bool) (word : Word Bool) : Nat :=
  ArrowCounting.arrowCountFrom (ArrowCounting.c2Step flipPhase)
    0 0 label word

/-- The direct mod-four analogue of the signed pair balance used for `S₃`. -/
def pairBalance4 (label : Bool) (word : Word Bool) : ZMod 4 :=
  ∑ other : Bool,
    if other = label then 0
    else
      (pairCountOf label other word : ZMod 4) -
        (pairCountOf other label word : ZMod 4)

def short : Word Bool := []
def long : Word Bool := [true, true, true, true]

/-- The old mod-four features agree on the exact counterexample. -/
example :
    ((short.count true : ZMod 4), pairBalance4 true short) =
      ((long.count true : ZMod 4), pairBalance4 true long) := by
  decide

/-- The arrow residues nevertheless differ by two. -/
example :
    (sourceZeroCount true short : ZMod 4) = 0 ∧
    (sourceZeroCount true long : ZMod 4) = 2 ∧
    (0 : ZMod 4) ≠ 2 := by
  decide

/-- The obstruction is precisely non-injectivity of doubling modulo four. -/
example : (2 * (0 : ZMod 4)) = 2 * (2 : ZMod 4) ∧
    (0 : ZMod 4) ≠ 2 := by
  decide

/-- Lifting the doubled coordinate to modulus eight restores injectivity. -/
example : Function.Injective
    (fun residue : Fin 4 => (2 * residue.1 : ZMod 8)) := by
  decide

end GSHTest.D4PairBalanceCounterexample
