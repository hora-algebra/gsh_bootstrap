import GSH.Height.D5ArrowCoordinates

set_option autoImplicit false

namespace GSHTest

open GSH

example (start : ZMod 2) (label : D5Alphabet) (word : Word D5Alphabet) :
    d5ArrowCountFrom start 0 label word +
        d5ArrowCountFrom start 1 label word = word.count label :=
  d5ArrowCount_partition start label word

example (word : Word D5Alphabet) :
    d5BetaByArrows word =
      Finset.univ.sum fun label =>
        d5Beta label *
          ((2 : ZMod 5) *
              (d5ArrowCountFrom 0 0 label word : ZMod 5) -
            (word.count label : ZMod 5)) :=
  d5BetaByArrows_eq_sourceZero_total word

example (word : Word D5Alphabet) :
    word.prod = 1 ↔
      (word.map d5Phase).sum = 0 ∧ d5BetaByArrows word = 0 :=
  d5_prod_eq_one_iff_arrowCounts word

example : fullIdentityFiber D5Alphabet = d5ArrowCoordinateFiber :=
  fullIdentityFiber_d5_eq_arrowCoordinateFiber

end GSHTest
