import GSH.Height.D4ArrowCoordinates

set_option autoImplicit false

namespace GSHTest

open GSH

/-- The two prefix source states partition all occurrences of a label. -/
example (start : ZMod 2) (label : D4Alphabet) (word : Word D4Alphabet) :
    d4ArrowCountFrom start 0 label word +
        d4ArrowCountFrom start 1 label word =
      word.count label := by
  exact d4ArrowCount_partition start label word

/-- Prefix arrow counts reconstruct the signed `ZMod 4` coordinate. -/
example (word : Word D4Alphabet) :
    d4Beta word.prod = d4BetaByArrows word := by
  exact d4Beta_prod_eq_arrowCounts word

/-- Direct consumer form used by the final finite Boolean assembly. -/
example (word : Word D4Alphabet) :
    d4BetaByArrows word =
      Finset.univ.sum fun label =>
        d4Beta label *
          ((2 : ZMod 4) *
              (d4ArrowCountFrom 0 0 label word : ZMod 4) -
            (word.count label : ZMod 4)) := by
  exact d4BetaByArrows_eq_sourceZero_total word

/-- Exact full-alphabet identity fibre in prefix arrow coordinates. -/
example :
    fullIdentityFiber D4Alphabet = d4ArrowCoordinateFiber := by
  exact fullIdentityFiber_d4_eq_arrowCoordinateFiber

end GSHTest
