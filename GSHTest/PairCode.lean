import GSH.Height.PairCode

/-!
# Compile-time acceptance tests for pair-code bookkeeping

The examples retain universal quantification over the label and word.  They
exercise the theorem interfaces rather than checking a finite collection of
sample words.
-/

set_option autoImplicit false

namespace GSHTest

open GSH GSH.ArrowCounting GSH.PairCode

example (label : Bool) (word : Word Bool) (hEven : word.length % 2 = 0) :
    arrowCountFrom allFlipStep 0 0 label word =
      pairCount label false word + pairCount label true word :=
  arrowCount_allFlip_zero_even label word hEven

example (word : Word Bool) (hEven : word.length % 2 = 0) :
    word.count false =
      2 * pairCount false false word +
        pairCount false true word + pairCount true false word :=
  count_false_eq_pairCounts word hEven

end GSHTest
