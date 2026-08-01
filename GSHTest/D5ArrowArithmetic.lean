import GSH.Height.D5ArrowArithmetic

set_option autoImplicit false

namespace GSHTest

open GSH GSH.D5ArrowArithmetic

example (label : D5Alphabet) (hlabel : d5Phase label = 1)
    (word : Word D5Alphabet) (target : Fin 5)
    (hphase : (word.map d5Phase).sum = 0) :
    d5ArrowCountFrom 0 0 label word % 5 = target.1 ↔
      d5ArrowFingerprint5 label hlabel word =
        (2 : ZMod 5) * (target.1 : ZMod 5) :=
  d5ArrowCount_mod_five_iff_features_mod_five
    label hlabel word target hphase

end GSHTest
