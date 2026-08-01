import GSH.Height.D4ArrowArithmetic

set_option autoImplicit false

namespace GSHTest

open GSH
open GSH.ArrowCounting
open GSH.S3ArrowArithmetic
open GSH.D4ArrowArithmetic

/-- Doubling embeds all four arrow residues in `ZMod 8`. -/
example : Function.Injective
    (fun residue : Fin 4 =>
      (2 : ZMod 8) * (residue.1 : ZMod 8)) := by
  intro left right h
  exact d4TwoMulFin4_injective left right h

/-- Exact mod-eight consumer on the actual full `D₄` alphabet. -/
example (label : D4Alphabet) (hlabel : d4Phase label = 1)
    (word : Word D4Alphabet) (hphase : (word.map d4Phase).sum = 0) :
    (2 : ZMod 8) *
        (d4ArrowCountFrom 0 0 label word : ZMod 8) =
      (word.count label : ZMod 8) +
        d4PairBalance8 ⟨label, hlabel⟩ (d4PhaseOneSubword word) := by
  exact two_mul_d4Arrow_eq_count_add_pairBalance label hlabel word hphase

/-- The identity reconstructs the source-zero arrow residue modulo four. -/
example (label : D4Alphabet) (hlabel : d4Phase label = 1)
    (word : Word D4Alphabet) (target : Fin 4)
    (hphase : (word.map d4Phase).sum = 0) :
    d4ArrowCountFrom 0 0 label word % 4 = target.1 ↔
      d4ArrowFingerprint8 label hlabel word =
        (2 : ZMod 8) * (target.1 : ZMod 8) := by
  exact d4ArrowCount_mod_four_iff_features_mod_eight
    label hlabel word target hphase

end GSHTest
