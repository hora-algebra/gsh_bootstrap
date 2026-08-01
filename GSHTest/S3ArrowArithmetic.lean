import GSH.Height.S3ArrowArithmetic
import GSH.Height.S3FullFiber

set_option autoImplicit false

namespace GSHTest

open GSH
open GSH.ArrowCounting
open GSH.S3ArrowArithmetic

local instance : BEq S3PhaseOne := instBEqOfDecidableEq

/-- Compile-time acceptance for the exact phase-one identity required by the
`S₃` moving-edge route. -/
example (label : S3PhaseOne) (word : Word S3PhaseOne)
    (hEven : word.length % 2 = 0) :
    (2 : ZMod 3) *
        (arrowCountFrom allFlipStepOf 0 0 label word : ZMod 3) =
      (word.count label : ZMod 3) +
        ∑ other : S3PhaseOne,
          if other = label then 0
          else
            (pairCountOf label other word : ZMod 3) -
              (pairCountOf other label word : ZMod 3) := by
  simpa [pairBalance] using
    two_mul_evenArrow_eq_count_add_pairBalance label word hEven

example (word : Word S3Alphabet) :
    (phaseOneSubword word).length % 2 = 0 ↔
      (word.map s3Phase).sum = 0 :=
  phaseOneSubword_even_iff_phase_sum_zero word

example (label : S3Alphabet) (hlabel : s3Phase label = 1)
    (word : Word S3Alphabet) :
    (phaseOneSubword word).count ⟨label, hlabel⟩ = word.count label :=
  count_phaseOneSubword label hlabel word

example (label : S3Alphabet) (hlabel : s3Phase label = 1)
    (word : Word S3Alphabet) :
    s3ArrowCountFrom 0 0 label word =
      arrowCountFrom allFlipStepOf 0 0 ⟨label, hlabel⟩
        (phaseOneSubword word) :=
  s3ArrowCountFrom_eq_phaseOneSubword label hlabel word

/-- Exact consumer over the original six-letter `S₃` alphabet. -/
example (label : S3Alphabet) (hlabel : s3Phase label = 1)
    (word : Word S3Alphabet) (hphase : (word.map s3Phase).sum = 0) :
    (2 : ZMod 3) * (s3ArrowCountFrom 0 0 label word : ZMod 3) =
      (word.count label : ZMod 3) +
        ∑ other : S3PhaseOne,
          if other = ⟨label, hlabel⟩ then 0
          else
            (pairCountOf ⟨label, hlabel⟩ other (phaseOneSubword word) :
                ZMod 3) -
              (pairCountOf other ⟨label, hlabel⟩ (phaseOneSubword word) :
                ZMod 3) := by
  simpa [pairBalance] using
    two_mul_s3Arrow_eq_count_add_pairBalance label hlabel word hphase

end GSHTest
