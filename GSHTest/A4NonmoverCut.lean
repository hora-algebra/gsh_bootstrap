import GSH.Height.A4NonmoverCut
import GSH.Height.A4ParityAssembly

/-! Consumer-first checks for the §5.1 nonmover cut identity. -/

set_option autoImplicit false

open GSH

example (label : A4) (hlabel : a4PhaseValue label = 0)
    (start target : ZMod 3) (word : Word A4) :
    a4BaseCutCountFrom start target word =
      a4PhaseLabelCountFrom start target label word +
        a4SingleDelayCutCountFrom label start target word :=
  a4_baseCut_partition_nonmover label hlabel start target word

example (label : A4) (hlabel : a4PhaseValue label = 0)
    (target : ZMod 3) (word : Word A4) :
    a4PhaseLabelCount target label word % 2 =
      (a4BaseCutCountFrom 0 target word % 2 +
        a4SingleDelayCutCountFrom label 0 target word % 2) % 2 :=
  a4_nonmover_mod_two_identity label hlabel target word

-- Exact next consumer in `A4ParityAssembly`: a phase-zero event feature is
-- the Boolean parity combination of its base and single-delay cut counts.
example (label : A4) (hlabel : a4PhaseValue label = 0)
    (target : ZMod 3) (word : Word A4) :
    word ∈ a4PhaseLabelParityFeature (target, label) ↔
      (a4BaseCutCountFrom 0 target word % 2 +
        a4SingleDelayCutCountFrom label 0 target word % 2) % 2 = 1 := by
  change a4PhaseLabelCount target label word % 2 = 1 ↔ _
  rw [a4_nonmover_mod_two_identity label hlabel target word]
