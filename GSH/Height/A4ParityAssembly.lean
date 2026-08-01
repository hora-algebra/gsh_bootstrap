import GSH.Height.A4Coordinates
import GSH.Height.FiniteBoolean
import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Finite Boolean assembly of the `A₄` residual parity state

One feature records oddness for each of the 36 phase/letter events.  Boolean
complement supplies evenness, so no duplicated residue-indexed features are
needed.
-/

set_option autoImplicit false

namespace GSH

local instance : IsKleinFour A4Klein :=
  alternatingGroup.kleinFour_isKleinFour (α := Fin 4) (by simp)

local instance : CommGroup A4Klein :=
  { (inferInstance : Group A4Klein) with
    mul_comm := IsKleinFour.isMulCommutative.is_comm.comm }

/-- The odd-count feature for one phase/letter event. -/
def a4PhaseLabelParityFeature (event : ZMod 3 × A4) : Language A4 :=
  {word | a4PhaseLabelCount event.1 event.2 word % 2 = 1}

/-- Truth vectors whose selected twisted `V₄` factors multiply to one. -/
def a4ParityAccept (bits : (ZMod 3 × A4) → Bool) : Prop :=
  ∏ event : ZMod 3 × A4,
    a4TwistedVectorKlein event ^ (if bits event then 1 else 0) = 1

/-- The finite Boolean assembly of the 36 odd-count features. -/
noncomputable def a4ParityAssembly : Language A4 :=
  Language.booleanCombination a4PhaseLabelParityFeature a4ParityAccept

private theorem a4_pow_parity (x : A4Klein) (n : Nat) :
    x ^ n = x ^ (n % 2) := by
  apply pow_eq_pow_mod
  simpa [pow_two] using IsKleinFour.mul_self x

private theorem a4_pow_count_eq_truthBit
    (event : ZMod 3 × A4) (word : Word A4) :
    a4TwistedVectorKlein event ^
        @List.count (ZMod 3 × A4) instBEqOfDecidableEq event
          (a4PhaseLabelsFrom 0 word) =
      a4TwistedVectorKlein event ^
        (if Language.truthVector a4PhaseLabelParityFeature word event
          then 1 else 0) := by
  rw [a4_pow_parity]
  change a4TwistedVectorKlein event ^
      (a4PhaseLabelCount event.1 event.2 word % 2) = _
  by_cases hodd : a4PhaseLabelCount event.1 event.2 word % 2 = 1
  · have htruth : Language.truthVector a4PhaseLabelParityFeature word event =
        true := by
      simp [Language.truthVector, a4PhaseLabelParityFeature, hodd]
    rw [hodd, htruth]
    rfl
  · have heven : a4PhaseLabelCount event.1 event.2 word % 2 = 0 := by
      omega
    have htruth : Language.truthVector a4PhaseLabelParityFeature word event =
        false := by
      simp [Language.truthVector, a4PhaseLabelParityFeature, hodd]
    rw [heven, htruth]
    rfl

/-- The 36-feature Boolean assembly is exactly the residual count-state
coordinate fibre. -/
theorem a4ParityAssembly_eq :
    a4ParityAssembly = a4PhaseLabelCoordinateFiber := by
  classical
  ext word
  simp only [a4ParityAssembly, Language.booleanCombination, a4ParityAccept,
    a4PhaseLabelCoordinateFiber, Set.mem_setOf_eq]
  rw [a4VectorFromPhaseLabelCounts]
  constructor
  · intro h
    calc
      (∏ event : ZMod 3 × A4,
        a4TwistedVectorKlein event ^
          @List.count (ZMod 3 × A4) instBEqOfDecidableEq event
            (a4PhaseLabelsFrom 0 word)) =
          ∏ event : ZMod 3 × A4,
            a4TwistedVectorKlein event ^
              (if Language.truthVector a4PhaseLabelParityFeature word event
                then 1 else 0) := by
                  apply Finset.prod_congr rfl
                  intro event _
                  exact a4_pow_count_eq_truthBit event word
      _ = 1 := h
  · intro h
    calc
      (∏ event : ZMod 3 × A4,
        a4TwistedVectorKlein event ^
          (if Language.truthVector a4PhaseLabelParityFeature word event
            then 1 else 0)) =
          ∏ event : ZMod 3 × A4,
            a4TwistedVectorKlein event ^
              @List.count (ZMod 3 × A4) instBEqOfDecidableEq event
                (a4PhaseLabelsFrom 0 word) := by
                  apply Finset.prod_congr rfl
                  intro event _
                  exact (a4_pow_count_eq_truthBit event word).symm
      _ = 1 := h

/-- Height one for every odd-count feature closes the residual coordinate by
finite Boolean assembly. -/
theorem hasHeightAtMost_a4Coordinate_of_parities
    (hfeatures : ∀ event : ZMod 3 × A4,
      HasHeightAtMost (a4PhaseLabelParityFeature event) 1) :
    HasHeightAtMost a4PhaseLabelCoordinateFiber 1 := by
  have h := HasHeightAtMost.booleanCombination
    a4PhaseLabelParityFeature a4ParityAccept hfeatures
  exact h.congr a4ParityAssembly_eq

/-- Exact parent consumer: the 36 feature certificates imply the fully
quantified group theorem for `A₄`. -/
theorem heightOne_A4_of_parities
    (hfeatures : ∀ event : ZMod 3 × A4,
      HasHeightAtMost (a4PhaseLabelParityFeature event) 1) :
    HeightOneForGroup A4 := by
  apply heightOneForGroup_of_fullIdentityFiber
  apply heightOne_fullIdentityFiber_A4_of_v4
  rw [a4V4CoordinateFiber_eq_phaseLabelCoordinateFiber]
  exact hasHeightAtMost_a4Coordinate_of_parities hfeatures

end GSH
