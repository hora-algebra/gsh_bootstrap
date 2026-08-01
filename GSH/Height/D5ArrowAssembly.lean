import GSH.Height.Counting
import GSH.Height.D5ArrowCoordinates
import GSH.Height.D5FlipArrowAssembly
import GSH.Height.D5SelfLoopTransfer
import GSH.Height.FiniteBoolean

/-! # Final finite Boolean assembly of the D5 identity fibre -/

set_option autoImplicit false

namespace GSH

open scoped BigOperators

namespace D5ArrowAssembly

/-- The source-zero arrow residues and ordinary count residues used by the
final `D₅` coordinate truth table. -/
def coordinateFeature :
    ((D5Alphabet × Fin 5) ⊕ (D5Alphabet × Fin 5)) → Language D5Alphabet
  | .inl (label, residue) =>
      {word | (word.map d5Phase).sum = 0 ∧
        d5ArrowCountFrom 0 0 label word % 5 = residue.1}
  | .inr (label, residue) =>
      {word | word.count label % 5 = residue.1}

/-- The finite truth table for zero phase and zero signed `D₅` coordinate.
Source one is eliminated arithmetically as `total - sourceZero`. -/
def coordinateAccept
    (bits : ((D5Alphabet × Fin 5) ⊕ (D5Alphabet × Fin 5)) → Bool) : Prop :=
  ∃ sourceZero total : D5Alphabet → Fin 5,
    (∀ label, bits (.inl (label, sourceZero label)) = true) ∧
    (∀ label, bits (.inr (label, total label)) = true) ∧
    (∑ label : D5Alphabet,
      d5Beta label *
        ((2 : ZMod 5) * ((sourceZero label).1 : ZMod 5) -
          ((total label).1 : ZMod 5))) = 0

/-- Finite Boolean reconstruction of the complete `D₅` arrow-coordinate
identity fibre. -/
noncomputable def coordinateAssembly : Language D5Alphabet :=
  Language.booleanCombination coordinateFeature coordinateAccept

private theorem coordinateAssembly_eq :
    coordinateAssembly = d5ArrowCoordinateFiber := by
  classical
  ext word
  simp only [coordinateAssembly, Language.booleanCombination,
    coordinateAccept, d5ArrowCoordinateFiber, Set.mem_setOf_eq]
  constructor
  · rintro ⟨sourceZero, total, hzeroBits, htotalBits, hsum⟩
    have hzero : ∀ label, word ∈
        coordinateFeature (.inl (label, sourceZero label)) := by
      intro label
      exact of_decide_eq_true (hzeroBits label)
    have htotal : ∀ label, word ∈
        coordinateFeature (.inr (label, total label)) := by
      intro label
      exact of_decide_eq_true (htotalBits label)
    have hone := hzero (1 : D5Alphabet)
    change (word.map d5Phase).sum = 0 ∧ _ at hone
    refine ⟨hone.1, ?_⟩
    rw [d5BetaByArrows_eq_sourceZero_total]
    calc
      (∑ label : D5Alphabet,
        d5Beta label *
          ((2 : ZMod 5) *
              (d5ArrowCountFrom 0 0 label word : ZMod 5) -
            (word.count label : ZMod 5))) =
        ∑ label : D5Alphabet,
          d5Beta label *
            ((2 : ZMod 5) * ((sourceZero label).1 : ZMod 5) -
              ((total label).1 : ZMod 5)) := by
          apply Finset.sum_congr rfl
          intro label _
          have hz := (hzero label).2
          have ht := htotal label
          change word.count label % 5 = (total label).1 at ht
          rw [← ZMod.natCast_mod
            (d5ArrowCountFrom 0 0 label word) 5, hz,
            ← ZMod.natCast_mod (word.count label) 5, ht]
      _ = 0 := hsum
  · rintro ⟨hphase, hbeta⟩
    let sourceZero : D5Alphabet → Fin 5 := fun label =>
      ⟨d5ArrowCountFrom 0 0 label word % 5,
        Nat.mod_lt _ (by omega)⟩
    let total : D5Alphabet → Fin 5 := fun label =>
      ⟨word.count label % 5, Nat.mod_lt _ (by omega)⟩
    refine ⟨sourceZero, total, ?_, ?_, ?_⟩
    · intro label
      simp [Language.truthVector, coordinateFeature, sourceZero, hphase]
    · intro label
      simp [Language.truthVector, coordinateFeature, total]
    · rw [d5BetaByArrows_eq_sourceZero_total] at hbeta
      calc
        (∑ label : D5Alphabet,
          d5Beta label *
            ((2 : ZMod 5) * ((sourceZero label).1 : ZMod 5) -
              ((total label).1 : ZMod 5))) =
          ∑ label : D5Alphabet,
            d5Beta label *
              ((2 : ZMod 5) *
                  (d5ArrowCountFrom 0 0 label word : ZMod 5) -
                (word.count label : ZMod 5)) := by
            apply Finset.sum_congr rfl
            intro label _
            simp [sourceZero, total, ZMod.natCast_mod]
        _ = 0 := hbeta

private theorem coordinateFeature_heightOne
    (index : (D5Alphabet × Fin 5) ⊕ (D5Alphabet × Fin 5)) :
    HasHeightAtMost (coordinateFeature index) 1 := by
  rcases index with ⟨label, residue⟩ | ⟨label, residue⟩
  · have hphase : d5Phase label = 0 ∨ d5Phase label = 1 := by
      revert label
      decide
    rcases hphase with hlabel | hlabel
    · exact D5SelfLoopTransfer.hasHeightAtMost_d5SelfLoopEvenSourceZero
        label hlabel residue
    · exact hasHeightAtMost_d5FlipEvenSourceZero label hlabel residue
  · exact Counting.hasHeightAtMost_count label residue.2

end D5ArrowAssembly

/-- The complete `D₅` arithmetic identity fibre has generalized star height
at most one. -/
theorem hasHeightAtMost_d5ArrowCoordinateFiber :
    HasHeightAtMost d5ArrowCoordinateFiber 1 := by
  have hassembly := HasHeightAtMost.booleanCombination
    D5ArrowAssembly.coordinateFeature D5ArrowAssembly.coordinateAccept
    D5ArrowAssembly.coordinateFeature_heightOne
  exact hassembly.congr D5ArrowAssembly.coordinateAssembly_eq

/-- The full-alphabet identity fibre of `D₅` has generalized star height at
most one. -/
theorem heightOne_fullIdentityFiber_D5 :
    HasHeightAtMost (fullIdentityFiber (DihedralGroup 5)) 1 :=
  hasHeightAtMost_d5ArrowCoordinateFiber.congr
    fullIdentityFiber_d5_eq_arrowCoordinateFiber.symm

/-- Every language recognized by `D₅`, over every finite alphabet and for
every accepting subset, has generalized star height at most one. -/
theorem heightOne_D5 : HeightOneForGroup (DihedralGroup 5) :=
  heightOneForGroup_of_fullIdentityFiber heightOne_fullIdentityFiber_D5

end GSH
