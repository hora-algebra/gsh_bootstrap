import GSH.Height.S3PhaseAssembly

/-!
# Finite assembly of the full `S₃` identity fibre

This file isolates the final quantifier-preserving reduction.  Once every
labelled two-state arrow-count residue language has height at most one, their
finite truth table reconstructs the translation coordinate.  Intersecting
with the already-closed phase coordinate gives the full identity fibre and
hence `HeightOneForGroup S₃`.
-/

set_option autoImplicit false

namespace GSH

open scoped BigOperators

/-- A single labelled-arrow residue feature. -/
def s3ArrowFeature
    (index : (ZMod 2 × S3Alphabet) × Fin 3) : Language S3Alphabet :=
  {word | s3ArrowCountFrom 0 index.1.1 index.1.2 word % 3 = index.2.1}

/-- The truth-table condition that the selected arrow residues have signed
`S₃` translation coordinate zero. -/
def s3BetaAccept
    (bits : (((ZMod 2 × S3Alphabet) × Fin 3)) → Bool) : Prop :=
  ∃ residues : ZMod 2 → S3Alphabet → Fin 3,
    (∀ source label, bits ((source, label), residues source label) = true) ∧
      (∑ label : S3Alphabet,
        (s3Beta label * ((residues 0 label).1 : ZMod 3) -
          s3Beta label * ((residues 1 label).1 : ZMod 3))) = 0

/-- Finite Boolean reconstruction of the zero translation coordinate. -/
noncomputable def s3BetaZeroAssembly : Language S3Alphabet :=
  Language.booleanCombination s3ArrowFeature s3BetaAccept

/-- The words whose signed arrow coordinate is zero. -/
def s3BetaZeroLanguage : Language S3Alphabet :=
  {word | s3BetaByArrows word = 0}

/-- The Boolean assembly has exactly the zero-translation semantics. -/
theorem s3BetaZeroAssembly_eq :
    s3BetaZeroAssembly = s3BetaZeroLanguage := by
  classical
  ext word
  simp only [s3BetaZeroAssembly, Language.booleanCombination, s3BetaAccept,
    s3BetaZeroLanguage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨residues, hbits, hsum⟩
    rw [s3BetaByArrows, s3BetaByArrowsFrom]
    calc
      (∑ label : S3Alphabet,
          (s3Beta label * (s3ArrowCountFrom 0 0 label word : ZMod 3) -
            s3Beta label * (s3ArrowCountFrom 0 1 label word : ZMod 3))) =
        ∑ label : S3Alphabet,
          (s3Beta label * ((residues 0 label).1 : ZMod 3) -
            s3Beta label * ((residues 1 label).1 : ZMod 3)) := by
              apply Finset.sum_congr rfl
              intro label _
              have hbit0 := hbits 0 label
              have hbit1 := hbits 1 label
              have hmem0 : word ∈
                  s3ArrowFeature ((0, label), residues 0 label) :=
                of_decide_eq_true hbit0
              have hmem1 : word ∈
                  s3ArrowFeature ((1, label), residues 1 label) :=
                of_decide_eq_true hbit1
              change s3ArrowCountFrom 0 0 label word % 3 =
                (residues 0 label).1 at hmem0
              change s3ArrowCountFrom 0 1 label word % 3 =
                (residues 1 label).1 at hmem1
              rw [← ZMod.natCast_mod
                (s3ArrowCountFrom 0 0 label word) 3]
              rw [← ZMod.natCast_mod
                (s3ArrowCountFrom 0 1 label word) 3]
              rw [hmem0, hmem1]
      _ = 0 := hsum
  · intro hbeta
    let residues : ZMod 2 → S3Alphabet → Fin 3 := fun source label =>
      ⟨s3ArrowCountFrom 0 source label word % 3,
        Nat.mod_lt _ (by decide)⟩
    refine ⟨residues, ?_, ?_⟩
    · intro source label
      simp [Language.truthVector, s3ArrowFeature, residues]
    · rw [s3BetaByArrows, s3BetaByArrowsFrom] at hbeta
      calc
        (∑ label : S3Alphabet,
            (s3Beta label * ((residues 0 label).1 : ZMod 3) -
              s3Beta label * ((residues 1 label).1 : ZMod 3))) =
          ∑ label : S3Alphabet,
            (s3Beta label * (s3ArrowCountFrom 0 0 label word : ZMod 3) -
              s3Beta label *
                (s3ArrowCountFrom 0 1 label word : ZMod 3)) := by
                  apply Finset.sum_congr rfl
                  intro label _
                  simp [residues, ZMod.natCast_mod]
        _ = 0 := hbeta

/-- The phase and arrow assemblies reconstruct the exact arithmetic fibre. -/
theorem s3ArrowCoordinateFiber_eq_phase_inter_beta :
    s3ArrowCoordinateFiber = s3PhaseZeroLanguage ∩ s3BetaZeroLanguage := by
  rfl

/-- If all labelled-arrow residue features have height one, so does the
translation-coordinate zero language. -/
theorem hasHeightAtMost_s3BetaZeroLanguage_of_arrowResidues
    (harrow : ∀ (label : S3Alphabet) (source : ZMod 2) (residue : Fin 3),
      HasHeightAtMost
        {word : Word S3Alphabet |
          s3ArrowCountFrom 0 source label word % 3 = residue.1} 1) :
    HasHeightAtMost s3BetaZeroLanguage 1 := by
  have hfeatures : ∀ index : (ZMod 2 × S3Alphabet) × Fin 3,
      HasHeightAtMost (s3ArrowFeature index) 1 := by
    intro index
    exact harrow index.1.2 index.1.1 index.2
  have hassembly := HasHeightAtMost.booleanCombination
    s3ArrowFeature s3BetaAccept hfeatures
  exact hassembly.congr s3BetaZeroAssembly_eq

/-- Conditional final bridge from all arrow-residue features to the full
arithmetic identity fibre. -/
theorem hasHeightAtMost_s3ArrowCoordinateFiber_of_arrowResidues
    (harrow : ∀ (label : S3Alphabet) (source : ZMod 2) (residue : Fin 3),
      HasHeightAtMost
        {word : Word S3Alphabet |
          s3ArrowCountFrom 0 source label word % 3 = residue.1} 1) :
    HasHeightAtMost s3ArrowCoordinateFiber 1 := by
  have hbeta := hasHeightAtMost_s3BetaZeroLanguage_of_arrowResidues harrow
  exact (hasHeightAtMost_s3PhaseZeroLanguage.inter hbeta).congr
    s3ArrowCoordinateFiber_eq_phase_inter_beta.symm

/-- Conditional full-identity-fibre theorem for `S₃`. -/
theorem hasHeightAtMost_fullIdentityFiber_S3_of_arrowResidues
    (harrow : ∀ (label : S3Alphabet) (source : ZMod 2) (residue : Fin 3),
      HasHeightAtMost
        {word : Word S3Alphabet |
          s3ArrowCountFrom 0 source label word % 3 = residue.1} 1) :
    HasHeightAtMost (fullIdentityFiber S3Alphabet) 1 := by
  exact (hasHeightAtMost_s3ArrowCoordinateFiber_of_arrowResidues harrow).congr
    fullIdentityFiber_s3_eq_arrowCoordinateFiber.symm

/-- Exact quantifier-preserving consumer: every finite alphabet, recognizing
morphism, and accepting subset follows from the full identity fibre. -/
theorem heightOne_S3_of_arrowResidues
    (harrow : ∀ (label : S3Alphabet) (source : ZMod 2) (residue : Fin 3),
      HasHeightAtMost
        {word : Word S3Alphabet |
          s3ArrowCountFrom 0 source label word % 3 = residue.1} 1) :
    HeightOneForGroup S3Alphabet :=
  heightOneForGroup_of_fullIdentityFiber
    (hasHeightAtMost_fullIdentityFiber_S3_of_arrowResidues harrow)

end GSH
