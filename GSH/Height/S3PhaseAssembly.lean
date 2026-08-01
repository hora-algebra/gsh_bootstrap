import GSH.Height.Counting
import GSH.Height.FiniteBoolean
import GSH.Height.S3FullFiber

/-!
# Finite Boolean assembly of the `S₃` phase coordinate

The total phase is determined by the parity of the occurrence count of each
of the six full-alphabet letters.  This file packages that finite truth table
and proves that its zero fibre has generalized star height at most one.
-/

set_option autoImplicit false

namespace GSH

open scoped BigOperators

/-- The words whose product has phase zero. -/
def s3PhaseZeroLanguage : Language S3Alphabet :=
  {word | (word.map s3Phase).sum = 0}

/-- A count-residue feature used to reconstruct the phase coordinate. -/
def s3PhaseFeature (index : S3Alphabet × Fin 2) : Language S3Alphabet :=
  {word | word.count index.1 % 2 = index.2.1}

/-- The truth-table condition saying that a consistent choice of all six
count parities has weighted phase sum zero. -/
def s3PhaseAccept (bits : (S3Alphabet × Fin 2) → Bool) : Prop :=
  ∃ residues : S3Alphabet → Fin 2,
    (∀ label, bits (label, residues label) = true) ∧
      (∑ label : S3Alphabet,
        ((residues label).1 : ZMod 2) * s3Phase label) = 0

/-- Finite Boolean reconstruction of the phase-zero language. -/
noncomputable def s3PhaseZeroAssembly : Language S3Alphabet :=
  Language.booleanCombination s3PhaseFeature s3PhaseAccept

private theorem s3Phase_sum_eq_count_sum (word : Word S3Alphabet) :
    (word.map s3Phase).sum =
      ∑ label : S3Alphabet,
        (word.count label : ZMod 2) * s3Phase label := by
  classical
  induction word with
  | nil => simp
  | cons a word ih =>
      rw [List.map_cons, List.sum_cons, ih]
      calc
        s3Phase a +
            ∑ label : S3Alphabet,
              (word.count label : ZMod 2) * s3Phase label =
          (∑ label : S3Alphabet,
              (((if a = label then 1 else 0) : Nat) : ZMod 2) *
                s3Phase label) +
            ∑ label : S3Alphabet,
              (word.count label : ZMod 2) * s3Phase label := by simp
        _ = ∑ label : S3Alphabet,
              (((if a = label then 1 else 0) + word.count label : Nat) :
                  ZMod 2) * s3Phase label := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro label _
            push_cast
            ring
        _ = ∑ label : S3Alphabet,
              ((a :: word).count label : ZMod 2) * s3Phase label := by
            apply Finset.sum_congr rfl
            intro label _
            simp only [List.count_cons]
            by_cases h : a = label <;> simp [h, add_comm]

/-- The Boolean assembly has exactly the phase-zero semantics. -/
theorem s3PhaseZeroAssembly_eq :
    s3PhaseZeroAssembly = s3PhaseZeroLanguage := by
  classical
  ext word
  simp only [s3PhaseZeroAssembly, Language.booleanCombination,
    s3PhaseAccept, s3PhaseZeroLanguage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨residues, hbits, hsum⟩
    rw [s3Phase_sum_eq_count_sum]
    calc
      (∑ label : S3Alphabet,
          (word.count label : ZMod 2) * s3Phase label) =
        ∑ label : S3Alphabet,
          ((residues label).1 : ZMod 2) * s3Phase label := by
            apply Finset.sum_congr rfl
            intro label _
            have hbit := hbits label
            have hmem : word ∈ s3PhaseFeature (label, residues label) := by
              exact of_decide_eq_true hbit
            change word.count label % 2 = (residues label).1 at hmem
            rw [← ZMod.natCast_mod (word.count label) 2]
            rw [hmem]
      _ = 0 := hsum
  · intro hphase
    let residues : S3Alphabet → Fin 2 := fun label =>
      ⟨word.count label % 2, Nat.mod_lt _ (by decide)⟩
    refine ⟨residues, ?_, ?_⟩
    · intro label
      simp [Language.truthVector, s3PhaseFeature, residues]
    · rw [s3Phase_sum_eq_count_sum] at hphase
      calc
        (∑ label : S3Alphabet,
            ((residues label).1 : ZMod 2) * s3Phase label) =
          ∑ label : S3Alphabet,
            (word.count label : ZMod 2) * s3Phase label := by
              apply Finset.sum_congr rfl
              intro label _
              simp [residues, ZMod.natCast_mod]
        _ = 0 := hphase

/-- The phase-zero coordinate language has generalized star height at most
one. -/
theorem hasHeightAtMost_s3PhaseZeroLanguage :
    HasHeightAtMost s3PhaseZeroLanguage 1 := by
  have hfeatures : ∀ index : S3Alphabet × Fin 2,
      HasHeightAtMost (s3PhaseFeature index) 1 := by
    intro index
    exact Counting.hasHeightAtMost_count index.1 index.2.2
  have hassembly := HasHeightAtMost.booleanCombination
    s3PhaseFeature s3PhaseAccept hfeatures
  exact hassembly.congr s3PhaseZeroAssembly_eq

end GSH
