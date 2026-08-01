import GSH.Height.Counting
import GSH.Height.D4ArrowArithmetic
import GSH.Height.D4FlipPairQuotients
import GSH.Height.D4SelfLoopTransfer
import GSH.Height.FiniteBoolean

/-!
# Finite Boolean assembly of phase-one `D₄` arrow residues

For a fixed reflection label, the source-zero arrow count modulo four is
recovered from its ordinary count and all incident distinct-pair counts
modulo eight.  This file turns that arithmetic reconstruction into the
height-one language consumed by the final `D₄` coordinate assembly.
-/

set_option autoImplicit false

namespace GSH

open scoped BigOperators

namespace D4ArrowAssembly

open D4ArrowArithmetic D4FlipPairQuotients
open S3ArrowArithmetic

/-- The phase-one labels distinct from a fixed phase-one label. -/
abbrev Other (label : D4PhaseOne) := {other : D4PhaseOne // other ≠ label}

/-- The finite feature family used for one source-zero moving-arrow residue.
The left summand is the ordinary count; the two Boolean directions in the
right summand are the ordered pair counts incident with `label`. -/
def sourceZeroFeature (label : D4PhaseOne) :
    (Fin 8 ⊕ ((Bool × Other label) × Fin 8)) → Language D4Alphabet
  | .inl residue =>
      {word | word.count label.1 % 8 = residue.1}
  | .inr ((direction, other), residue) =>
      if direction then
        d4PairResidue other.1 label residue
      else
        d4PairResidue label other.1 residue

/-- The truth-table condition encoding the mod-eight fingerprint of a fixed
source-zero moving-arrow residue. -/
def sourceZeroAccept (label : D4PhaseOne) (target : Fin 4)
    (bits : (Fin 8 ⊕ ((Bool × Other label) × Fin 8)) → Bool) : Prop :=
  ∃ countResidue : Fin 8,
    ∃ forward reverse : D4PhaseOne → Fin 8,
      bits (.inl countResidue) = true ∧
      (∀ other : Other label,
        bits (.inr ((false, other), forward other.1)) = true) ∧
      (∀ other : Other label,
        bits (.inr ((true, other), reverse other.1)) = true) ∧
      (countResidue.1 : ZMod 8) +
          (∑ other : D4PhaseOne,
            if other = label then 0
            else ((forward other).1 : ZMod 8) -
              ((reverse other).1 : ZMod 8)) =
        (2 : ZMod 8) * (target.1 : ZMod 8)

/-- Finite Boolean reconstruction of one source-zero moving-arrow residue. -/
noncomputable def sourceZeroAssembly (label : D4PhaseOne)
    (target : Fin 4) : Language D4Alphabet :=
  Language.booleanCombination (sourceZeroFeature label)
    (sourceZeroAccept label target)

/-- The exact phase-zero source-zero arrow-residue language. -/
def sourceZeroResidue (label : D4PhaseOne) (target : Fin 4) :
    Language D4Alphabet :=
  {word | (word.map d4Phase).sum = 0 ∧
    d4ArrowCountFrom 0 0 label.1 word % 4 = target.1}

private theorem pairResidue_cast (left right : D4PhaseOne)
    (residue : Fin 8) (word : Word D4Alphabet)
    (hmem : word ∈ d4PairResidue left right residue) :
    (pairCountOf left right
        (d4PhaseOneSubword word) : ZMod 8) = residue.1 := by
  have hmod := hmem.2
  rw [← ZMod.natCast_mod
    (pairCountOf left right
      (d4PhaseOneSubword word)) 8]
  rw [hmod]

private theorem fingerprint_eq_of_bits (label : D4PhaseOne)
    (target : Fin 4) (word : Word D4Alphabet)
    (countResidue : Fin 8) (forward reverse : D4PhaseOne → Fin 8)
    (hcount : word ∈ sourceZeroFeature label (.inl countResidue))
    (hforward : ∀ other : Other label,
      word ∈ sourceZeroFeature label
        (.inr ((false, other), forward other.1)))
    (hreverse : ∀ other : Other label,
      word ∈ sourceZeroFeature label
        (.inr ((true, other), reverse other.1)))
    (hsum : (countResidue.1 : ZMod 8) +
          (∑ other : D4PhaseOne,
            if other = label then 0
            else ((forward other).1 : ZMod 8) -
              ((reverse other).1 : ZMod 8)) =
        (2 : ZMod 8) * (target.1 : ZMod 8)) :
    d4ArrowFingerprint8 label.1 label.2 word =
      (2 : ZMod 8) * (target.1 : ZMod 8) := by
  have hcountCast : (word.count label.1 : ZMod 8) = countResidue.1 := by
    change word.count label.1 % 8 = countResidue.1 at hcount
    rw [← ZMod.natCast_mod (word.count label.1) 8]
    rw [hcount]
  rw [d4ArrowFingerprint8, hcountCast]
  unfold d4PairBalance8
  calc
    (countResidue.1 : ZMod 8) +
        (∑ other : D4PhaseOne,
          if other = label then 0
          else
            (pairCountOf label other
                (d4PhaseOneSubword word) : ZMod 8) -
              (pairCountOf other label
                (d4PhaseOneSubword word) : ZMod 8)) =
      (countResidue.1 : ZMod 8) +
        (∑ other : D4PhaseOne,
          if other = label then 0
          else ((forward other).1 : ZMod 8) -
            ((reverse other).1 : ZMod 8)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro other _
      by_cases hother : other = label
      · simp [hother]
      · let other' : Other label := ⟨other, hother⟩
        have hf := hforward other'
        have hr := hreverse other'
        change word ∈ d4PairResidue label other (forward other) at hf
        change word ∈ d4PairResidue other label (reverse other) at hr
        rw [pairResidue_cast label other (forward other) word hf,
          pairResidue_cast other label (reverse other) word hr]
    _ = _ := hsum

private theorem exists_other (label : D4PhaseOne) :
    ∃ other : D4PhaseOne, other ≠ label := by
  revert label
  decide

/-- The Boolean assembly has exactly the requested source-zero semantics. -/
theorem sourceZeroAssembly_eq (label : D4PhaseOne) (target : Fin 4) :
    sourceZeroAssembly label target = sourceZeroResidue label target := by
  classical
  ext word
  simp only [sourceZeroAssembly, Language.booleanCombination,
    sourceZeroAccept, sourceZeroResidue, Set.mem_setOf_eq]
  constructor
  · rintro ⟨countResidue, forward, reverse,
      hcountBit, hforwardBits, hreverseBits, hsum⟩
    have hcount : word ∈ sourceZeroFeature label (.inl countResidue) :=
      of_decide_eq_true hcountBit
    have hforward : ∀ other : Other label,
        word ∈ sourceZeroFeature label
          (.inr ((false, other), forward other.1)) := by
      intro other
      exact of_decide_eq_true (hforwardBits other)
    have hreverse : ∀ other : Other label,
        word ∈ sourceZeroFeature label
          (.inr ((true, other), reverse other.1)) := by
      intro other
      exact of_decide_eq_true (hreverseBits other)
    obtain ⟨other, hne⟩ := exists_other label
    let other' : Other label := ⟨other, hne⟩
    have hpair := hforward other'
    change word ∈ d4PairResidue label other (forward other) at hpair
    have hphase := hpair.1
    refine ⟨hphase, ?_⟩
    apply (d4ArrowCount_mod_four_iff_features_mod_eight
      label.1 label.2 word target hphase).mpr
    exact fingerprint_eq_of_bits label target word countResidue
      forward reverse hcount hforward hreverse hsum
  · rintro ⟨hphase, htarget⟩
    let countResidue : Fin 8 :=
      ⟨word.count label.1 % 8, Nat.mod_lt _ (by omega)⟩
    let forward : D4PhaseOne → Fin 8 := fun other =>
      ⟨pairCountOf label other
          (d4PhaseOneSubword word) % 8, Nat.mod_lt _ (by omega)⟩
    let reverse : D4PhaseOne → Fin 8 := fun other =>
      ⟨pairCountOf other label
          (d4PhaseOneSubword word) % 8, Nat.mod_lt _ (by omega)⟩
    refine ⟨countResidue, forward, reverse, ?_, ?_, ?_, ?_⟩
    · simp [Language.truthVector, sourceZeroFeature, countResidue]
    · intro other
      simp [Language.truthVector, sourceZeroFeature, forward,
        d4PairResidue, hphase]
    · intro other
      simp [Language.truthVector, sourceZeroFeature, reverse,
        d4PairResidue, hphase]
    · have hfingerprint :=
        (d4ArrowCount_mod_four_iff_features_mod_eight
          label.1 label.2 word target hphase).mp htarget
      calc
        (countResidue.1 : ZMod 8) +
            (∑ other : D4PhaseOne,
              if other = label then 0
              else ((forward other).1 : ZMod 8) -
                ((reverse other).1 : ZMod 8)) =
          d4ArrowFingerprint8 label.1 label.2 word := by
            rw [d4ArrowFingerprint8]
            unfold d4PairBalance8
            congr 1
            · simp [countResidue, ZMod.natCast_mod]
            · apply Finset.sum_congr rfl
              intro other _
              by_cases ho : other = label
              · simp [ho]
              · simp [ho, forward, reverse, ZMod.natCast_mod]
        _ = _ := hfingerprint

private theorem sourceZeroFeature_heightOne (label : D4PhaseOne)
    (index : Fin 8 ⊕ ((Bool × Other label) × Fin 8)) :
    HasHeightAtMost (sourceZeroFeature label index) 1 := by
  rcases index with residue | ⟨⟨direction, other⟩, residue⟩
  · exact Counting.hasHeightAtMost_count label.1 residue.2
  · cases direction
    · exact hasHeightAtMost_d4PairResidue label other.1
        (by intro h; exact other.2 (Subtype.ext h.symm)) residue
    · exact hasHeightAtMost_d4PairResidue other.1 label
        (by intro h; exact other.2 (Subtype.ext h)) residue

/-- Every phase-zero, source-zero residue of a phase-one `D₄` label has
generalized star height at most one. -/
theorem hasHeightAtMost_sourceZeroResidue (label : D4PhaseOne)
    (target : Fin 4) :
    HasHeightAtMost (sourceZeroResidue label target) 1 := by
  have hassembly := HasHeightAtMost.booleanCombination
    (sourceZeroFeature label) (sourceZeroAccept label target)
    (sourceZeroFeature_heightOne label)
  exact hassembly.congr (sourceZeroAssembly_eq label target)

end D4ArrowAssembly

/-- Public consumer for every phase-one source-zero `D₄` arrow residue. -/
theorem hasHeightAtMost_d4FlipEvenSourceZero (label : D4Alphabet)
    (hlabel : d4Phase label = 1) (residue : Fin 4) :
    HasHeightAtMost
      {word : Word D4Alphabet |
        (word.map d4Phase).sum = 0 ∧
          d4ArrowCountFrom 0 0 label word % 4 = residue.1} 1 := by
  exact D4ArrowAssembly.hasHeightAtMost_sourceZeroResidue
    ⟨label, hlabel⟩ residue

namespace D4ArrowAssembly

/-- The source-zero arrow residues and ordinary count residues used by the
final `D₄` coordinate truth table. -/
def coordinateFeature :
    ((D4Alphabet × Fin 4) ⊕ (D4Alphabet × Fin 4)) → Language D4Alphabet
  | .inl (label, residue) =>
      {word | (word.map d4Phase).sum = 0 ∧
        d4ArrowCountFrom 0 0 label word % 4 = residue.1}
  | .inr (label, residue) =>
      {word | word.count label % 4 = residue.1}

/-- The finite truth table for zero phase and zero signed `D₄` coordinate.
Source one is eliminated arithmetically as `total - sourceZero`. -/
def coordinateAccept
    (bits : ((D4Alphabet × Fin 4) ⊕ (D4Alphabet × Fin 4)) → Bool) : Prop :=
  ∃ sourceZero total : D4Alphabet → Fin 4,
    (∀ label, bits (.inl (label, sourceZero label)) = true) ∧
    (∀ label, bits (.inr (label, total label)) = true) ∧
    (∑ label : D4Alphabet,
      d4Beta label *
        ((2 : ZMod 4) * ((sourceZero label).1 : ZMod 4) -
          ((total label).1 : ZMod 4))) = 0

/-- Finite Boolean reconstruction of the complete `D₄` arrow-coordinate
identity fibre. -/
noncomputable def coordinateAssembly : Language D4Alphabet :=
  Language.booleanCombination coordinateFeature coordinateAccept

private theorem coordinateAssembly_eq :
    coordinateAssembly = d4ArrowCoordinateFiber := by
  classical
  ext word
  simp only [coordinateAssembly, Language.booleanCombination,
    coordinateAccept, d4ArrowCoordinateFiber, Set.mem_setOf_eq]
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
    have hone := hzero (1 : D4Alphabet)
    change (word.map d4Phase).sum = 0 ∧ _ at hone
    refine ⟨hone.1, ?_⟩
    rw [d4BetaByArrows_eq_sourceZero_total]
    calc
      (∑ label : D4Alphabet,
        d4Beta label *
          ((2 : ZMod 4) *
              (d4ArrowCountFrom 0 0 label word : ZMod 4) -
            (word.count label : ZMod 4))) =
        ∑ label : D4Alphabet,
          d4Beta label *
            ((2 : ZMod 4) * ((sourceZero label).1 : ZMod 4) -
              ((total label).1 : ZMod 4)) := by
          apply Finset.sum_congr rfl
          intro label _
          have hz := (hzero label).2
          have ht := htotal label
          change word.count label % 4 = (total label).1 at ht
          rw [← ZMod.natCast_mod
            (d4ArrowCountFrom 0 0 label word) 4, hz,
            ← ZMod.natCast_mod (word.count label) 4, ht]
      _ = 0 := hsum
  · rintro ⟨hphase, hbeta⟩
    let sourceZero : D4Alphabet → Fin 4 := fun label =>
      ⟨d4ArrowCountFrom 0 0 label word % 4,
        Nat.mod_lt _ (by omega)⟩
    let total : D4Alphabet → Fin 4 := fun label =>
      ⟨word.count label % 4, Nat.mod_lt _ (by omega)⟩
    refine ⟨sourceZero, total, ?_, ?_, ?_⟩
    · intro label
      simp [Language.truthVector, coordinateFeature, sourceZero, hphase]
    · intro label
      simp [Language.truthVector, coordinateFeature, total]
    · rw [d4BetaByArrows_eq_sourceZero_total] at hbeta
      calc
        (∑ label : D4Alphabet,
          d4Beta label *
            ((2 : ZMod 4) * ((sourceZero label).1 : ZMod 4) -
              ((total label).1 : ZMod 4))) =
          ∑ label : D4Alphabet,
            d4Beta label *
              ((2 : ZMod 4) *
                  (d4ArrowCountFrom 0 0 label word : ZMod 4) -
                (word.count label : ZMod 4)) := by
            apply Finset.sum_congr rfl
            intro label _
            simp [sourceZero, total, ZMod.natCast_mod]
        _ = 0 := hbeta

private theorem coordinateFeature_heightOne
    (index : (D4Alphabet × Fin 4) ⊕ (D4Alphabet × Fin 4)) :
    HasHeightAtMost (coordinateFeature index) 1 := by
  rcases index with ⟨label, residue⟩ | ⟨label, residue⟩
  · have hphase : d4Phase label = 0 ∨ d4Phase label = 1 := by
      revert label
      decide
    rcases hphase with hlabel | hlabel
    · exact D4SelfLoopTransfer.hasHeightAtMost_d4SelfLoopEvenSourceZero
        label hlabel residue
    · exact hasHeightAtMost_d4FlipEvenSourceZero label hlabel residue
  · exact Counting.hasHeightAtMost_count label residue.2

end D4ArrowAssembly

/-- The complete `D₄` arithmetic identity fibre has generalized star height
at most one. -/
theorem hasHeightAtMost_d4ArrowCoordinateFiber :
    HasHeightAtMost d4ArrowCoordinateFiber 1 := by
  have hassembly := HasHeightAtMost.booleanCombination
    D4ArrowAssembly.coordinateFeature D4ArrowAssembly.coordinateAccept
    D4ArrowAssembly.coordinateFeature_heightOne
  exact hassembly.congr D4ArrowAssembly.coordinateAssembly_eq

/-- The full-alphabet identity fibre of `D₄` has generalized star height at
most one. -/
theorem heightOne_fullIdentityFiber_D4 :
    HasHeightAtMost (fullIdentityFiber (DihedralGroup 4)) 1 :=
  hasHeightAtMost_d4ArrowCoordinateFiber.congr
    fullIdentityFiber_d4_eq_arrowCoordinateFiber.symm

/-- Every language recognized by `D₄`, over every finite alphabet and for
every accepting subset, has generalized star height at most one. -/
theorem heightOne_D4 : HeightOneForGroup (DihedralGroup 4) :=
  heightOneForGroup_of_fullIdentityFiber heightOne_fullIdentityFiber_D4

end GSH
