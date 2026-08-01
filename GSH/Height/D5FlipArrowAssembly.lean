import GSH.Height.Counting
import GSH.Height.D5ArrowArithmetic
import GSH.Height.D5FlipPairQuotients
import GSH.Height.FiniteBoolean

/-!
# Finite Boolean assembly of phase-one `D₅` arrow residues

For a fixed reflection label, the source-zero arrow count modulo five is
recovered from its ordinary count and all incident distinct-pair counts
modulo five.  This file turns that arithmetic reconstruction into the
height-one language consumed by the final `D₅` coordinate assembly.
-/

set_option autoImplicit false

namespace GSH

open scoped BigOperators

namespace D5FlipArrowAssembly

open D5ArrowArithmetic D5FlipPairQuotients
open S3ArrowArithmetic
open D5FlipPairTransfer

/-- The phase-one labels distinct from a fixed phase-one label. -/
abbrev Other (label : D5PhaseOne) := {other : D5PhaseOne // other ≠ label}

/-- The finite feature family used for one source-zero moving-arrow residue.
The left summand is the ordinary count; the two Boolean directions in the
right summand are the ordered pair counts incident with `label`. -/
def sourceZeroFeature (label : D5PhaseOne) :
    (Fin 5 ⊕ ((Bool × Other label) × Fin 5)) → Language D5Alphabet
  | .inl residue =>
      {word | word.count label.1 % 5 = residue.1}
  | .inr ((direction, other), residue) =>
      if direction then
        d5PairResidue other.1 label residue
      else
        d5PairResidue label other.1 residue

/-- The truth-table condition encoding the mod-five fingerprint of a fixed
source-zero moving-arrow residue. -/
def sourceZeroAccept (label : D5PhaseOne) (target : Fin 5)
    (bits : (Fin 5 ⊕ ((Bool × Other label) × Fin 5)) → Bool) : Prop :=
  ∃ countResidue : Fin 5,
    ∃ forward reverse : D5PhaseOne → Fin 5,
      bits (.inl countResidue) = true ∧
      (∀ other : Other label,
        bits (.inr ((false, other), forward other.1)) = true) ∧
      (∀ other : Other label,
        bits (.inr ((true, other), reverse other.1)) = true) ∧
      (countResidue.1 : ZMod 5) +
          (∑ other : D5PhaseOne,
            if other = label then 0
            else ((forward other).1 : ZMod 5) -
              ((reverse other).1 : ZMod 5)) =
        (2 : ZMod 5) * (target.1 : ZMod 5)

/-- Finite Boolean reconstruction of one source-zero moving-arrow residue. -/
noncomputable def sourceZeroAssembly (label : D5PhaseOne)
    (target : Fin 5) : Language D5Alphabet :=
  Language.booleanCombination (sourceZeroFeature label)
    (sourceZeroAccept label target)

/-- The exact phase-zero source-zero arrow-residue language. -/
def sourceZeroResidue (label : D5PhaseOne) (target : Fin 5) :
    Language D5Alphabet :=
  {word | (word.map d5Phase).sum = 0 ∧
    d5ArrowCountFrom 0 0 label.1 word % 5 = target.1}

private theorem pairResidue_cast (left right : D5PhaseOne)
    (residue : Fin 5) (word : Word D5Alphabet)
    (hmem : word ∈ d5PairResidue left right residue) :
    (pairCountOf left right
        (d5PhaseOneSubword word) : ZMod 5) = residue.1 := by
  have hmod := hmem.2
  rw [← ZMod.natCast_mod
    (pairCountOf left right
      (d5PhaseOneSubword word)) 5]
  rw [hmod]

private theorem fingerprint_eq_of_bits (label : D5PhaseOne)
    (target : Fin 5) (word : Word D5Alphabet)
    (countResidue : Fin 5) (forward reverse : D5PhaseOne → Fin 5)
    (hcount : word ∈ sourceZeroFeature label (.inl countResidue))
    (hforward : ∀ other : Other label,
      word ∈ sourceZeroFeature label
        (.inr ((false, other), forward other.1)))
    (hreverse : ∀ other : Other label,
      word ∈ sourceZeroFeature label
        (.inr ((true, other), reverse other.1)))
    (hsum : (countResidue.1 : ZMod 5) +
          (∑ other : D5PhaseOne,
            if other = label then 0
            else ((forward other).1 : ZMod 5) -
              ((reverse other).1 : ZMod 5)) =
        (2 : ZMod 5) * (target.1 : ZMod 5)) :
    d5ArrowFingerprint5 label.1 label.2 word =
      (2 : ZMod 5) * (target.1 : ZMod 5) := by
  have hcountCast : (word.count label.1 : ZMod 5) = countResidue.1 := by
    change word.count label.1 % 5 = countResidue.1 at hcount
    rw [← ZMod.natCast_mod (word.count label.1) 5]
    rw [hcount]
  rw [d5ArrowFingerprint5, hcountCast]
  unfold d5PairBalance5
  calc
    (countResidue.1 : ZMod 5) +
        (∑ other : D5PhaseOne,
          if other = label then 0
          else
            (pairCountOf label other
                (d5PhaseOneSubword word) : ZMod 5) -
              (pairCountOf other label
                (d5PhaseOneSubword word) : ZMod 5)) =
      (countResidue.1 : ZMod 5) +
        (∑ other : D5PhaseOne,
          if other = label then 0
          else ((forward other).1 : ZMod 5) -
            ((reverse other).1 : ZMod 5)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro other _
      by_cases hother : other = label
      · simp [hother]
      · let other' : Other label := ⟨other, hother⟩
        have hf := hforward other'
        have hr := hreverse other'
        change word ∈ d5PairResidue label other (forward other) at hf
        change word ∈ d5PairResidue other label (reverse other) at hr
        rw [pairResidue_cast label other (forward other) word hf,
          pairResidue_cast other label (reverse other) word hr]
    _ = _ := hsum

private theorem exists_other (label : D5PhaseOne) :
    ∃ other : D5PhaseOne, other ≠ label := by
  revert label
  decide

/-- The Boolean assembly has exactly the requested source-zero semantics. -/
theorem sourceZeroAssembly_eq (label : D5PhaseOne) (target : Fin 5) :
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
    change word ∈ d5PairResidue label other (forward other) at hpair
    have hphase := hpair.1
    refine ⟨hphase, ?_⟩
    apply (d5ArrowCount_mod_five_iff_features_mod_five
      label.1 label.2 word target hphase).mpr
    exact fingerprint_eq_of_bits label target word countResidue
      forward reverse hcount hforward hreverse hsum
  · rintro ⟨hphase, htarget⟩
    let countResidue : Fin 5 :=
      ⟨word.count label.1 % 5, Nat.mod_lt _ (by omega)⟩
    let forward : D5PhaseOne → Fin 5 := fun other =>
      ⟨pairCountOf label other
          (d5PhaseOneSubword word) % 5, Nat.mod_lt _ (by omega)⟩
    let reverse : D5PhaseOne → Fin 5 := fun other =>
      ⟨pairCountOf other label
          (d5PhaseOneSubword word) % 5, Nat.mod_lt _ (by omega)⟩
    refine ⟨countResidue, forward, reverse, ?_, ?_, ?_, ?_⟩
    · simp [Language.truthVector, sourceZeroFeature, countResidue]
    · intro other
      simp [Language.truthVector, sourceZeroFeature, forward,
        d5PairResidue, hphase]
    · intro other
      simp [Language.truthVector, sourceZeroFeature, reverse,
        d5PairResidue, hphase]
    · have hfingerprint :=
        (d5ArrowCount_mod_five_iff_features_mod_five
          label.1 label.2 word target hphase).mp htarget
      calc
        (countResidue.1 : ZMod 5) +
            (∑ other : D5PhaseOne,
              if other = label then 0
              else ((forward other).1 : ZMod 5) -
                ((reverse other).1 : ZMod 5)) =
          d5ArrowFingerprint5 label.1 label.2 word := by
            rw [d5ArrowFingerprint5]
            unfold d5PairBalance5
            congr 1
            · simp [countResidue, ZMod.natCast_mod]
            · apply Finset.sum_congr rfl
              intro other _
              by_cases ho : other = label
              · simp [ho]
              · simp [ho, forward, reverse, ZMod.natCast_mod]
        _ = _ := hfingerprint

private theorem sourceZeroFeature_heightOne (label : D5PhaseOne)
    (index : Fin 5 ⊕ ((Bool × Other label) × Fin 5)) :
    HasHeightAtMost (sourceZeroFeature label index) 1 := by
  rcases index with residue | ⟨⟨direction, other⟩, residue⟩
  · exact Counting.hasHeightAtMost_count label.1 residue.2
  · cases direction
    · exact hasHeightAtMost_d5PairResidue label other.1
        (by intro h; exact other.2 (Subtype.ext h.symm)) residue
    · exact hasHeightAtMost_d5PairResidue other.1 label
        (by intro h; exact other.2 (Subtype.ext h)) residue

/-- Every phase-zero, source-zero residue of a phase-one `D₅` label has
generalized star height at most one. -/
theorem hasHeightAtMost_sourceZeroResidue (label : D5PhaseOne)
    (target : Fin 5) :
    HasHeightAtMost (sourceZeroResidue label target) 1 := by
  have hassembly := HasHeightAtMost.booleanCombination
    (sourceZeroFeature label) (sourceZeroAccept label target)
    (sourceZeroFeature_heightOne label)
  exact hassembly.congr (sourceZeroAssembly_eq label target)

end D5FlipArrowAssembly

/-- Public consumer for every phase-one source-zero `D₅` arrow residue. -/
theorem hasHeightAtMost_d5FlipEvenSourceZero (label : D5Alphabet)
    (hlabel : d5Phase label = 1) (residue : Fin 5) :
    HasHeightAtMost
      {word : Word D5Alphabet |
        (word.map d5Phase).sum = 0 ∧
          d5ArrowCountFrom 0 0 label word % 5 = residue.1} 1 := by
  exact D5FlipArrowAssembly.hasHeightAtMost_sourceZeroResidue
    ⟨label, hlabel⟩ residue


end GSH
