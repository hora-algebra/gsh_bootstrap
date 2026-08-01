import GSH.Height.S3ArrowAssembly
import GSH.Height.S3FlipPairQuotients
import GSH.Height.S3PhaseAssembly

/-!
# Finite assembly of the moving-label `S₃` arrow residues

For an even-phase word, the source-zero count of a phase-one label is
determined modulo three by its ordinary count and all ordered phase-one pair
counts.  This file turns that arithmetic identity into a finite union of
finite intersections of height-one languages.
-/

set_option autoImplicit false

namespace GSH

open scoped BigOperators

open S3ArrowArithmetic

namespace S3FlipArrowAssembly

/-- A complete assignment of residues to ordered phase-one pairs. -/
abbrev PairResidues := S3PhaseOne → S3PhaseOne → Fin 3

/-- A diagonal pair carries no information; distinct pairs use the exact
pair-residue language. -/
def conditionalPairResidue (x y : S3PhaseOne) (residue : Fin 3) :
    Language S3Alphabet :=
  if x = y then Set.univ
  else S3FlipPairQuotients.s3PairResidue x y residue.1

/-- Even-phase words with a fixed source-zero moving-label residue. -/
def s3FlipEvenSourceZeroResidue (label : S3Alphabet) (residue : Nat) :
    Language S3Alphabet :=
  {word | (word.map s3Phase).sum = 0 ∧
    s3ArrowCountFrom 0 0 label word % 3 = residue}

/-- One finite cell: the ordinary-count residue and every ordered pair
residue are fixed, and the arithmetic identity selects the target arrow
residue. -/
def sourceZeroCell (label : S3PhaseOne) (target countResidue : Fin 3)
    (pairResidues : PairResidues) : Language S3Alphabet :=
  if (2 : ZMod 3) * (target.1 : ZMod 3) =
      (countResidue.1 : ZMod 3) +
        ∑ other : S3PhaseOne,
          if other = label then 0
          else
            ((pairResidues label other).1 : ZMod 3) -
              ((pairResidues other label).1 : ZMod 3)
  then
    s3PhaseZeroLanguage ∩
      {word | word.count label.1 % 3 = countResidue.1} ∩
        ⋂ x : S3PhaseOne, ⋂ y : S3PhaseOne,
          conditionalPairResidue x y (pairResidues x y)
  else ∅

/-- Finite union of all residue cells for the requested source-zero arrow
residue. -/
def sourceZeroAssembly (label : S3PhaseOne) (target : Fin 3) :
    Language S3Alphabet :=
  ⋃ countResidue : Fin 3, ⋃ pairResidues : PairResidues,
    sourceZeroCell label target countResidue pairResidues

private theorem conditionalPairResidue_mem_of_distinct
    (x y : S3PhaseOne) (hxy : x ≠ y) (residue : Fin 3)
    (word : Word S3Alphabet) :
    word ∈ conditionalPairResidue x y residue ↔
      (word.map s3Phase).sum = 0 ∧
        pairCountOf x y (phaseOneSubword word) % 3 = residue.1 := by
  have hval : x.1 ≠ y.1 := by
    intro h
    exact hxy (Subtype.ext h)
  simp [conditionalPairResidue, hxy,
    S3FlipPairQuotients.s3PairResidue]

private theorem isHeightOne_conditionalPairResidue
    (x y : S3PhaseOne) (residue : Fin 3) :
    HasHeightAtMost (conditionalPairResidue x y residue) 1 := by
  by_cases hxy : x = y
  · simp [conditionalPairResidue, hxy]
    exact HasHeightAtMost.univ
  · have hval : x.1 ≠ y.1 := by
      intro h
      exact hxy (Subtype.ext h)
    simp only [conditionalPairResidue, hxy, if_false]
    exact S3FlipPairQuotients.hasHeightAtMost_s3PairResidue
      x y hval residue

private theorem sourceZeroCell_heightOne (label : S3PhaseOne)
    (target countResidue : Fin 3) (pairResidues : PairResidues) :
    HasHeightAtMost
      (sourceZeroCell label target countResidue pairResidues) 1 := by
  classical
  unfold sourceZeroCell
  split
  next _ =>
    apply HasHeightAtMost.inter
    · apply HasHeightAtMost.inter
      · exact hasHeightAtMost_s3PhaseZeroLanguage
      · exact Counting.hasHeightAtMost_count label.1 countResidue.2
    · apply HasHeightAtMost.iInter
      intro x
      apply HasHeightAtMost.iInter
      intro y
      exact isHeightOne_conditionalPairResidue x y (pairResidues x y)
  next _ => exact HasHeightAtMost.empty

private theorem sourceZeroAssembly_heightOne (label : S3PhaseOne)
    (target : Fin 3) :
    HasHeightAtMost (sourceZeroAssembly label target) 1 := by
  classical
  unfold sourceZeroAssembly
  apply HasHeightAtMost.iUnion
  intro countResidue
  apply HasHeightAtMost.iUnion
  intro pairResidues
  exact sourceZeroCell_heightOne label target countResidue pairResidues

private theorem sourceZeroAssembly_eq (label : S3PhaseOne)
    (target : Fin 3) :
    sourceZeroAssembly label target =
      s3FlipEvenSourceZeroResidue label.1 target.1 := by
  classical
  ext word
  simp only [sourceZeroAssembly, Set.mem_iUnion]
  constructor
  · rintro ⟨countResidue, pairResidues, hcell⟩
    have haccept : (2 : ZMod 3) * (target.1 : ZMod 3) =
        (countResidue.1 : ZMod 3) +
          ∑ other : S3PhaseOne,
            if other = label then 0
            else
              ((pairResidues label other).1 : ZMod 3) -
                ((pairResidues other label).1 : ZMod 3) := by
      by_contra hreject
      simp [sourceZeroCell, hreject] at hcell
    rw [sourceZeroCell, if_pos haccept] at hcell
    rcases hcell with ⟨⟨hphase, hcount⟩, hpairs⟩
    have hbalance :
        pairBalance label (phaseOneSubword word) =
          ∑ other : S3PhaseOne,
            if other = label then 0
            else
              ((pairResidues label other).1 : ZMod 3) -
                ((pairResidues other label).1 : ZMod 3) := by
      unfold pairBalance
      apply Finset.sum_congr rfl
      intro other _
      by_cases hother : other = label
      · simp [hother]
      · have hforward :=
          (conditionalPairResidue_mem_of_distinct label other (Ne.symm hother)
            (pairResidues label other) word).mp
            ((Set.mem_iInter.mp (Set.mem_iInter.mp hpairs label) other))
        have hbackward :=
          (conditionalPairResidue_mem_of_distinct other label hother
            (pairResidues other label) word).mp
            ((Set.mem_iInter.mp (Set.mem_iInter.mp hpairs other) label))
        simp only [hother, if_false]
        rw [← ZMod.natCast_mod
              (pairCountOf label other (phaseOneSubword word)) 3,
            hforward.2,
            ← ZMod.natCast_mod
              (pairCountOf other label (phaseOneSubword word)) 3,
            hbackward.2]
    have hidentity := two_mul_s3Arrow_eq_count_add_pairBalance
      label.1 label.2 word hphase
    rw [hbalance] at hidentity
    have hcountCast : (word.count label.1 : ZMod 3) =
        (countResidue.1 : ZMod 3) := by
      rw [← ZMod.natCast_mod (word.count label.1) 3, hcount]
    rw [hcountCast] at hidentity
    rw [← ZMod.natCast_mod (s3ArrowCountFrom 0 0 label.1 word) 3]
      at hidentity
    have hmul := hidentity.trans haccept.symm
    have hcast :
        ((s3ArrowCountFrom 0 0 label.1 word % 3 : Nat) : ZMod 3) =
          (target.1 : ZMod 3) := by
      have htwo : ∀ z : ZMod 3, z = 2 * (2 * z) := by decide
      exact (htwo _).trans
        ((congrArg (fun z : ZMod 3 => 2 * z) hmul).trans (htwo _).symm)
    have hmodEq : s3ArrowCountFrom 0 0 label.1 word % 3 ≡
        target.1 [MOD 3] :=
      (ZMod.natCast_eq_natCast_iff _ _ 3).mp hcast
    exact ⟨hphase, hmodEq.eq_of_lt_of_lt
      (Nat.mod_lt _ (by decide)) target.2⟩
  · rintro ⟨hphase, harrow⟩
    let countResidue : Fin 3 :=
      ⟨word.count label.1 % 3, Nat.mod_lt _ (by decide)⟩
    let pairResidues : PairResidues := fun x y =>
      ⟨pairCountOf x y (phaseOneSubword word) % 3,
        Nat.mod_lt _ (by decide)⟩
    refine ⟨countResidue, pairResidues, ?_⟩
    have haccept : (2 : ZMod 3) * (target.1 : ZMod 3) =
        (countResidue.1 : ZMod 3) +
          ∑ other : S3PhaseOne,
            if other = label then 0
            else
              ((pairResidues label other).1 : ZMod 3) -
                ((pairResidues other label).1 : ZMod 3) := by
      have hidentity := two_mul_s3Arrow_eq_count_add_pairBalance
        label.1 label.2 word hphase
      rw [← ZMod.natCast_mod (s3ArrowCountFrom 0 0 label.1 word) 3,
        harrow] at hidentity
      simpa [countResidue, pairResidues, pairBalance,
        ZMod.natCast_mod] using hidentity
    rw [sourceZeroCell, if_pos haccept]
    refine ⟨⟨hphase, rfl⟩, ?_⟩
    rw [Set.mem_iInter]
    intro x
    rw [Set.mem_iInter]
    intro y
    by_cases hxy : x = y
    · simp [conditionalPairResidue, hxy]
    · apply (conditionalPairResidue_mem_of_distinct x y hxy
        (pairResidues x y) word).mpr
      exact ⟨hphase, rfl⟩

end S3FlipArrowAssembly

/-- Every even-phase source-zero residue of a moving label has generalized
star height at most one. -/
theorem hasHeightAtMost_s3FlipEvenSourceZero
    (label : S3Alphabet) (hlabel : s3Phase label = 1)
    (residue : Fin 3) :
    HasHeightAtMost
      {word : Word S3Alphabet |
        (word.map s3Phase).sum = 0 ∧
          s3ArrowCountFrom 0 0 label word % 3 = residue.1} 1 := by
  let phaseLabel : S3ArrowArithmetic.S3PhaseOne := ⟨label, hlabel⟩
  exact (S3FlipArrowAssembly.sourceZeroAssembly_heightOne
    phaseLabel residue).congr
      (S3FlipArrowAssembly.sourceZeroAssembly_eq phaseLabel residue)

end GSH
