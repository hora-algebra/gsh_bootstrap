import GSH.Groups.A4

/-!
# Word-level `V₄` coordinates for `A₄`

Each letter is tagged by the `ZMod 3` phase immediately before it is read.
The residual coordinate is reconstructed from the counts of these
phase/letter tags.  Since every resulting factor lies in the Klein four
subgroup, only the parity of each count matters.
-/

set_option autoImplicit false

namespace GSH

local instance : CommGroup A4Klein :=
  { (inferInstance : Group A4Klein) with
    mul_comm :=
      (alternatingGroup.kleinFour_isKleinFour
        (α := Fin 4) (by simp)).isMulCommutative.is_comm.comm }

/-- The phase/letter events of a word, starting at an arbitrary phase. -/
def a4PhaseLabelsFrom : ZMod 3 → Word A4 → List (ZMod 3 × A4)
  | _, [] => []
  | phase, g :: word =>
      (phase, g) :: a4PhaseLabelsFrom (phase + a4PhaseValue g) word

/-- The number of occurrences of `label` read from `phase`. -/
def a4PhaseLabelCount (phase : ZMod 3) (label : A4)
    (word : Word A4) : Nat :=
  @List.count (ZMod 3 × A4) instBEqOfDecidableEq
    (phase, label) (a4PhaseLabelsFrom 0 word)

/-- The letter's `V₄` coordinate, conjugated by the phase before the letter. -/
def a4TwistedVector (phase : ZMod 3) (g : A4) : A4 :=
  a4T ^ phase.val * a4VectorPart g * (a4T ^ phase.val)⁻¹

/-- Every phase-twisted residual coordinate lies in the canonical `V₄`. -/
def a4TwistedVectorKlein (event : ZMod 3 × A4) : A4Klein :=
  ⟨a4TwistedVector event.1 event.2, by
    rcases event with ⟨phase, g⟩
    show a4TwistedVector phase g ∈ (A4Klein : Set A4)
    rw [alternatingGroup.coe_kleinFour_of_card_eq_four (α := Fin 4) (by simp)]
    revert phase g
    set_option maxRecDepth 100000 in decide⟩

/-- Multiplication of normal forms advances the phase before twisting the
second residual coordinate. -/
private theorem a4_twistedVector_mul (phase : ZMod 3) (g h : A4) :
    a4TwistedVector phase g *
        a4TwistedVector (phase + a4PhaseValue g) h =
      a4TwistedVector phase (g * h) := by
  revert phase g h
  set_option maxRecDepth 100000 in decide

/-- Reading the tagged factors in temporal order gives the residual coordinate
of the whole word, conjugated by the starting phase. -/
theorem a4_phaseLabels_prod_from (phase : ZMod 3) (word : Word A4) :
    (((a4PhaseLabelsFrom phase word).map a4TwistedVectorKlein).prod : A4) =
      a4TwistedVector phase word.prod := by
  induction word generalizing phase with
  | nil =>
      simp [a4PhaseLabelsFrom, a4TwistedVector, a4VectorPart, a4PhaseValue,
        a4InKlein]
  | cons g word ih =>
      simp only [a4PhaseLabelsFrom, List.map_cons, List.prod_cons,
        List.prod_cons, Subgroup.coe_mul]
      rw [ih]
      exact a4_twistedVector_mul phase g word.prod

/-- The exact count-state reconstruction of the residual coordinate. -/
def a4VectorFromPhaseLabelCounts (word : Word A4) : A4Klein :=
  ∏ event : ZMod 3 × A4,
    a4TwistedVectorKlein event ^
      @List.count (ZMod 3 × A4) instBEqOfDecidableEq event
        (a4PhaseLabelsFrom 0 word)

/-- The residual coordinate of a word is determined by its phase-before
labelled-letter counts (equivalently their parities in `V₄`). -/
theorem a4VectorPart_prod_eq_phaseLabelCounts (word : Word A4) :
    a4VectorPart word.prod = (a4VectorFromPhaseLabelCounts word : A4) := by
  have hcount := Abelian.prod_map_count a4TwistedVectorKlein
    (a4PhaseLabelsFrom 0 word)
  have hcountCoe := congrArg (fun x : A4Klein => (x : A4)) hcount
  calc
    a4VectorPart word.prod =
        (((a4PhaseLabelsFrom 0 word).map a4TwistedVectorKlein).prod : A4) := by
          rw [a4_phaseLabels_prod_from]
          simp [a4TwistedVector]
    _ = (a4VectorFromPhaseLabelCounts word : A4) := by
      simpa [a4VectorFromPhaseLabelCounts] using hcountCoe

/-- The count-state presentation of the remaining `V₄` fibre. -/
def a4PhaseLabelCoordinateFiber : Language A4 :=
  {word | a4VectorFromPhaseLabelCounts word = 1}

/-- Exact consumer equality: the remaining parent fibre is precisely the
zero cell of the phase-before labelled-letter count state. -/
theorem a4V4CoordinateFiber_eq_phaseLabelCoordinateFiber :
    a4V4CoordinateFiber = a4PhaseLabelCoordinateFiber := by
  ext word
  simp only [a4V4CoordinateFiber, a4PhaseLabelCoordinateFiber,
    Set.mem_setOf_eq]
  rw [a4VectorPart_prod_eq_phaseLabelCounts]
  constructor
  · intro h
    apply Subtype.ext
    simpa using h
  · intro h
    simpa using congrArg Subtype.val h

end GSH
