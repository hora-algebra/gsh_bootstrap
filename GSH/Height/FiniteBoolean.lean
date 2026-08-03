import GSH.Height.Closure
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

/-!
# Finite Boolean assembly of bounded-height features

If finitely many feature languages all have generalized star height at most
`n`, then any Boolean truth table in their membership bits has height at most
`n`.  The proof writes the accepted truth table as a finite union of cells,
with each cell a finite intersection of a feature or its complement.
-/

set_option autoImplicit false

namespace GSH

universe u v

namespace Language

variable {α : Type u} {ι : Type v}

/-- The membership bits of a finite family of feature languages at a word. -/
noncomputable def truthVector (features : ι → Language α) (word : Word α) :
    ι → Bool :=
  by
    classical
    exact fun i => decide (word ∈ features i)

/-- The cell on which every feature has the prescribed truth value. -/
def featureCell (features : ι → Language α) (bits : ι → Bool) : Language α :=
  ⋂ i, if bits i = true then features i else (features i)ᶜ

/-- The language selected by an arbitrary predicate on the finite feature
truth vector. -/
noncomputable def booleanCombination
    (features : ι → Language α) (accept : (ι → Bool) → Prop) : Language α :=
  {word | accept (truthVector features word)}

theorem booleanCombination_eq_iUnion_cells [Fintype ι]
    (features : ι → Language α) (accept : (ι → Bool) → Prop) :
    booleanCombination features accept =
      ⋃ bits : {bits : ι → Bool // accept bits},
        featureCell features bits.1 := by
  classical
  ext word
  constructor
  · intro h
    let bits := truthVector features word
    have hbits : accept bits := h
    refine Set.mem_iUnion.2 ⟨⟨bits, hbits⟩, ?_⟩
    simp only [featureCell, Set.mem_iInter]
    intro i
    by_cases hi : word ∈ features i
    · simp [bits, truthVector, hi]
    · simp [bits, truthVector, hi]
  · intro h
    obtain ⟨bits, hcell⟩ := Set.mem_iUnion.1 h
    have htruth : truthVector features word = bits.1 := by
      funext i
      simp only [featureCell, Set.mem_iInter] at hcell
      have hi := hcell i
      by_cases hmem : word ∈ features i
      · have hbit : bits.1 i = true := by
          by_contra hfalse
          have hcompl : word ∈ (features i)ᶜ := by
            simpa [hfalse] using hi
          have hnot : word ∉ features i := by
            simpa using hcompl
          exact hnot hmem
        simp [truthVector, hmem, hbit]
      · have hbit : bits.1 i = false := by
          apply Bool.eq_false_of_not_eq_true
          intro htrue
          have hfeature : word ∈ features i := by
            simpa [htrue] using hi
          exact hmem hfeature
        simp [truthVector, hmem, hbit]
    show accept (truthVector features word)
    rw [htruth]
    exact bits.2

end Language

namespace HasHeightAtMost

variable {α : Type u} {ι : Type v}

theorem featureCell [Fintype ι] (features : ι → Language α)
    (bits : ι → Bool) {n : Nat}
    (hfeatures : ∀ i, HasHeightAtMost (features i) n) :
    HasHeightAtMost (Language.featureCell features bits) n := by
  apply iInter
  intro i
  by_cases hi : bits i = true
  · simpa [Language.featureCell, hi] using hfeatures i
  · simpa [Language.featureCell, hi] using (hfeatures i).compl

/-- Any finite Boolean truth table in bounded-height feature languages has the
same height bound. -/
theorem booleanCombination [Fintype ι] (features : ι → Language α)
    (accept : (ι → Bool) → Prop) {n : Nat}
    (hfeatures : ∀ i, HasHeightAtMost (features i) n) :
    HasHeightAtMost (Language.booleanCombination features accept) n := by
  classical
  rw [Language.booleanCombination_eq_iUnion_cells]
  letI : Fintype (ι → Bool) := inferInstance
  letI : Fintype {bits : ι → Bool // accept bits} := Fintype.ofFinite _
  exact iUnion _ fun bits => featureCell features bits.1 hfeatures

end HasHeightAtMost

end GSH
