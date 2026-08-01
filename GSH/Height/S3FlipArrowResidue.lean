import GSH.Height.S3FlipSourceOne
import GSH.Height.S3FullFiberAssembly
import GSH.Height.S3SelfLoopTransfer

/-!
# Completion of all labelled-arrow residues for `S₃`

The even-phase moving-edge theorem is extended to odd-phase words by a left
quotient with a phase-one prefix different from the counted label.  Combining
moving edges with the completed self-loop branch gives every labelled-arrow
residue feature and therefore the exact `HeightOneForGroup S₃` theorem.
-/

set_option autoImplicit false

namespace GSH

/-- A phase-one permutation chosen to be different from the counted moving
label. -/
def s3FlipPrefix (label : S3Alphabet) : S3Alphabet :=
  if label = Equiv.swap (0 : Fin 3) 1 then
    Equiv.swap (0 : Fin 3) 2
  else
    Equiv.swap (0 : Fin 3) 1

theorem s3Phase_s3FlipPrefix (label : S3Alphabet) :
    s3Phase (s3FlipPrefix label) = 1 := by
  unfold s3FlipPrefix
  split <;> decide

theorem s3FlipPrefix_ne (label : S3Alphabet) :
    s3FlipPrefix label ≠ label := by
  unfold s3FlipPrefix
  split
  · rename_i h
    subst label
    decide
  · rename_i h
    exact fun heq => h heq.symm

/-- Odd-final words with a fixed moving-edge residue. -/
def s3FlipOddResidue (source : ZMod 2) (label : S3Alphabet)
    (residue : Nat) : Language S3Alphabet :=
  {word | (word.map s3Phase).sum = 1 ∧
    s3ArrowCountFrom 0 source label word % 3 = residue}

/-- Prefixing by a different moving letter swaps source state, changes odd
final phase to even, and does not itself increment the counted label. -/
theorem leftQuotient_s3FlipEven_eq_odd (label : S3Alphabet)
    (source : ZMod 2) (residue : Nat) :
    Language.leftQuotient (s3FlipPrefix label)
        {word : Word S3Alphabet |
          (word.map s3Phase).sum = 0 ∧
            s3ArrowCountFrom 0 (source + 1) label word % 3 = residue} =
      s3FlipOddResidue source label residue := by
  ext word
  simp only [Language.mem_leftQuotient_iff, Set.mem_setOf_eq,
    s3FlipOddResidue, List.map_cons, List.sum_cons,
    s3Phase_s3FlipPrefix]
  have hshift := s3ArrowCount_shift 1 0 source label word
  have hshift' : s3ArrowCountFrom 1 (source + 1) label word =
      s3ArrowCountFrom 0 source label word := by
    simpa using hshift
  have hcount :
      s3ArrowCountFrom 0 (source + 1) label
          (s3FlipPrefix label :: word) =
        s3ArrowCountFrom 0 source label word := by
    simpa [s3ArrowCountFrom, ArrowCounting.c2Step,
      s3Phase_s3FlipPrefix, s3FlipPrefix_ne] using hshift'
  rw [hcount]
  have hphase : ∀ phase : ZMod 2, 1 + phase = 0 ↔ phase = 1 := by
    decide
  rw [hphase]

/-- Every odd-final moving-edge residue language has height at most one. -/
theorem hasHeightAtMost_s3FlipOdd (label : S3Alphabet)
    (hlabel : s3Phase label = 1) (source : ZMod 2)
    (residue : Fin 3) :
    HasHeightAtMost (s3FlipOddResidue source label residue.1) 1 := by
  have heven := hasHeightAtMost_s3FlipEven
    label hlabel (source + 1) residue
  exact (heven.leftQuotient (s3FlipPrefix label)).congr
    (leftQuotient_s3FlipEven_eq_odd label source residue.1)

/-- Complete moving-edge branch over both final phases. -/
theorem hasHeightAtMost_s3FlipArrowResidue (label : S3Alphabet)
    (hlabel : s3Phase label = 1) (source : ZMod 2)
    (residue : Fin 3) :
    HasHeightAtMost
      {word : Word S3Alphabet |
        s3ArrowCountFrom 0 source label word % 3 = residue.1} 1 := by
  have heven := hasHeightAtMost_s3FlipEven label hlabel source residue
  have hodd := hasHeightAtMost_s3FlipOdd label hlabel source residue
  refine (heven.union hodd).congr ?_
  ext word
  simp only [Set.mem_union, Set.mem_setOf_eq, s3FlipOddResidue]
  constructor
  · rintro (⟨-, hcount⟩ | ⟨-, hcount⟩) <;> exact hcount
  · intro hcount
    have phaseCases : ∀ phase : ZMod 2, phase = 0 ∨ phase = 1 := by
      decide
    rcases phaseCases (word.map s3Phase).sum with hphase | hphase
    · exact Or.inl ⟨hphase, hcount⟩
    · exact Or.inr ⟨hphase, hcount⟩

private theorem s3Phase_eq_zero_or_one (label : S3Alphabet) :
    s3Phase label = 0 ∨ s3Phase label = 1 := by
  unfold s3Phase
  split <;> simp

/-- Every labelled two-state arrow residue over the full `S₃` alphabet has
generalized star height at most one. -/
theorem hasHeightAtMost_s3ArrowResidue (label : S3Alphabet)
    (source : ZMod 2) (residue : Fin 3) :
    HasHeightAtMost
      {word : Word S3Alphabet |
        s3ArrowCountFrom 0 source label word % 3 = residue.1} 1 := by
  rcases s3Phase_eq_zero_or_one label with hzero | hone
  · exact hasHeightAtMost_s3SelfLoopArrowResidue
      label hzero source residue
  · exact hasHeightAtMost_s3FlipArrowResidue
      label hone source residue

/-- The full six-letter identity fibre of `S₃` has generalized star height at
most one. -/
theorem heightOne_fullIdentityFiber_S3 :
    HasHeightAtMost (fullIdentityFiber (Equiv.Perm (Fin 3))) 1 :=
  hasHeightAtMost_fullIdentityFiber_S3_of_arrowResidues
    hasHeightAtMost_s3ArrowResidue

/-- The exact first noncommutative group theorem, preserving the quantifiers
over every finite alphabet, every recognizing morphism, and every accepting
subset. -/
theorem heightOne_S3 : HeightOneForGroup (Equiv.Perm (Fin 3)) :=
  heightOneForGroup_of_fullIdentityFiber heightOne_fullIdentityFiber_S3

end GSH
