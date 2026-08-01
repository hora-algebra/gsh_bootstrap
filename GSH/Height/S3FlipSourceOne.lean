import GSH.Height.S3FlipArrowAssembly

/-!
# Source-one assembly for even-phase moving edges in `S₃`

For even-phase words, source-one occurrences of a fixed moving label are
recovered from source-zero occurrences and the ordinary occurrence count.
The construction uses only a finite union and Boolean operations, so it
preserves the height-one bound supplied by the source-zero theorem.
-/

set_option autoImplicit false

namespace GSH

/-- Even-final words with a fixed source-one moving-edge residue. -/
def s3FlipEvenSourceOneResidue (label : S3Alphabet)
    (residue : Nat) : Language S3Alphabet :=
  {word | (word.map s3Phase).sum = 0 ∧
    s3ArrowCountFrom 0 1 label word % 3 = residue}

/-- Finite Boolean assembly of a source-one residue from source-zero
residues and the ordinary occurrence count. -/
def s3FlipSourceOneAssembly (label : S3Alphabet)
    (residue : Fin 3) : Language S3Alphabet :=
  ⋃ sourceZero : Fin 3,
    {word : Word S3Alphabet |
      (word.map s3Phase).sum = 0 ∧
        s3ArrowCountFrom 0 0 label word % 3 = sourceZero.1} ∩
      {word | word.count label % 3 = (sourceZero.1 + residue.1) % 3}

private theorem mod_partition_iff (left right total residue : Nat)
    (hpartition : left + right = total) (hresidue : residue < 3) :
    right % 3 = residue ↔
      total % 3 = (left % 3 + residue) % 3 := by
  rw [← hpartition, Nat.add_mod]
  have hleft := Nat.mod_lt left (by decide : 0 < 3)
  have hright := Nat.mod_lt right (by decide : 0 < 3)
  omega

/-- The finite assembly has exactly the source-one residue semantics. -/
theorem s3FlipSourceOneAssembly_eq (label : S3Alphabet)
    (residue : Fin 3) :
    s3FlipSourceOneAssembly label residue =
      s3FlipEvenSourceOneResidue label residue.1 := by
  ext word
  simp only [s3FlipSourceOneAssembly, Set.mem_iUnion, Set.mem_inter_iff,
    s3FlipEvenSourceOneResidue, Set.mem_setOf_eq]
  constructor
  · rintro ⟨sourceZero, ⟨hphase, hzero⟩, htotal⟩
    refine ⟨hphase, ?_⟩
    have hpartition := s3ArrowCount_partition 0 label word
    apply (mod_partition_iff
      (s3ArrowCountFrom 0 0 label word)
      (s3ArrowCountFrom 0 1 label word) (word.count label)
      residue.1 hpartition residue.2).mpr
    simpa [hzero] using htotal
  · rintro ⟨hphase, hone⟩
    let sourceZero : Fin 3 :=
      ⟨s3ArrowCountFrom 0 0 label word % 3,
        Nat.mod_lt _ (by decide)⟩
    refine ⟨sourceZero, ⟨hphase, rfl⟩, ?_⟩
    have hpartition := s3ArrowCount_partition 0 label word
    have htotal := (mod_partition_iff
      (s3ArrowCountFrom 0 0 label word)
      (s3ArrowCountFrom 0 1 label word) (word.count label)
      residue.1 hpartition residue.2).mp hone
    simpa [sourceZero] using htotal

/-- Every even-phase source-one moving-edge residue has height at most one. -/
theorem hasHeightAtMost_s3FlipEvenSourceOne (label : S3Alphabet)
    (hlabel : s3Phase label = 1) (residue : Fin 3) :
    HasHeightAtMost
      (s3FlipEvenSourceOneResidue label residue.1) 1 := by
  have hassembly : HasHeightAtMost
      (s3FlipSourceOneAssembly label residue) 1 := by
    apply HasHeightAtMost.iUnion
    intro sourceZero
    apply HasHeightAtMost.inter
    · exact hasHeightAtMost_s3FlipEvenSourceZero label hlabel sourceZero
    · exact Counting.hasHeightAtMost_count label
        (Nat.mod_lt _ (by decide : 0 < 3))
  exact hassembly.congr (s3FlipSourceOneAssembly_eq label residue)

/-- Every even-phase moving-edge residue, for either source state, has
height at most one. -/
theorem hasHeightAtMost_s3FlipEven (label : S3Alphabet)
    (hlabel : s3Phase label = 1) (source : ZMod 2)
    (residue : Fin 3) :
    HasHeightAtMost
      {word : Word S3Alphabet |
        (word.map s3Phase).sum = 0 ∧
          s3ArrowCountFrom 0 source label word % 3 = residue.1} 1 := by
  have hsource : source = 0 ∨ source = 1 := by
    revert source
    decide
  rcases hsource with rfl | rfl
  · exact hasHeightAtMost_s3FlipEvenSourceZero label hlabel residue
  · exact hasHeightAtMost_s3FlipEvenSourceOne label hlabel residue

end GSH
