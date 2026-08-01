import GSH.Height.S3SelfLoopQuotients

/-!
# Finite arithmetic assembly for `S₃` arrow residues

This file records arithmetic identities used to combine the two source-state
arrow counts and the first source-one height consequence consumed by the
completed self-loop transfer.
-/

set_option autoImplicit false

namespace GSH

/-- The two source-state counts of a fixed label partition its ordinary
occurrences. -/
theorem s3ArrowCount_partition (start : ZMod 2) (label : S3Alphabet)
    (word : Word S3Alphabet) :
    s3ArrowCountFrom start 0 label word +
        s3ArrowCountFrom start 1 label word =
      word.count label := by
  induction word generalizing start with
  | nil => rfl
  | cons a word ih =>
      have hstate : start = 0 ∨ start = 1 := by
        revert start
        decide
      rcases hstate with rfl | rfl
      · simp only [s3ArrowCountFrom, ArrowCounting.arrowCountFrom_cons,
          List.count_cons]
        have htail :
            ArrowCounting.arrowCountFrom (ArrowCounting.c2Step s3Phase)
                (ArrowCounting.c2Step s3Phase 0 a) 0 label word +
              ArrowCounting.arrowCountFrom (ArrowCounting.c2Step s3Phase)
                (ArrowCounting.c2Step s3Phase 0 a) 1 label word =
              word.count label := by
          simpa [s3ArrowCountFrom] using
            ih (ArrowCounting.c2Step s3Phase 0 a)
        by_cases ha : a = label
        · subst a
          simp only [beq_self_eq_true, if_true, if_false, true_and, false_and,
            eq_self, zero_ne_one] at ⊢
          omega
        · simpa [ha, Nat.add_assoc, Nat.add_comm] using htail
      · simp only [s3ArrowCountFrom, ArrowCounting.arrowCountFrom_cons,
          List.count_cons]
        have htail :
            ArrowCounting.arrowCountFrom (ArrowCounting.c2Step s3Phase)
                (ArrowCounting.c2Step s3Phase 1 a) 0 label word +
              ArrowCounting.arrowCountFrom (ArrowCounting.c2Step s3Phase)
                (ArrowCounting.c2Step s3Phase 1 a) 1 label word =
              word.count label := by
          simpa [s3ArrowCountFrom] using
            ih (ArrowCounting.c2Step s3Phase 1 a)
        by_cases ha : a = label
        · subst a
          simp only [beq_self_eq_true, if_true, if_false, true_and, false_and,
            eq_self, one_ne_zero] at ⊢
          omega
        · simpa [ha, Nat.add_comm] using htail

/-- Translating both the start and source states by the same `C₂` element
does not change a labelled-arrow count. -/
theorem s3ArrowCount_shift (shift start source : ZMod 2)
    (label : S3Alphabet) (word : Word S3Alphabet) :
    s3ArrowCountFrom (start + shift) (source + shift) label word =
      s3ArrowCountFrom start source label word := by
  induction word generalizing start with
  | nil => rfl
  | cons a word ih =>
      change
        (if start + shift = source + shift ∧ a = label then 1 else 0) +
            s3ArrowCountFrom ((start + shift) + s3Phase a)
              (source + shift) label word =
          (if start = source ∧ a = label then 1 else 0) +
            s3ArrowCountFrom (start + s3Phase a) source label word
      have hstate : start + shift = source + shift ↔ start = source :=
        add_right_cancel_iff
      have htail := ih (start + s3Phase a)
      have hnext : (start + shift) + s3Phase a =
          (start + s3Phase a) + shift := by
        ac_rfl
      rw [hnext]
      simpa [hstate] using htail

private theorem mod_partition_iff (left right total residue : Nat)
    (hpartition : left + right = total) (hresidue : residue < 3) :
    right % 3 = residue ↔
      total % 3 = (left % 3 + residue) % 3 := by
  rw [← hpartition, Nat.add_mod]
  have hleft := Nat.mod_lt left (by decide : 0 < 3)
  have hright := Nat.mod_lt right (by decide : 0 < 3)
  omega

/-- Even-final words with a fixed source-one self-loop residue. -/
def s3SelfLoopEvenSourceOneResidue (label : S3Alphabet)
    (residue : Nat) : Language S3Alphabet :=
  {word | (word.map s3Phase).sum = 0 ∧
    s3ArrowCountFrom 0 1 label word % 3 = residue}

/-- Boolean assembly of a source-one residue from the source-zero residue and
the ordinary occurrence count. -/
def s3SelfLoopSourceOneAssembly (label : S3Alphabet)
    (residue : Fin 3) : Language S3Alphabet :=
  ⋃ sourceZero : Fin 3,
    S3SelfLoopQuotients.evenResidue label sourceZero.1 ∩
      {word | word.count label % 3 = (sourceZero.1 + residue.1) % 3}

/-- The assembly language has the exact source-one semantics. -/
theorem s3SelfLoopSourceOneAssembly_eq (label : S3Alphabet)
    (residue : Fin 3) :
    s3SelfLoopSourceOneAssembly label residue =
      s3SelfLoopEvenSourceOneResidue label residue.1 := by
  ext word
  simp only [s3SelfLoopSourceOneAssembly, Set.mem_iUnion, Set.mem_inter_iff,
    S3SelfLoopQuotients.evenResidue, s3SelfLoopEvenSourceOneResidue,
    Set.mem_setOf_eq]
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

/-- Once source-zero even residues have height one, the source-one even
residues follow by finite Boolean assembly with ordinary counting. -/
theorem hasHeightAtMost_s3SelfLoopEvenSourceOne_of_zero
    (label : S3Alphabet) (hlabel : s3Phase label = 0)
    (hzero : HasHeightAtMost
      (S3SelfLoopQuotients.evenResidue label 0) 1)
    (residue : Fin 3) :
    HasHeightAtMost
      (s3SelfLoopEvenSourceOneResidue label residue.1) 1 := by
  have hassembly : HasHeightAtMost
      (s3SelfLoopSourceOneAssembly label residue) 1 := by
    apply HasHeightAtMost.iUnion
    intro sourceZero
    apply HasHeightAtMost.inter
    · exact S3SelfLoopQuotients.hasHeightAtMost_evenResidue_of_zero
        label hlabel hzero sourceZero
    · exact Counting.hasHeightAtMost_count label
        (Nat.mod_lt _ (by decide : 0 < 3))
  exact hassembly.congr (s3SelfLoopSourceOneAssembly_eq label residue)

end GSH
