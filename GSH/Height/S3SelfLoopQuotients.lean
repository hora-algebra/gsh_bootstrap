import GSH.Height.S3SelfLoopHeight

/-!
# Residue shifts for the `S₃` self-loop language

Prefixing a phase-zero label preserves the final phase and increments its
source-zero arrow count once.  Hence the two nonzero residues modulo three
are one-letter left quotients of the zero-residue language.  This avoids a
separate shifted version of the PST transfer formula.
-/

set_option autoImplicit false

namespace GSH

namespace S3SelfLoopQuotients

/-- Zero-final-phase words with a fixed source-zero self-loop residue. -/
def evenResidue (label : S3Alphabet) (residue : Nat) : Language S3Alphabet :=
  {word | (word.map s3Phase).sum = 0 ∧
    s3ArrowCountFrom 0 0 label word % 3 = residue}

private theorem add_one_mod_three_eq_zero_iff (n : Nat) :
    (1 + n) % 3 = 0 ↔ n % 3 = 2 := by
  rw [Nat.add_mod]
  have h := Nat.mod_lt n (by decide : 0 < 3)
  omega

private theorem add_one_mod_three_eq_two_iff (n : Nat) :
    (1 + n) % 3 = 2 ↔ n % 3 = 1 := by
  rw [Nat.add_mod]
  have h := Nat.mod_lt n (by decide : 0 < 3)
  omega

/-- Prefixing the counted phase-zero letter sends residue two to residue
zero, so one left quotient of the zero language is the residue-two
language. -/
theorem leftQuotient_zero_eq_two (label : S3Alphabet)
    (hlabel : s3Phase label = 0) :
    Language.leftQuotient label (evenResidue label 0) =
      evenResidue label 2 := by
  ext word
  simp only [Language.mem_leftQuotient_iff, evenResidue, Set.mem_setOf_eq]
  simp only [List.map_cons, List.sum_cons, hlabel, zero_add]
  rw [show s3ArrowCountFrom 0 0 label (label :: word) =
      1 + s3ArrowCountFrom 0 0 label word by
    simp [s3ArrowCountFrom, ArrowCounting.c2Step, hlabel]]
  rw [add_one_mod_three_eq_zero_iff]

/-- Prefixing twice shifts residue one to zero. -/
theorem leftQuotient_twice_zero_eq_one (label : S3Alphabet)
    (hlabel : s3Phase label = 0) :
    Language.leftQuotient label
        (Language.leftQuotient label (evenResidue label 0)) =
      evenResidue label 1 := by
  rw [leftQuotient_zero_eq_two label hlabel]
  ext word
  simp only [Language.mem_leftQuotient_iff, evenResidue, Set.mem_setOf_eq]
  simp only [List.map_cons, List.sum_cons, hlabel, zero_add]
  rw [show s3ArrowCountFrom 0 0 label (label :: word) =
      1 + s3ArrowCountFrom 0 0 label word by
    simp [s3ArrowCountFrom, ArrowCounting.c2Step, hlabel]]
  rw [add_one_mod_three_eq_two_iff]

/-- Height one for the zero-residue even language automatically gives height
one for all three residues, without a shifted Transfer formula. -/
theorem hasHeightAtMost_evenResidue_of_zero (label : S3Alphabet)
    (hlabel : s3Phase label = 0)
    (hzero : HasHeightAtMost (evenResidue label 0) 1)
    (residue : Fin 3) :
    HasHeightAtMost (evenResidue label residue.1) 1 := by
  rcases residue with ⟨residue, hresidue⟩
  interval_cases residue
  · exact hzero
  · exact ((hzero.leftQuotient label).leftQuotient label).congr
      (leftQuotient_twice_zero_eq_one label hlabel)
  · exact (hzero.leftQuotient label).congr
      (leftQuotient_zero_eq_two label hlabel)

end S3SelfLoopQuotients

end GSH
