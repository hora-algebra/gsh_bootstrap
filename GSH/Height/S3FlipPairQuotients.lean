import GSH.Height.S3FlipPairTransfer

/-!
# Residue shifts for canonical `S₃` flip pairs

Prefixing the fixed phase-one pair `[x,y]` preserves total phase and adds
one to its fixed-block pair count.  Repeated one-letter left quotients
therefore transfer the height-one result for residue zero to all residues
modulo three.
-/

set_option autoImplicit false

namespace GSH

namespace S3FlipPairQuotients

open S3ArrowArithmetic
open S3FlipPairTransfer

/-- Even-phase words with a prescribed fixed-pair residue modulo three. -/
def s3PairResidue (x y : S3PhaseOne) (residue : Nat) :
    Language S3Alphabet :=
  {word | (word.map s3Phase).sum = 0 ∧
    pairCountOf x y (phaseOneSubword word) % 3 = residue}

/-- The new residue-family definition agrees definitionally with the existing
zero-residue transfer language. -/
theorem s3PairResidue_zero (x y : S3PhaseOne) :
    s3PairResidue x y 0 = s3PairResidueZero x y := rfl

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

private theorem phaseOneSubword_pair_prefix (x y : S3PhaseOne)
    (word : Word S3Alphabet) :
    phaseOneSubword (x.1 :: y.1 :: word) =
      x :: y :: phaseOneSubword word := by
  simp [phaseOneSubword, x.2, y.2]

private theorem phase_sum_pair_prefix (x y : S3PhaseOne)
    (word : Word S3Alphabet) :
    ((x.1 :: y.1 :: word).map s3Phase).sum =
      (word.map s3Phase).sum := by
  simp only [List.map_cons, List.sum_cons, x.2, y.2]
  rw [← add_assoc, CharTwo.add_self_eq_zero]
  simp

private theorem pairCount_pair_prefix (x y : S3PhaseOne)
    (word : Word S3Alphabet) :
    pairCountOf x y (phaseOneSubword (x.1 :: y.1 :: word)) =
      1 + pairCountOf x y (phaseOneSubword word) := by
  rw [phaseOneSubword_pair_prefix]
  simp [pairCountOf]

/-- One fixed-pair prefix shifts residue two into residue zero. -/
theorem leftQuotient_pair_zero_eq_two (x y : S3PhaseOne)
    (_hne : x.1 ≠ y.1) :
    Language.leftQuotient y.1
        (Language.leftQuotient x.1 (s3PairResidue x y 0)) =
      s3PairResidue x y 2 := by
  ext word
  simp only [Language.mem_leftQuotient_iff, s3PairResidue,
    Set.mem_setOf_eq]
  rw [phase_sum_pair_prefix, pairCount_pair_prefix,
    add_one_mod_three_eq_zero_iff]

/-- Two fixed-pair prefixes shift residue one into residue zero. -/
theorem leftQuotient_pair_twice_zero_eq_one (x y : S3PhaseOne)
    (hne : x.1 ≠ y.1) :
    Language.leftQuotient y.1
        (Language.leftQuotient x.1
          (Language.leftQuotient y.1
            (Language.leftQuotient x.1 (s3PairResidue x y 0)))) =
      s3PairResidue x y 1 := by
  rw [leftQuotient_pair_zero_eq_two x y hne]
  ext word
  simp only [Language.mem_leftQuotient_iff, s3PairResidue,
    Set.mem_setOf_eq]
  rw [phase_sum_pair_prefix, pairCount_pair_prefix,
    add_one_mod_three_eq_two_iff]

/-- Every fixed-pair residue has generalized star-height at most one. -/
theorem hasHeightAtMost_s3PairResidue (x y : S3PhaseOne)
    (hne : x.1 ≠ y.1) (residue : Fin 3) :
    HasHeightAtMost (s3PairResidue x y residue.1) 1 := by
  have hzero : HasHeightAtMost (s3PairResidue x y 0) 1 := by
    rw [s3PairResidue_zero]
    exact hasHeightAtMost_s3PairResidue_zero x y hne
  rcases residue with ⟨residue, hresidue⟩
  interval_cases residue
  · exact hzero
  · have htwo := (hzero.leftQuotient x.1).leftQuotient y.1
    have hone := (htwo.leftQuotient x.1).leftQuotient y.1
    exact hone.congr (leftQuotient_pair_twice_zero_eq_one x y hne)
  · exact ((hzero.leftQuotient x.1).leftQuotient y.1).congr
      (leftQuotient_pair_zero_eq_two x y hne)

end S3FlipPairQuotients

end GSH
