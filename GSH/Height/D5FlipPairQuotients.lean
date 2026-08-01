import GSH.Height.D5FlipPairTransfer

/-! # All modulus-five residues for a fixed `D₅` reflection pair -/

set_option autoImplicit false

namespace GSH

namespace D5FlipPairQuotients

open S3ArrowArithmetic D5FlipPairTransfer

/-- Phase-zero words with a fixed-pair residue modulo five. -/
def d5PairResidue (x y : D5PhaseOne) (residue : Fin 5) :
    Language D5Alphabet :=
  {word | (word.map d5Phase).sum = 0 ∧
    pairCountOf x y (d5PhaseOneSubword word) % 5 = residue.1}

theorem d5PairResidue_zero (x y : D5PhaseOne) :
    d5PairResidue x y 0 = d5PairResidueZero x y := rfl

private theorem add_one_mod_five_eq_iff (n residue : Nat)
    (hresidue : residue < 5) :
    (1 + n) % 5 = residue ↔ n % 5 = (residue + 4) % 5 := by
  rw [Nat.add_mod]
  have hn := Nat.mod_lt n (by omega : 0 < 5)
  omega

private theorem phaseOneSubword_pair_prefix (x y : D5PhaseOne)
    (word : Word D5Alphabet) :
    d5PhaseOneSubword (x.1 :: y.1 :: word) =
      x :: y :: d5PhaseOneSubword word := by
  simp [d5PhaseOneSubword, x.2, y.2]

private theorem phase_sum_pair_prefix (x y : D5PhaseOne)
    (word : Word D5Alphabet) :
    ((x.1 :: y.1 :: word).map d5Phase).sum =
      (word.map d5Phase).sum := by
  simp only [List.map_cons, List.sum_cons, x.2, y.2]
  rw [← add_assoc, CharTwo.add_self_eq_zero]
  simp

private theorem pairCount_pair_prefix (x y : D5PhaseOne)
    (word : Word D5Alphabet) :
    pairCountOf x y
        (d5PhaseOneSubword (x.1 :: y.1 :: word)) =
      1 + pairCountOf x y (d5PhaseOneSubword word) := by
  rw [phaseOneSubword_pair_prefix]
  simp [pairCountOf]

/-- Prefixing the selected pair subtracts one from the residue. -/
theorem leftQuotient_pair_eq_pred (x y : D5PhaseOne)
    (residue : Fin 5) :
    Language.leftQuotient y.1
        (Language.leftQuotient x.1 (d5PairResidue x y residue)) =
      d5PairResidue x y
        ⟨(residue.1 + 4) % 5, Nat.mod_lt _ (by omega)⟩ := by
  ext word
  simp only [Language.mem_leftQuotient_iff, d5PairResidue,
    Set.mem_setOf_eq]
  rw [phase_sum_pair_prefix, pairCount_pair_prefix,
    add_one_mod_five_eq_iff _ residue.1 residue.isLt]

/-- Every actual phase-zero fixed-pair residue modulo five has generalized
star height at most one. -/
theorem hasHeightAtMost_d5PairResidue (x y : D5PhaseOne)
    (hne : x.1 ≠ y.1) (residue : Fin 5) :
    HasHeightAtMost (d5PairResidue x y residue) 1 := by
  have hzero : HasHeightAtMost (d5PairResidue x y 0) 1 := by
    rw [d5PairResidue_zero]
    exact hasHeightAtMost_d5PairResidue_zero x y hne
  have h4 : HasHeightAtMost (d5PairResidue x y 4) 1 :=
    ((hzero.leftQuotient x.1).leftQuotient y.1).congr
      (by simpa using leftQuotient_pair_eq_pred x y ⟨0, by omega⟩)
  have h3 : HasHeightAtMost (d5PairResidue x y 3) 1 :=
    ((h4.leftQuotient x.1).leftQuotient y.1).congr
      (by simpa using leftQuotient_pair_eq_pred x y ⟨4, by omega⟩)
  have h2 : HasHeightAtMost (d5PairResidue x y 2) 1 :=
    ((h3.leftQuotient x.1).leftQuotient y.1).congr
      (by simpa using leftQuotient_pair_eq_pred x y ⟨3, by omega⟩)
  have h1 : HasHeightAtMost (d5PairResidue x y 1) 1 :=
    ((h2.leftQuotient x.1).leftQuotient y.1).congr
      (by simpa using leftQuotient_pair_eq_pred x y ⟨2, by omega⟩)
  rcases residue with ⟨residue, hresidue⟩
  interval_cases residue <;> assumption

end D5FlipPairQuotients

end GSH
