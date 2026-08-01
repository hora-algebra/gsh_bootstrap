import GSH.Height.D4FlipPairTransfer

/-!
# All modulus-eight residues for a fixed `D₄` reflection pair

Prefixing the fixed phase-one pair preserves total phase and adds exactly one
to the canonical ordered-pair count.  Repeated left quotients therefore move
the verified zero-residue height bound around all eight residues.
-/

set_option autoImplicit false

namespace GSH

namespace D4FlipPairQuotients

open S3ArrowArithmetic
open D4ArrowArithmetic
open D4FlipPairTransfer

/-- Phase-zero words with a prescribed fixed-pair residue modulo eight. -/
def d4PairResidue (x y : D4PhaseOne) (residue : Fin 8) :
    Language D4Alphabet :=
  {word | (word.map d4Phase).sum = 0 ∧
    pairCountOf x y (d4PhaseOneSubword word) % 8 = residue.1}

theorem d4PairResidue_zero (x y : D4PhaseOne) :
    d4PairResidue x y 0 = d4PairResidueZero x y := rfl

private theorem add_one_mod_eight_eq_iff (n residue : Nat)
    (hresidue : residue < 8) :
    (1 + n) % 8 = residue ↔ n % 8 = (residue + 7) % 8 := by
  rw [Nat.add_mod]
  have hn := Nat.mod_lt n (by omega : 0 < 8)
  omega

private theorem phaseOneSubword_pair_prefix (x y : D4PhaseOne)
    (word : Word D4Alphabet) :
    d4PhaseOneSubword (x.1 :: y.1 :: word) =
      x :: y :: d4PhaseOneSubword word := by
  simp [d4PhaseOneSubword, x.2, y.2]

private theorem phase_sum_pair_prefix (x y : D4PhaseOne)
    (word : Word D4Alphabet) :
    ((x.1 :: y.1 :: word).map d4Phase).sum =
      (word.map d4Phase).sum := by
  simp only [List.map_cons, List.sum_cons, x.2, y.2]
  rw [← add_assoc, CharTwo.add_self_eq_zero]
  simp

private theorem pairCount_pair_prefix (x y : D4PhaseOne)
    (word : Word D4Alphabet) :
    pairCountOf x y
        (d4PhaseOneSubword (x.1 :: y.1 :: word)) =
      1 + pairCountOf x y (d4PhaseOneSubword word) := by
  rw [phaseOneSubword_pair_prefix]
  simp [pairCountOf]

/-- One fixed-pair prefix subtracts one from the requested residue modulo
eight. -/
theorem leftQuotient_pair_eq_pred (x y : D4PhaseOne)
    (residue : Fin 8) :
    Language.leftQuotient y.1
        (Language.leftQuotient x.1
          (d4PairResidue x y residue)) =
      d4PairResidue x y ⟨(residue.1 + 7) % 8, Nat.mod_lt _ (by omega)⟩ := by
  ext word
  simp only [Language.mem_leftQuotient_iff, d4PairResidue,
    Set.mem_setOf_eq]
  rw [phase_sum_pair_prefix, pairCount_pair_prefix,
    add_one_mod_eight_eq_iff _ residue.1 residue.isLt]

/-- Every actual phase-zero fixed-pair residue modulo eight has generalized
star height at most one. -/
theorem hasHeightAtMost_d4PairResidue (x y : D4PhaseOne)
    (hne : x.1 ≠ y.1) (residue : Fin 8) :
    HasHeightAtMost (d4PairResidue x y residue) 1 := by
  have hzero : HasHeightAtMost (d4PairResidue x y 0) 1 := by
    rw [d4PairResidue_zero]
    exact hasHeightAtMost_d4PairResidue_zero x y hne
  have h7 : HasHeightAtMost (d4PairResidue x y 7) 1 :=
    ((hzero.leftQuotient x.1).leftQuotient y.1).congr
      (by simpa using leftQuotient_pair_eq_pred x y ⟨0, by omega⟩)
  have h6 : HasHeightAtMost (d4PairResidue x y 6) 1 :=
    ((h7.leftQuotient x.1).leftQuotient y.1).congr
      (by simpa using leftQuotient_pair_eq_pred x y ⟨7, by omega⟩)
  have h5 : HasHeightAtMost (d4PairResidue x y 5) 1 :=
    ((h6.leftQuotient x.1).leftQuotient y.1).congr
      (by simpa using leftQuotient_pair_eq_pred x y ⟨6, by omega⟩)
  have h4 : HasHeightAtMost (d4PairResidue x y 4) 1 :=
    ((h5.leftQuotient x.1).leftQuotient y.1).congr
      (by simpa using leftQuotient_pair_eq_pred x y ⟨5, by omega⟩)
  have h3 : HasHeightAtMost (d4PairResidue x y 3) 1 :=
    ((h4.leftQuotient x.1).leftQuotient y.1).congr
      (by simpa using leftQuotient_pair_eq_pred x y ⟨4, by omega⟩)
  have h2 : HasHeightAtMost (d4PairResidue x y 2) 1 :=
    ((h3.leftQuotient x.1).leftQuotient y.1).congr
      (by simpa using leftQuotient_pair_eq_pred x y ⟨3, by omega⟩)
  have h1 : HasHeightAtMost (d4PairResidue x y 1) 1 :=
    ((h2.leftQuotient x.1).leftQuotient y.1).congr
      (by simpa using leftQuotient_pair_eq_pred x y ⟨2, by omega⟩)
  rcases residue with ⟨residue, hresidue⟩
  interval_cases residue <;> assumption

end D4FlipPairQuotients

end GSH
