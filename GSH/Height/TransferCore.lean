import GSH.Height.Closure

/-!
# The height-one core of the PST transfer lemma

Pin--Straubing--Thérien's transfer lemma rewrites a nested-looking counting
expression as a finite union of intersections with only one level of Kleene
star.  This file records exactly the height-theoretic right-hand side of that
rewrite.  It deliberately does not assert that an arbitrary language is equal
to the formula: the prefix-code factorization establishing that equality is a
separate semantic obligation for the `S₃` consumer.
-/

set_option autoImplicit false

namespace GSH

universe u

namespace HasHeightAtMost

variable {alpha : Type u}

/-- Concatenation preserves a common generalized-star-height bound. -/
theorem concat {L K : Language alpha} {n : Nat}
    (hL : HasHeightAtMost L n) (hK : HasHeightAtMost K n) :
    HasHeightAtMost (Language.concat L K) n := by
  obtain ⟨r, hr, hrHeight⟩ := hL
  obtain ⟨s, hs, hsHeight⟩ := hK
  refine ⟨GRegex.concat r s, ?_, ?_⟩
  · simp [GRegex.denote, hr, hs]
  · simpa [GRegex.starHeight] using max_le hrHeight hsHeight

/-- A fixed concatenation power preserves generalized star height. -/
theorem power {L : Language alpha} {n : Nat} (hL : HasHeightAtMost L n)
    (k : Nat) : HasHeightAtMost (Language.power L k) n := by
  obtain ⟨r, hr, hrHeight⟩ := hL
  refine ⟨GRegex.pow r k, ?_, ?_⟩
  · simp [hr]
  · exact (GRegex.starHeight_pow_le r k).trans hrHeight

/-- One Kleene star raises a generalized-star-height bound by at most one. -/
theorem star {L : Language alpha} {n : Nat} (hL : HasHeightAtMost L n) :
    HasHeightAtMost (Language.star L) (n + 1) := by
  obtain ⟨r, hr, hrHeight⟩ := hL
  refine ⟨GRegex.star r, ?_, ?_⟩
  · simp [GRegex.denote, hr]
  · simpa [GRegex.starHeight] using Nat.add_le_add_right hrHeight 1

end HasHeightAtMost

namespace TransferCore

variable {alpha : Type u}

/-- One cell in the explicit Boolean formula from PST Lemma 6.1.

`L0` is the distinguished codeword language and `L1` is the language of
return blocks.  The index `r` records the common length/count residue modulo
`modulus` in the two-letter source code. -/
def cell (L0 L1 : Language alpha) (modulus residue : Nat) : Language alpha :=
  let alphabet := L0 ∪ L1
  let lengthSide := Language.concat
    (Language.star (Language.power alphabet modulus))
    (Language.power alphabet residue)
  let countTail := L0 ∪ Language.concat
    (Language.power (Language.concat L1 (Language.star L0)) (modulus - 1)) L1
  let countSide := Language.concat
    (Language.power (Language.concat (Language.star L0) L1) residue)
    (Language.star countTail)
  lengthSide ∩ countSide

/-- The finite union of the transfer cells for all residues below `modulus`. -/
def formula (L0 L1 : Language alpha) (modulus : Nat) : Language alpha :=
  ⋃ residue : Fin modulus, cell L0 L1 modulus residue.1

/-- The explicit transfer formula has generalized star height at most one.

This is the height-theoretic half of PST Lemma 6.1.  The hypotheses are exactly
the three star-free inputs used in the printed proof: `L0`, `L1`, and `L0*`.
No prefix-code or language-equality claim is hidden here. -/
theorem hasHeightAtMost_formula (L0 L1 : Language alpha) (modulus : Nat)
    (hL0 : IsStarFree L0) (hL1 : IsStarFree L1)
    (hL0Star : IsStarFree (Language.star L0)) :
    HasHeightAtMost (formula L0 L1 modulus) 1 := by
  apply HasHeightAtMost.iUnion
  intro residue
  apply HasHeightAtMost.inter
  · apply HasHeightAtMost.concat
    · exact ((hL0.union hL1).power modulus).star
    · exact ((hL0.union hL1).power residue.1).mono (by omega)
  · apply HasHeightAtMost.concat
    · exact (hL0Star.concat hL1).power residue.1 |>.mono (by omega)
    · apply HasHeightAtMost.star
      exact hL0.union
        (((hL1.concat hL0Star).power (modulus - 1)).concat hL1)

end TransferCore

end GSH
