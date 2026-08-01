import GSH.Height.TransferSemantics

/-!
# Arbitrary-modulus length semantics for the PST transfer formula

This file removes the fixed modulus three from the length half of
`TransferCore.formula`.  `TransferSemantics.TokenMod` supplies the matching
arbitrary-positive-modulus Boolean grouping theorem.  The remaining bridge is
to lift that grouping to the actual `L0/L1` codewords in the count half.
-/

set_option autoImplicit false

namespace GSH

universe u

namespace TransferSemantics

variable {alpha : Type u}

/-- A power of `modulus`-codeword blocks is a factorization whose length is
`modulus * k`. -/
theorem mem_power_power_modulus_iff (code : Language alpha) (modulus k : Nat)
    (word : Word alpha) :
    word ∈ Language.power (Language.power code modulus) k ↔
      ∃ pieces : List (Word alpha),
        Factorizes code pieces word ∧ pieces.length = modulus * k := by
  induction k generalizing word with
  | zero =>
      constructor
      · intro hword
        have : word = [] := by simpa [Language.power, Language.epsilon] using hword
        subst word
        exact ⟨[], factorizes_nil code, by simp⟩
      · rintro ⟨pieces, hpieces, hlength⟩
        have hp : pieces = [] := by
          cases pieces with
          | nil => rfl
          | cons piece pieces => simp at hlength
        subst pieces
        simpa [Language.power, Language.epsilon] using hpieces.2.symm
  | succ k ih =>
      rw [Language.power_succ_left]
      constructor
      · rintro ⟨first, hfirst, rest, hrest, rfl⟩
        obtain ⟨firstPieces, hfirstPieces, hfirstLength⟩ :=
          (mem_power_iff_factorizes_length code modulus first).mp hfirst
        obtain ⟨restPieces, hrestPieces, hrestLength⟩ := (ih rest).mp hrest
        exact ⟨firstPieces ++ restPieces,
          factorizes_append hfirstPieces hrestPieces, by
            simp only [List.length_append, hfirstLength, hrestLength]
            rw [Nat.mul_succ]
            omega⟩
      · rintro ⟨pieces, hpieces, hlength⟩
        let firstPieces := pieces.take modulus
        let restPieces := pieces.drop modulus
        have hmodulusLe : modulus ≤ pieces.length := by
          rw [hlength, Nat.mul_succ]
          omega
        have hfirstLength : firstPieces.length = modulus := by
          simp [firstPieces, List.length_take, hmodulusLe]
        have hrestLength : restPieces.length = modulus * k := by
          simp [restPieces, List.length_drop, hlength, Nat.mul_succ]
        have hfirstPieces : Factorizes code firstPieces firstPieces.flatten := by
          constructor
          · intro piece hpiece
            exact hpieces.1 piece (List.mem_of_mem_take hpiece)
          · rfl
        have hrestPieces : Factorizes code restPieces restPieces.flatten := by
          constructor
          · intro piece hpiece
            exact hpieces.1 piece (List.mem_of_mem_drop hpiece)
          · rfl
        have hfirst : firstPieces.flatten ∈ Language.power code modulus :=
          (mem_power_iff_factorizes_length code modulus firstPieces.flatten).mpr
            ⟨firstPieces, hfirstPieces, hfirstLength⟩
        have hrest : restPieces.flatten ∈ Language.power
            (Language.power code modulus) k :=
          (ih restPieces.flatten).mpr ⟨restPieces, hrestPieces, hrestLength⟩
        refine ⟨firstPieces.flatten, hfirst, restPieces.flatten, hrest, ?_⟩
        rw [← List.flatten_append]
        change (pieces.take modulus ++ pieces.drop modulus).flatten = word
        rw [List.take_append_drop, hpieces.2]

/-- The star of `modulus`-codeword blocks consists exactly of factorizations
whose number of codewords is divisible by `modulus`. -/
theorem mem_star_power_modulus_iff (code : Language alpha) (modulus : Nat)
    (word : Word alpha) :
    word ∈ Language.star (Language.power code modulus) ↔
      ∃ pieces : List (Word alpha),
        Factorizes code pieces word ∧ pieces.length % modulus = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨pieces, hpieces, hlength⟩ :=
      (mem_power_power_modulus_iff code modulus k word).mp hk
    exact ⟨pieces, hpieces, by simp [hlength]⟩
  · rintro ⟨pieces, hpieces, hmod⟩
    have hdiv : modulus ∣ pieces.length := Nat.dvd_of_mod_eq_zero hmod
    obtain ⟨k, hk⟩ := hdiv
    refine ⟨k, (mem_power_power_modulus_iff code modulus k word).mpr
      ⟨pieces, hpieces, ?_⟩⟩
    omega

/-- Exact semantics of the length half of a transfer cell for every positive
modulus and every valid residue. -/
theorem mem_lengthSide_modulus_iff (code : Language alpha)
    (modulus residue : Nat) (hresidue : residue < modulus)
    (word : Word alpha) :
    word ∈ Language.concat
        (Language.star (Language.power code modulus))
        (Language.power code residue) ↔
      ∃ pieces : List (Word alpha),
        Factorizes code pieces word ∧ pieces.length % modulus = residue := by
  constructor
  · rintro ⟨left, hleft, right, hright, rfl⟩
    obtain ⟨leftPieces, hleftPieces, hleftMod⟩ :=
      (mem_star_power_modulus_iff code modulus left).mp hleft
    obtain ⟨rightPieces, hrightPieces, hrightLength⟩ :=
      (mem_power_iff_factorizes_length code residue right).mp hright
    refine ⟨leftPieces ++ rightPieces,
      factorizes_append hleftPieces hrightPieces, ?_⟩
    simp only [List.length_append, hrightLength]
    rw [Nat.add_mod, hleftMod, Nat.mod_eq_of_lt hresidue]
    simpa using Nat.mod_eq_of_lt hresidue
  · rintro ⟨pieces, hpieces, hmod⟩
    obtain ⟨k, hlength⟩ := (Counting.count_mod_iff hresidue).mp hmod
    let leftPieces := pieces.take (modulus * k)
    let rightPieces := pieces.drop (modulus * k)
    have hleftLength : leftPieces.length = modulus * k := by
      simp only [leftPieces, List.length_take]
      omega
    have hrightLength : rightPieces.length = residue := by
      simp only [rightPieces, List.length_drop]
      omega
    have hleftPieces : Factorizes code leftPieces leftPieces.flatten := by
      constructor
      · intro piece hpiece
        exact hpieces.1 piece (List.mem_of_mem_take hpiece)
      · rfl
    have hrightPieces : Factorizes code rightPieces rightPieces.flatten := by
      constructor
      · intro piece hpiece
        exact hpieces.1 piece (List.mem_of_mem_drop hpiece)
      · rfl
    have hleft : leftPieces.flatten ∈
        Language.star (Language.power code modulus) :=
      (mem_star_power_modulus_iff code modulus leftPieces.flatten).mpr
        ⟨leftPieces, hleftPieces, by simp [hleftLength]⟩
    have hright : rightPieces.flatten ∈ Language.power code residue :=
      (mem_power_iff_factorizes_length code residue rightPieces.flatten).mpr
        ⟨rightPieces, hrightPieces, hrightLength⟩
    refine ⟨leftPieces.flatten, hleft, rightPieces.flatten, hright, ?_⟩
    rw [← List.flatten_append]
    change (pieces.take (modulus * k) ++ pieces.drop (modulus * k)).flatten = word
    rw [List.take_append_drop, hpieces.2]

end TransferSemantics

end GSH
