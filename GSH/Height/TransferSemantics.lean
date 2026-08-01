import GSH.Height.FullAlphabet
import GSH.Height.Counting
import GSH.Height.TransferCore

/-!
# Finite factorization semantics for the PST transfer formula

This file records the elementary bridge between language powers/stars and
finite lists of codewords.  It is the semantic bookkeeping needed to prove
that `TransferCore.formula` counts one side of a prefix code.
-/

set_option autoImplicit false

namespace GSH

universe u

namespace TransferSemantics

variable {alpha : Type u}

/-- Number of pieces belonging to an arbitrary language.  This is
noncomputable only because a semantic language need not come with executable
membership. -/
noncomputable def countIn (language : Language alpha)
    (pieces : List (Word alpha)) : Nat := by
  classical
  exact pieces.countP fun piece => decide (piece ∈ language)

theorem countIn_append (language : Language alpha)
    (left right : List (Word alpha)) :
    countIn language (left ++ right) =
      countIn language left + countIn language right := by
  classical
  simp [countIn]

theorem countIn_letter_eq_count [DecidableEq alpha] (label : alpha)
    (pieces : List (Word alpha)) :
    countIn (Language.letter label) pieces = pieces.count [label] := by
  classical
  unfold countIn List.count
  apply List.countP_congr
  intro piece _
  simp [Language.mem_letter_iff]

/-- `pieces` is a factorization of `word` into members of `code`. -/
def Factorizes (code : Language alpha) (pieces : List (Word alpha))
    (word : Word alpha) : Prop :=
  (∀ piece ∈ pieces, piece ∈ code) ∧ pieces.flatten = word

theorem factorizes_nil (code : Language alpha) :
    Factorizes code [] [] := by
  simp [Factorizes]

theorem factorizes_cons {code : Language alpha} {piece : Word alpha}
    {pieces : List (Word alpha)} {word : Word alpha}
    (hpiece : piece ∈ code) (hpieces : Factorizes code pieces word) :
    Factorizes code (piece :: pieces) (piece ++ word) := by
  rcases hpieces with ⟨hall, rfl⟩
  constructor
  · intro other hother
    simp only [List.mem_cons] at hother
    rcases hother with rfl | hother
    · exact hpiece
    · exact hall other hother
  · simp

/-- Concatenating two block factorizations concatenates both their piece lists
and the represented words. -/
theorem factorizes_append {code : Language alpha} {leftPieces rightPieces :
    List (Word alpha)} {leftWord rightWord : Word alpha}
    (hleft : Factorizes code leftPieces leftWord)
    (hright : Factorizes code rightPieces rightWord) :
    Factorizes code (leftPieces ++ rightPieces) (leftWord ++ rightWord) := by
  rcases hleft with ⟨hleft, rfl⟩
  rcases hright with ⟨hright, rfl⟩
  constructor
  · intro piece hpiece
    rw [List.mem_append] at hpiece
    exact hpiece.elim (hleft piece) (hright piece)
  · simp

/-- Membership in a fixed language power is exactly a factorization of the
specified length. -/
theorem mem_power_iff_factorizes_length (code : Language alpha) (n : Nat)
    (word : Word alpha) :
    word ∈ Language.power code n ↔
      ∃ pieces : List (Word alpha),
        Factorizes code pieces word ∧ pieces.length = n := by
  induction n generalizing word with
  | zero =>
      constructor
      · intro hword
        have : word = [] := by simpa [Language.power, Language.epsilon] using hword
        subst word
        exact ⟨[], factorizes_nil code, rfl⟩
      · rintro ⟨pieces, hpieces, hlength⟩
        cases pieces with
        | nil =>
            simpa [Factorizes, Language.power, Language.epsilon] using hpieces.2.symm
        | cons piece pieces => simp at hlength
  | succ n ih =>
      rw [Language.power_succ_left]
      constructor
      · rintro ⟨piece, hpiece, rest, hrest, rfl⟩
        obtain ⟨pieces, hpieces, hlength⟩ := (ih rest).mp hrest
        exact ⟨piece :: pieces, factorizes_cons hpiece hpieces, by simp [hlength]⟩
      · rintro ⟨pieces, hpieces, hlength⟩
        cases pieces with
        | nil => simp at hlength
        | cons piece pieces =>
            have hpiece : piece ∈ code := hpieces.1 piece (by simp)
            have htail : Factorizes code pieces pieces.flatten := by
              constructor
              · intro other hother
                exact hpieces.1 other (by simp [hother])
              · rfl
            have hlen : pieces.length = n := by simpa using hlength
            have hrest : pieces.flatten ∈ Language.power code n :=
              (ih pieces.flatten).mpr ⟨pieces, htail, hlen⟩
            exact ⟨piece, hpiece, pieces.flatten, hrest, hpieces.2⟩

/-- Membership in a Kleene star is exactly some finite factorization. -/
theorem mem_star_iff_factorizes (code : Language alpha) (word : Word alpha) :
    word ∈ Language.star code ↔
      ∃ pieces : List (Word alpha), Factorizes code pieces word := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨pieces, hpieces, -⟩ :=
      (mem_power_iff_factorizes_length code n word).mp hn
    exact ⟨pieces, hpieces⟩
  · rintro ⟨pieces, hpieces⟩
    exact ⟨pieces.length,
      (mem_power_iff_factorizes_length code pieces.length word).mpr
        ⟨pieces, hpieces, rfl⟩⟩

/-- A power of three-codeword blocks is exactly a factorization whose length
is three times the outer exponent.  This is the fixed-modulus grouping lemma
used by the `S₃` consumer. -/
theorem mem_power_power_three_iff (code : Language alpha) (k : Nat)
    (word : Word alpha) :
    word ∈ Language.power (Language.power code 3) k ↔
      ∃ pieces : List (Word alpha),
        Factorizes code pieces word ∧ pieces.length = 3 * k := by
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
          (mem_power_iff_factorizes_length code 3 first).mp hfirst
        obtain ⟨restPieces, hrestPieces, hrestLength⟩ :=
          (ih rest).mp hrest
        exact ⟨firstPieces ++ restPieces,
          factorizes_append hfirstPieces hrestPieces, by
            simp only [List.length_append, hfirstLength, hrestLength]
            omega⟩
      · rintro ⟨pieces, hpieces, hlength⟩
        let firstPieces := pieces.take 3
        let restPieces := pieces.drop 3
        have hfirstLength : firstPieces.length = 3 := by
          simp only [firstPieces, List.length_take]
          omega
        have hrestLength : restPieces.length = 3 * k := by
          simp only [restPieces, List.length_drop]
          omega
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
        have hfirst : firstPieces.flatten ∈ Language.power code 3 :=
          (mem_power_iff_factorizes_length code 3 firstPieces.flatten).mpr
            ⟨firstPieces, hfirstPieces, hfirstLength⟩
        have hrest : restPieces.flatten ∈
            Language.power (Language.power code 3) k :=
          (ih restPieces.flatten).mpr ⟨restPieces, hrestPieces, hrestLength⟩
        refine ⟨firstPieces.flatten, hfirst, restPieces.flatten, hrest, ?_⟩
        rw [← List.flatten_append]
        change (pieces.take 3 ++ pieces.drop 3).flatten = word
        rw [List.take_append_drop, hpieces.2]

/-- The star of three-codeword blocks consists exactly of factorizations
whose number of codewords is divisible by three. -/
theorem mem_star_power_three_iff (code : Language alpha) (word : Word alpha) :
    word ∈ Language.star (Language.power code 3) ↔
      ∃ pieces : List (Word alpha),
        Factorizes code pieces word ∧ pieces.length % 3 = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨pieces, hpieces, hlength⟩ :=
      (mem_power_power_three_iff code k word).mp hk
    exact ⟨pieces, hpieces, by simp [hlength]⟩
  · rintro ⟨pieces, hpieces, hmod⟩
    have hdiv : 3 ∣ pieces.length := Nat.dvd_of_mod_eq_zero hmod
    obtain ⟨k, hk⟩ := hdiv
    refine ⟨k, (mem_power_power_three_iff code k word).mpr ⟨pieces, hpieces, ?_⟩⟩
    omega

/-- The length half of a modulus-three transfer cell. -/
theorem mem_lengthSide_three_iff (code : Language alpha) (residue : Nat)
    (hresidue : residue < 3) (word : Word alpha) :
    word ∈ Language.concat
        (Language.star (Language.power code 3))
        (Language.power code residue) ↔
      ∃ pieces : List (Word alpha),
        Factorizes code pieces word ∧ pieces.length % 3 = residue := by
  constructor
  · rintro ⟨left, hleft, right, hright, rfl⟩
    obtain ⟨leftPieces, hleftPieces, hleftMod⟩ :=
      (mem_star_power_three_iff code left).mp hleft
    obtain ⟨rightPieces, hrightPieces, hrightLength⟩ :=
      (mem_power_iff_factorizes_length code residue right).mp hright
    refine ⟨leftPieces ++ rightPieces,
      factorizes_append hleftPieces hrightPieces, ?_⟩
    simp only [List.length_append, hrightLength]
    omega
  · rintro ⟨pieces, hpieces, hmod⟩
    obtain ⟨k, hlength⟩ := (Counting.count_mod_iff hresidue).mp hmod
    let leftPieces := pieces.take (3 * k)
    let rightPieces := pieces.drop (3 * k)
    have hleftLength : leftPieces.length = 3 * k := by
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
        Language.star (Language.power code 3) :=
      (mem_star_power_three_iff code leftPieces.flatten).mpr
        ⟨leftPieces, hleftPieces, by simp [hleftLength]⟩
    have hright : rightPieces.flatten ∈ Language.power code residue :=
      (mem_power_iff_factorizes_length code residue rightPieces.flatten).mpr
        ⟨rightPieces, hrightPieces, hrightLength⟩
    refine ⟨leftPieces.flatten, hleft, rightPieces.flatten, hright, ?_⟩
    rw [← List.flatten_append]
    change (pieces.take (3 * k) ++ pieces.drop (3 * k)).flatten = word
    rw [List.take_append_drop, hpieces.2]

section CountSide

variable [DecidableEq alpha]

/-- Number of code pieces which are not the distinguished singleton. -/
def otherCount (label : alpha) (pieces : List (Word alpha)) : Nat :=
  pieces.countP fun piece => decide (piece ≠ [label])

theorem otherCount_append (label : alpha) (left right : List (Word alpha)) :
    otherCount label (left ++ right) =
      otherCount label left + otherCount label right := by
  simp [otherCount]

/-- Every word in `language` has a code factorization with exactly `amount`
non-distinguished pieces. -/
def EncodesExact (code : Language alpha) (label : alpha)
    (language : Language alpha) (amount : Nat) : Prop :=
  ∀ word ∈ language, ∃ pieces : List (Word alpha),
    Factorizes code pieces word ∧ otherCount label pieces = amount

theorem EncodesExact.concat {code : Language alpha} {label : alpha}
    {left right : Language alpha} {leftAmount rightAmount : Nat}
    (hleft : EncodesExact code label left leftAmount)
    (hright : EncodesExact code label right rightAmount) :
    EncodesExact code label (Language.concat left right)
      (leftAmount + rightAmount) := by
  intro word hword
  rcases hword with ⟨u, hu, v, hv, rfl⟩
  obtain ⟨up, hup, huc⟩ := hleft u hu
  obtain ⟨vp, hvp, hvc⟩ := hright v hv
  exact ⟨up ++ vp, factorizes_append hup hvp, by
    rw [otherCount_append, huc, hvc]⟩

theorem EncodesExact.power {code : Language alpha} {label : alpha}
    {language : Language alpha} {amount : Nat}
    (hlanguage : EncodesExact code label language amount) (n : Nat) :
    EncodesExact code label (Language.power language n) (amount * n) := by
  induction n with
  | zero =>
      intro word hword
      have : word = [] := by simpa [Language.power, Language.epsilon] using hword
      subst word
      exact ⟨[], factorizes_nil code, by simp [otherCount]⟩
  | succ n ih =>
      rw [Language.power_succ_left]
      simpa [Nat.mul_succ, Nat.add_comm] using hlanguage.concat ih

theorem EncodesExact.star_zero {code : Language alpha} {label : alpha}
    {language : Language alpha}
    (hlanguage : EncodesExact code label language 0) :
    EncodesExact code label (Language.star language) 0 := by
  intro word hword
  rcases hword with ⟨n, hn⟩
  simpa using hlanguage.power n word hn

theorem encodesExact_letter_zero (code : Language alpha) (label : alpha)
    (hsubset : Language.letter label ⊆ code) :
    EncodesExact code label (Language.letter label) 0 := by
  intro word hword
  have hw : word = [label] := hword
  subst word
  exact ⟨[[label]], by
    constructor
    · intro piece hpiece
      have : piece = [label] := by simpa using hpiece
      subst piece
      exact hsubset rfl
    · simp, by simp [otherCount]⟩

theorem encodesExact_other_one (code other : Language alpha) (label : alpha)
    (hsubset : other ⊆ code) (hne : ∀ word ∈ other, word ≠ [label]) :
    EncodesExact code label other 1 := by
  intro word hword
  exact ⟨[word], by
    constructor
    · intro piece hpiece
      have : piece = word := by simpa using hpiece
      subst piece
      exact hsubset hword
    · simp, by simp [otherCount, hne word hword]⟩

/-- Forward normalization of the count half of a modulus-three transfer
cell.  It does not require unique decipherability; that is needed only to
identify this factorization with the one supplied by the length half. -/
theorem mem_countSide_three_imp (L0 L1 : Language alpha) (label : alpha)
    (hL0 : L0 = Language.letter label)
    (hdisjoint : ∀ word ∈ L1, word ≠ [label])
    (residue : Nat) (word : Word alpha)
    (hword : word ∈ Language.concat
      (Language.power (Language.concat (Language.star L0) L1) residue)
      (Language.star
        (L0 ∪ Language.concat
          (Language.power (Language.concat L1 (Language.star L0)) 2) L1))) :
    ∃ pieces : List (Word alpha),
      Factorizes (L0 ∪ L1) pieces word ∧
        otherCount label pieces % 3 = residue % 3 := by
  subst L0
  let code : Language alpha := Language.letter label ∪ L1
  have hletter : EncodesExact code label (Language.letter label) 0 :=
    encodesExact_letter_zero code label (by intro w hw; exact Or.inl hw)
  have hother : EncodesExact code label L1 1 :=
    encodesExact_other_one code L1 label (by intro w hw; exact Or.inr hw) hdisjoint
  have hletterStar : EncodesExact code label
      (Language.star (Language.letter label)) 0 := hletter.star_zero
  have hprefix : EncodesExact code label
      (Language.power
        (Language.concat (Language.star (Language.letter label)) L1) residue)
      residue := by
    simpa using (hletterStar.concat hother).power residue
  have htriple : EncodesExact code label
      (Language.concat
        (Language.power
          (Language.concat L1 (Language.star (Language.letter label))) 2) L1) 3 := by
    have hpair := (hother.concat hletterStar).power 2
    simpa using hpair.concat hother
  have htailCell : ∀ cell ∈
      (Language.letter label ∪ Language.concat
        (Language.power
          (Language.concat L1 (Language.star (Language.letter label))) 2) L1),
      ∃ pieces : List (Word alpha), Factorizes code pieces cell ∧
        otherCount label pieces % 3 = 0 := by
    intro cell hcell
    rcases hcell with hcell | hcell
    · obtain ⟨pieces, hp, hc⟩ := hletter cell hcell
      exact ⟨pieces, hp, by simp [hc]⟩
    · obtain ⟨pieces, hp, hc⟩ := htriple cell hcell
      exact ⟨pieces, hp, by simp [hc]⟩
  rcases hword with ⟨preWord, hpref, tail, htail, rfl⟩
  obtain ⟨prefixPieces, hprefixPieces, hprefixCount⟩ := hprefix preWord hpref
  obtain ⟨tailCells, htailCells⟩ :=
    (mem_star_iff_factorizes
      (Language.letter label ∪ Language.concat
        (Language.power
          (Language.concat L1 (Language.star (Language.letter label))) 2) L1)
      tail).mp htail
  have refineTail : ∀ cells : List (Word alpha),
      (∀ cell ∈ cells,
        cell ∈ Language.letter label ∪ Language.concat
          (Language.power
            (Language.concat L1 (Language.star (Language.letter label))) 2) L1) →
      ∃ pieces : List (Word alpha),
        Factorizes code pieces cells.flatten ∧ otherCount label pieces % 3 = 0 := by
    intro cells
    induction cells with
    | nil =>
        intro _
        exact ⟨[], factorizes_nil code, by simp [otherCount]⟩
    | cons cell cells ih =>
        intro hall
        obtain ⟨cellPieces, hcellPieces, hcellCount⟩ :=
          htailCell cell (hall cell (by simp))
        obtain ⟨restPieces, hrestPieces, hrestCount⟩ := ih (by
          intro other hmem
          exact hall other (by simp [hmem]))
        refine ⟨cellPieces ++ restPieces,
          factorizes_append hcellPieces hrestPieces, ?_⟩
        rw [otherCount_append]
        omega
  obtain ⟨tailPieces, htailPieces, htailCount⟩ :=
    refineTail tailCells htailCells.1
  refine ⟨prefixPieces ++ tailPieces,
    factorizes_append hprefixPieces ?_, ?_⟩
  · simpa [htailCells.2] using htailPieces
  · rw [otherCount_append, hprefixCount]
    omega

/-! The same forward calculation with an arbitrary `L1` classifier. -/

noncomputable def EncodesPartitionExact (code counted language : Language alpha)
    (amount : Nat) : Prop :=
  ∀ word ∈ language, ∃ pieces : List (Word alpha),
    Factorizes code pieces word ∧ countIn counted pieces = amount

omit [DecidableEq alpha] in
theorem EncodesPartitionExact.concat {code counted : Language alpha}
    {left right : Language alpha} {leftAmount rightAmount : Nat}
    (hleft : EncodesPartitionExact code counted left leftAmount)
    (hright : EncodesPartitionExact code counted right rightAmount) :
    EncodesPartitionExact code counted (Language.concat left right)
      (leftAmount + rightAmount) := by
  intro word hword
  rcases hword with ⟨u, hu, v, hv, rfl⟩
  obtain ⟨up, hup, huc⟩ := hleft u hu
  obtain ⟨vp, hvp, hvc⟩ := hright v hv
  exact ⟨up ++ vp, factorizes_append hup hvp, by
    rw [countIn_append, huc, hvc]⟩

omit [DecidableEq alpha] in
theorem EncodesPartitionExact.power {code counted language : Language alpha}
    {amount : Nat}
    (hlanguage : EncodesPartitionExact code counted language amount) (n : Nat) :
    EncodesPartitionExact code counted (Language.power language n) (amount * n) := by
  induction n with
  | zero =>
      intro word hword
      have : word = [] := by simpa [Language.power, Language.epsilon] using hword
      subst word
      exact ⟨[], factorizes_nil code, by simp [countIn]⟩
  | succ n ih =>
      rw [Language.power_succ_left]
      simpa [Nat.mul_succ, Nat.add_comm] using hlanguage.concat ih

omit [DecidableEq alpha] in
theorem EncodesPartitionExact.star_zero {code counted language : Language alpha}
    (hlanguage : EncodesPartitionExact code counted language 0) :
    EncodesPartitionExact code counted (Language.star language) 0 := by
  intro word hword
  rcases hword with ⟨n, hn⟩
  simpa using hlanguage.power n word hn

omit [DecidableEq alpha] in
theorem encodesPartition_left_zero (L0 L1 : Language alpha)
    (hdisjoint : Disjoint L0 L1) :
    EncodesPartitionExact (L0 ∪ L1) L1 L0 0 := by
  classical
  intro word hword
  refine ⟨[word], ?_, ?_⟩
  · constructor
    · intro piece hpiece
      have : piece = word := by simpa using hpiece
      subst piece
      exact Or.inl hword
    · simp
  · simp [countIn, Set.disjoint_left.1 hdisjoint hword]

omit [DecidableEq alpha] in
theorem encodesPartition_right_one (L0 L1 : Language alpha) :
    EncodesPartitionExact (L0 ∪ L1) L1 L1 1 := by
  classical
  intro word hword
  refine ⟨[word], ?_, ?_⟩
  · constructor
    · intro piece hpiece
      have : piece = word := by simpa using hpiece
      subst piece
      exact Or.inr hword
    · simp
  · simp [countIn, hword]

omit [DecidableEq alpha] in
theorem mem_countSide_three_partition_imp (L0 L1 : Language alpha)
    (hdisjoint : Disjoint L0 L1) (residue : Nat) (word : Word alpha)
    (hword : word ∈ Language.concat
      (Language.power (Language.concat (Language.star L0) L1) residue)
      (Language.star
        (L0 ∪ Language.concat
          (Language.power (Language.concat L1 (Language.star L0)) 2) L1))) :
    ∃ pieces : List (Word alpha),
      Factorizes (L0 ∪ L1) pieces word ∧
        countIn L1 pieces % 3 = residue % 3 := by
  have hleft : EncodesPartitionExact (L0 ∪ L1) L1 L0 0 :=
    encodesPartition_left_zero L0 L1 hdisjoint
  have hright : EncodesPartitionExact (L0 ∪ L1) L1 L1 1 :=
    encodesPartition_right_one L0 L1
  have hleftStar : EncodesPartitionExact (L0 ∪ L1) L1
      (Language.star L0) 0 := hleft.star_zero
  have hprefix : EncodesPartitionExact (L0 ∪ L1) L1
      (Language.power (Language.concat (Language.star L0) L1) residue)
      residue := by
    simpa using (hleftStar.concat hright).power residue
  have htriple : EncodesPartitionExact (L0 ∪ L1) L1
      (Language.concat
        (Language.power (Language.concat L1 (Language.star L0)) 2) L1) 3 := by
    have hpair := (hright.concat hleftStar).power 2
    simpa using hpair.concat hright
  rcases hword with ⟨preWord, hpref, tail, htail, rfl⟩
  obtain ⟨prefixPieces, hprefixPieces, hprefixCount⟩ := hprefix preWord hpref
  obtain ⟨tailCells, htailCells⟩ :=
    (mem_star_iff_factorizes
      (L0 ∪ Language.concat
        (Language.power (Language.concat L1 (Language.star L0)) 2) L1)
      tail).mp htail
  have refineTail : ∀ cells : List (Word alpha),
      (∀ cell ∈ cells, cell ∈ L0 ∪ Language.concat
        (Language.power (Language.concat L1 (Language.star L0)) 2) L1) →
      ∃ pieces : List (Word alpha),
        Factorizes (L0 ∪ L1) pieces cells.flatten ∧ countIn L1 pieces % 3 = 0 := by
    intro cells
    induction cells with
    | nil =>
        intro _
        exact ⟨[], factorizes_nil (L0 ∪ L1), by simp [countIn]⟩
    | cons cell cells ih =>
        intro hall
        have hcell := hall cell (by simp)
        have hcellEncoded : ∃ pieces : List (Word alpha),
            Factorizes (L0 ∪ L1) pieces cell ∧ countIn L1 pieces % 3 = 0 := by
          rcases hcell with hcell | hcell
          · obtain ⟨pieces, hp, hc⟩ := hleft cell hcell
            exact ⟨pieces, hp, by simp [hc]⟩
          · obtain ⟨pieces, hp, hc⟩ := htriple cell hcell
            exact ⟨pieces, hp, by simp [hc]⟩
        obtain ⟨cellPieces, hcellPieces, hcellCount⟩ := hcellEncoded
        obtain ⟨restPieces, hrestPieces, hrestCount⟩ := ih (by
          intro other hmem
          exact hall other (by simp [hmem]))
        refine ⟨cellPieces ++ restPieces,
          factorizes_append hcellPieces hrestPieces, ?_⟩
        rw [countIn_append]
        omega
  obtain ⟨tailPieces, htailPieces, htailCount⟩ :=
    refineTail tailCells htailCells.1
  refine ⟨prefixPieces ++ tailPieces,
    factorizes_append hprefixPieces ?_, ?_⟩
  · simpa [htailCells.2] using htailPieces
  · rw [countIn_append, hprefixCount]
    omega

omit [DecidableEq alpha] in
theorem countIn_partition (L0 L1 : Language alpha)
    (hdisjoint : Disjoint L0 L1) (pieces : List (Word alpha))
    (hpieces : ∀ piece ∈ pieces, piece ∈ L0 ∪ L1) :
    countIn L0 pieces + countIn L1 pieces = pieces.length := by
  classical
  induction pieces with
  | nil => simp [countIn]
  | cons piece pieces ih =>
      have hhead := hpieces piece (by simp)
      have htail : ∀ other ∈ pieces, other ∈ L0 ∪ L1 := by
        intro other hother
        exact hpieces other (by simp [hother])
      have ih' := ih htail
      rcases hhead with hL0 | hL1
      · have hnL1 : piece ∉ L1 := by
          intro h
          exact Set.disjoint_left.1 hdisjoint hL0 h
        change countIn L0 ([piece] ++ pieces) +
          countIn L1 ([piece] ++ pieces) = pieces.length + 1
        rw [countIn_append, countIn_append]
        have hs0 : countIn L0 [piece] = 1 := by simp [countIn, hL0]
        have hs1 : countIn L1 [piece] = 0 := by simp [countIn, hnL1]
        rw [hs0, hs1]
        omega
      · have hnL0 : piece ∉ L0 := by
          intro h
          exact Set.disjoint_left.1 hdisjoint h hL1
        change countIn L0 ([piece] ++ pieces) +
          countIn L1 ([piece] ++ pieces) = pieces.length + 1
        rw [countIn_append, countIn_append]
        have hs0 : countIn L0 [piece] = 0 := by simp [countIn, hnL0]
        have hs1 : countIn L1 [piece] = 1 := by simp [countIn, hL1]
        rw [hs0, hs1]
        omega

theorem count_add_otherCount (label : alpha) (pieces : List (Word alpha)) :
    pieces.count [label] + otherCount label pieces = pieces.length := by
  have h := List.length_eq_countP_add_countP
    (fun piece : Word alpha => piece == [label]) (l := pieces)
  rw [h]
  simp [List.count, otherCount]

/-- Exact semantics of `TransferCore.formula` at modulus three, separated
from the one consumer-specific construction needed in the reverse direction
of the count half. -/
theorem mem_formula_three_iff (L0 L1 : Language alpha) (label : alpha)
    (hL0 : L0 = Language.letter label)
    (hdisjoint : ∀ word ∈ L1, word ≠ [label])
    (hUnique : ∀ left right : List (Word alpha),
      Factorizes (L0 ∪ L1) left left.flatten →
      Factorizes (L0 ∪ L1) right right.flatten →
      left.flatten = right.flatten → left = right)
    (hCountBack : ∀ (residue : Nat), residue < 3 →
      ∀ pieces : List (Word alpha),
        Factorizes (L0 ∪ L1) pieces pieces.flatten →
        otherCount label pieces % 3 = residue →
        pieces.flatten ∈ Language.concat
          (Language.power (Language.concat (Language.star L0) L1) residue)
          (Language.star
            (L0 ∪ Language.concat
              (Language.power (Language.concat L1 (Language.star L0)) 2) L1)))
    (word : Word alpha) :
    word ∈ TransferCore.formula L0 L1 3 ↔
      ∃ pieces : List (Word alpha),
        Factorizes (L0 ∪ L1) pieces word ∧ pieces.count [label] % 3 = 0 := by
  constructor
  · intro hword
    simp only [TransferCore.formula, Set.mem_iUnion] at hword
    obtain ⟨residue, hcell⟩ := hword
    have hboth : word ∈ Language.concat
          (Language.star (Language.power (L0 ∪ L1) 3))
          (Language.power (L0 ∪ L1) residue.1) ∧
        word ∈ Language.concat
          (Language.power (Language.concat (Language.star L0) L1) residue.1)
          (Language.star
            (L0 ∪ Language.concat
              (Language.power (Language.concat L1 (Language.star L0)) 2) L1)) := by
      simpa [TransferCore.cell] using hcell
    obtain ⟨lengthPieces, hlengthPieces, hlengthMod⟩ :=
      (mem_lengthSide_three_iff (L0 ∪ L1) residue.1 residue.isLt word).mp hboth.1
    obtain ⟨countPieces, hcountPieces, hcountMod⟩ :=
      mem_countSide_three_imp L0 L1 label hL0 hdisjoint residue.1 word hboth.2
    have hpEq : lengthPieces = countPieces :=
      hUnique lengthPieces countPieces
        ⟨hlengthPieces.1, rfl⟩ ⟨hcountPieces.1, rfl⟩
        (hlengthPieces.2.trans hcountPieces.2.symm)
    subst countPieces
    refine ⟨lengthPieces, hlengthPieces, ?_⟩
    have hpartition := count_add_otherCount label lengthPieces
    omega
  · rintro ⟨pieces, hpieces, hlabelMod⟩
    let residue : Fin 3 := ⟨otherCount label pieces % 3, Nat.mod_lt _ (by decide)⟩
    have hlengthMod : pieces.length % 3 = residue.1 := by
      have hpartition := count_add_otherCount label pieces
      dsimp [residue]
      omega
    have hlength : word ∈ Language.concat
        (Language.star (Language.power (L0 ∪ L1) 3))
        (Language.power (L0 ∪ L1) residue.1) :=
      (mem_lengthSide_three_iff (L0 ∪ L1) residue.1 residue.isLt word).mpr
        ⟨pieces, hpieces, hlengthMod⟩
    have hcount : word ∈ Language.concat
        (Language.power (Language.concat (Language.star L0) L1) residue.1)
        (Language.star
          (L0 ∪ Language.concat
            (Language.power (Language.concat L1 (Language.star L0)) 2) L1)) := by
      have := hCountBack residue.1 residue.isLt pieces ⟨hpieces.1, rfl⟩ (by rfl)
      simpa [hpieces.2] using this
    simp only [TransferCore.formula, Set.mem_iUnion]
    refine ⟨residue, ?_⟩
    simpa [TransferCore.cell] using And.intro hlength hcount

end CountSide

/-! ### Exact token-list normalization at an arbitrary positive modulus -/

namespace TokenMod

/-- Token `true` denotes a counted codeword; `false` denotes an uncounted one. -/
def ZeroWord (word : List Bool) : Prop := word.count true = 0

def PrefixPiece (word : List Bool) : Prop :=
  ∃ zeros, ZeroWord zeros ∧ word = zeros ++ [true]

/-- A tail piece is either one uncounted token or a block containing exactly
`modulus` prefix pieces.  The latter representation is deliberately list-based:
it is the normalization consumed next by the language-level transfer proof. -/
def TailPiece (modulus : Nat) (word : List Bool) : Prop :=
  word = [false] ∨
    ∃ block : List (List Bool),
      block.length = modulus ∧
      (∀ piece ∈ block, PrefixPiece piece) ∧
      block.flatten = word

def CountSide (modulus residue : Nat) (word : List Bool) : Prop :=
  ∃ leading tail : List (List Bool),
    leading.length = residue ∧
    (∀ piece ∈ leading, PrefixPiece piece) ∧
    (∀ piece ∈ tail, TailPiece modulus piece) ∧
    leading.flatten ++ tail.flatten = word

theorem count_prefixPiece {word : List Bool} (h : PrefixPiece word) :
    word.count true = 1 := by
  rcases h with ⟨zeros, hzeros, rfl⟩
  simp [ZeroWord] at hzeros
  simp [hzeros]

theorem count_flatten_prefixPieces (pieces : List (List Bool))
    (hpieces : ∀ piece ∈ pieces, PrefixPiece piece) :
    pieces.flatten.count true = pieces.length := by
  induction pieces with
  | nil => simp
  | cons piece pieces ih =>
      have hp := count_prefixPiece (hpieces piece (by simp))
      have hps : ∀ p ∈ pieces, PrefixPiece p := by
        intro p hpMem
        exact hpieces p (by simp [hpMem])
      simp [hp, ih hps, Nat.add_comm]

theorem count_tailPiece {modulus : Nat} {word : List Bool}
    (h : TailPiece modulus word) : word.count true % modulus = 0 := by
  rcases h with rfl | ⟨block, hlength, hblock, hflat⟩
  · simp
  · rw [← hflat, count_flatten_prefixPieces block hblock, hlength]
    exact Nat.mod_self modulus

theorem count_flatten_tailPieces (modulus : Nat) (pieces : List (List Bool))
    (hpieces : ∀ piece ∈ pieces, TailPiece modulus piece) :
    pieces.flatten.count true % modulus = 0 := by
  induction pieces with
  | nil => simp
  | cons piece pieces ih =>
      have hp := count_tailPiece (hpieces piece (by simp))
      have hps : ∀ p ∈ pieces, TailPiece modulus p := by
        intro p hpMem
        exact hpieces p (by simp [hpMem])
      rw [List.flatten_cons, List.count_append, Nat.add_mod]
      simp [hp, ih hps]

private theorem exists_falsePieces : ∀ word : List Bool,
    word.count true = 0 →
      ∃ pieces : List (List Bool),
        (∀ piece ∈ pieces, piece = [false]) ∧ pieces.flatten = word := by
  intro word hcount
  induction word with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons head rest ih =>
      cases head with
      | false =>
          have hrest : rest.count true = 0 := by simpa using hcount
          obtain ⟨pieces, hpieces, hflat⟩ := ih hrest
          refine ⟨[false] :: pieces, ?_, by simp [hflat]⟩
          intro piece hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · rfl
          · exact hpieces piece hp
      | true => simp at hcount

private theorem exists_prefixPieces_split : ∀ k : Nat, ∀ word : List Bool,
    k ≤ word.count true →
      ∃ pieces : List (List Bool), ∃ rest : List Bool,
        pieces.length = k ∧
        (∀ piece ∈ pieces, PrefixPiece piece) ∧
        pieces.flatten ++ rest = word ∧
        word.count true = k + rest.count true := by
  intro k
  induction k with
  | zero =>
      intro word _
      exact ⟨[], word, rfl, by simp, by simp, by simp⟩
  | succ k ih =>
      intro word hk
      have hpositive : 0 < word.count true := by omega
      obtain ⟨zeros, rest, hsplit, hzeros⟩ :=
        Counting.exists_first_occ true word (List.count_pos_iff.mp hpositive)
      have hcount : word.count true = 1 + rest.count true := by
        rw [hsplit, List.count_append]
        simp [hzeros]
      have hkrest : k ≤ rest.count true := by omega
      obtain ⟨pieces, tail, hlength, hpieces, hflat, htailCount⟩ :=
        ih rest hkrest
      refine ⟨(zeros ++ [true]) :: pieces, tail, ?_, ?_, ?_, ?_⟩
      · simp [hlength]
      · intro piece hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨zeros, hzeros, rfl⟩
        · exact hpieces piece hp
      · rw [List.flatten_cons]
        calc
          zeros ++ [true] ++ pieces.flatten ++ tail =
              zeros ++ [true] ++ (pieces.flatten ++ tail) := by simp [List.append_assoc]
          _ = zeros ++ [true] ++ rest := by rw [hflat]
          _ = word := hsplit.symm
      · omega

private theorem exists_tailPieces_of_count (modulus : Nat) (hmodulus : 0 < modulus) :
    ∀ n : Nat, ∀ word : List Bool, word.count true = n → n % modulus = 0 →
      ∃ pieces : List (List Bool),
        (∀ piece ∈ pieces, TailPiece modulus piece) ∧
        pieces.flatten = word := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih word hcount hmod
  by_cases hn : n = 0
  · have hwordZero : word.count true = 0 := by omega
    obtain ⟨pieces, hpieces, hflat⟩ := exists_falsePieces word hwordZero
    exact ⟨pieces, (fun piece hp => Or.inl (hpieces piece hp)), hflat⟩
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hmodLe : modulus ≤ n := by
      exact Nat.le_of_dvd hnpos (Nat.dvd_iff_mod_eq_zero.mpr hmod)
    have hwordLe : modulus ≤ word.count true := by simpa [hcount] using hmodLe
    obtain ⟨block, rest, hlength, hblock, hflat, hrestCount⟩ :=
      exists_prefixPieces_split modulus word hwordLe
    have hrestLt : rest.count true < n := by omega
    have hncount : n = modulus + rest.count true := by omega
    have hrestMod : rest.count true % modulus = 0 := by
      rw [hncount, Nat.add_mod] at hmod
      simpa using hmod
    obtain ⟨pieces, hpieces, hpiecesFlat⟩ :=
      ih (rest.count true) hrestLt rest rfl hrestMod
    refine ⟨block.flatten :: pieces, ?_, ?_⟩
    · intro piece hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact Or.inr ⟨block, hlength, hblock, rfl⟩
      · exact hpieces piece hp
    · rw [List.flatten_cons, hpiecesFlat]
      exact hflat

theorem exists_tailPieces (modulus : Nat) (hmodulus : 0 < modulus)
    (word : List Bool) (hmod : word.count true % modulus = 0) :
    ∃ pieces : List (List Bool),
      (∀ piece ∈ pieces, TailPiece modulus piece) ∧ pieces.flatten = word :=
  exists_tailPieces_of_count modulus hmodulus (word.count true) word rfl hmod

theorem exists_countSide_factorization (modulus : Nat) (hmodulus : 0 < modulus)
    (residue : Nat) (_hresidue : residue < modulus) (word : List Bool)
    (hmod : word.count true % modulus = residue) :
    CountSide modulus residue word := by
  have hresidueLe : residue ≤ word.count true := by
    rw [← hmod]
    exact Nat.mod_le _ _
  obtain ⟨leading, rest, hlength, hleading, hflat, hrestCount⟩ :=
    exists_prefixPieces_split residue word hresidueLe
  have hrestMod : rest.count true % modulus = 0 := by
    have hdivision := Nat.mod_add_div (word.count true) modulus
    rw [hmod] at hdivision
    have hrestEq : rest.count true = modulus * (word.count true / modulus) := by
      omega
    rw [hrestEq]
    simp
  obtain ⟨tail, htail, htailFlat⟩ :=
    exists_tailPieces modulus hmodulus rest hrestMod
  refine ⟨leading, tail, hlength, hleading, htail, ?_⟩
  rw [htailFlat]
  exact hflat

/-- Exact normalization of the count side for every positive modulus. -/
theorem countSide_iff (modulus : Nat) (hmodulus : 0 < modulus)
    (residue : Nat) (hresidue : residue < modulus) (word : List Bool) :
    CountSide modulus residue word ↔ word.count true % modulus = residue := by
  constructor
  · rintro ⟨leading, tail, hlength, hleading, htail, hflat⟩
    have hLeadingCount := count_flatten_prefixPieces leading hleading
    have hTailCount := count_flatten_tailPieces modulus tail htail
    rw [← hflat, List.count_append, hLeadingCount, hlength, Nat.add_mod]
    simp [hTailCount, Nat.mod_eq_of_lt hresidue]
  · exact exists_countSide_factorization modulus hmodulus residue hresidue word

end TokenMod

/-! ### Exact token-list normalization of the modulus-three count side -/

namespace Token3

/-- Token `true` denotes an `L1` codeword; `false` denotes an `L0` codeword. -/
def ZeroWord (word : List Bool) : Prop := word.count true = 0

def PrefixPiece (word : List Bool) : Prop :=
  ∃ zeros, ZeroWord zeros ∧ word = zeros ++ [true]

def TailPiece (word : List Bool) : Prop :=
  word = [false] ∨
    ∃ zeros₁ zeros₂, ZeroWord zeros₁ ∧ ZeroWord zeros₂ ∧
      word = true :: zeros₁ ++ true :: zeros₂ ++ [true]

/-- List-level semantics of
`(L0* L1)^residue (L0 ∪ (L1 L0*)^2 L1)*`. -/
def CountSide3 (residue : Nat) (word : List Bool) : Prop :=
  ∃ leading tail : List (List Bool),
    leading.length = residue ∧
    (∀ piece ∈ leading, PrefixPiece piece) ∧
    (∀ piece ∈ tail, TailPiece piece) ∧
    leading.flatten ++ tail.flatten = word

theorem count_prefixPiece {word : List Bool} (h : PrefixPiece word) :
    word.count true = 1 := by
  rcases h with ⟨zeros, hzeros, rfl⟩
  simp [ZeroWord] at hzeros
  simp [hzeros]

theorem count_flatten_prefixPieces (pieces : List (List Bool))
    (hpieces : ∀ piece ∈ pieces, PrefixPiece piece) :
    pieces.flatten.count true = pieces.length := by
  induction pieces with
  | nil => simp
  | cons piece pieces ih =>
      have hp := count_prefixPiece (hpieces piece (by simp))
      have hps : ∀ p ∈ pieces, PrefixPiece p := by
        intro p hpMem
        exact hpieces p (by simp [hpMem])
      simp [hp, ih hps, Nat.add_comm]

theorem count_tailPiece {word : List Bool} (h : TailPiece word) :
    word.count true % 3 = 0 := by
  rcases h with rfl | ⟨zeros₁, zeros₂, hz₁, hz₂, rfl⟩
  · decide
  · simp [ZeroWord] at hz₁ hz₂
    simp [hz₁, hz₂]

theorem count_flatten_tailPieces (pieces : List (List Bool))
    (hpieces : ∀ piece ∈ pieces, TailPiece piece) :
    pieces.flatten.count true % 3 = 0 := by
  induction pieces with
  | nil => simp
  | cons piece pieces ih =>
      have hp := count_tailPiece (hpieces piece (by simp))
      have hps : ∀ p ∈ pieces, TailPiece p := by
        intro p hpMem
        exact hpieces p (by simp [hpMem])
      rw [List.flatten_cons, List.count_append]
      have := ih hps
      omega

private theorem exists_tailPieces_of_length :
    ∀ n : Nat, ∀ word : List Bool, word.length = n → word.count true % 3 = 0 →
      ∃ pieces : List (List Bool),
        (∀ piece ∈ pieces, TailPiece piece) ∧ pieces.flatten = word := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih word hlength hmod
  cases word with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons head rest =>
      cases head with
      | false =>
          have hrestMod : rest.count true % 3 = 0 := by simpa using hmod
          have hrestLength : rest.length < n := by rw [← hlength]; simp
          obtain ⟨pieces, hpieces, hflat⟩ :=
            ih rest.length hrestLength rest rfl hrestMod
          refine ⟨[false] :: pieces, ?_, by simp [hflat]⟩
          intro piece hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact Or.inl rfl
          · exact hpieces piece hp
      | true =>
          have hrestMod : rest.count true % 3 = 2 := by
            have hmod' : (rest.count true + 1) % 3 = 0 := by simpa using hmod
            omega
          have hrestPos : 0 < rest.count true := by omega
          obtain ⟨zeros₁, rest₂, hsplit₁, hz₁⟩ :=
            Counting.exists_first_occ true rest (List.count_pos_iff.mp hrestPos)
          have hrest₂Mod : rest₂.count true % 3 = 1 := by
            have hcount : rest.count true = 1 + rest₂.count true := by
              rw [hsplit₁, List.count_append]
              simp [hz₁]
            omega
          have hrest₂Pos : 0 < rest₂.count true := by omega
          obtain ⟨zeros₂, tail, hsplit₂, hz₂⟩ :=
            Counting.exists_first_occ true rest₂ (List.count_pos_iff.mp hrest₂Pos)
          have htailMod : tail.count true % 3 = 0 := by
            have hcount : rest₂.count true = 1 + tail.count true := by
              rw [hsplit₂, List.count_append]
              simp [hz₂]
            omega
          have htailLength : tail.length < n := by
            rw [← hlength, hsplit₁, hsplit₂]
            simp
            omega
          obtain ⟨pieces, hpieces, hflat⟩ :=
            ih tail.length htailLength tail rfl htailMod
          refine ⟨(true :: zeros₁ ++ true :: zeros₂ ++ [true]) :: pieces, ?_, ?_⟩
          · intro piece hp
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact Or.inr ⟨zeros₁, zeros₂, hz₁, hz₂, rfl⟩
            · exact hpieces piece hp
          · rw [List.flatten_cons, hflat, hsplit₁, hsplit₂]
            simp

theorem exists_tailPieces (word : List Bool) (hmod : word.count true % 3 = 0) :
    ∃ pieces : List (List Bool),
      (∀ piece ∈ pieces, TailPiece piece) ∧ pieces.flatten = word :=
  exists_tailPieces_of_length word.length word rfl hmod

theorem exists_countSide3_factorization (residue : Nat) (hresidue : residue < 3) :
    ∀ word : List Bool, word.count true % 3 = residue → CountSide3 residue word := by
  induction residue with
  | zero =>
      intro word hmod
      obtain ⟨tail, htail, hflat⟩ := exists_tailPieces word hmod
      exact ⟨[], tail, rfl, by simp, htail, by simpa using hflat⟩
  | succ residue ih =>
      intro word hmod
      have hpositive : 0 < word.count true := by omega
      obtain ⟨zeros, rest, hsplit, hzeros⟩ :=
        Counting.exists_first_occ true word (List.count_pos_iff.mp hpositive)
      have hrestMod : rest.count true % 3 = residue := by
        have hcount : word.count true = 1 + rest.count true := by
          rw [hsplit, List.count_append]
          simp [hzeros]
        omega
      obtain ⟨leading, tail, hleadingLen, hleading, htail, hflat⟩ :=
        ih (by omega) rest hrestMod
      refine ⟨(zeros ++ [true]) :: leading, tail, ?_, ?_, htail, ?_⟩
      · simp [hleadingLen]
      · intro piece hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨zeros, hzeros, rfl⟩
        · exact hleading piece hp
      · simp only [List.flatten_cons, List.append_assoc]
        rw [hflat]
        simpa [List.append_assoc] using hsplit.symm

/-- Exact normalization of the count side at modulus three. -/
theorem countSide3_iff (residue : Nat) (hresidue : residue < 3)
    (word : List Bool) : CountSide3 residue word ↔ word.count true % 3 = residue := by
  constructor
  · rintro ⟨leading, tail, hlength, hleading, htail, hflat⟩
    have hLeadingCount := count_flatten_prefixPieces leading hleading
    have hTailCount := count_flatten_tailPieces tail htail
    rw [← hflat, List.count_append]
    omega
  · exact exists_countSide3_factorization residue hresidue word

end Token3

/-! ### Lifting token groupings back to codeword factorizations -/

namespace TokenLift

variable {beta : Type u}
variable {gamma delta : Type*}

def Matches (L0 L1 : Language beta) (token : Bool) (piece : Word beta) : Prop :=
  if token then piece ∈ L1 else piece ∈ L0

theorem forall₂_append_split {R : gamma → delta → Prop}
    {left right : List gamma}
    {values : List delta} (h : List.Forall₂ R (left ++ right) values) :
    ∃ leftValues rightValues,
      values = leftValues ++ rightValues ∧
      List.Forall₂ R left leftValues ∧ List.Forall₂ R right rightValues := by
  let leftValues := values.take left.length
  let rightValues := values.drop left.length
  have hleft := List.forall₂_take left.length h
  have hright := List.forall₂_drop left.length h
  refine ⟨leftValues, rightValues, ?_, ?_, ?_⟩
  · exact (List.take_append_drop left.length values).symm
  · simpa [leftValues] using hleft
  · simpa [rightValues] using hright

theorem forall₂_flatten_split {R : gamma → delta → Prop}
    (groups : List (List gamma)) (values : List delta)
    (h : List.Forall₂ R groups.flatten values) :
    ∃ valueGroups : List (List delta),
      List.Forall₂ (List.Forall₂ R) groups valueGroups ∧
        valueGroups.flatten = values := by
  induction groups generalizing values with
  | nil =>
      cases h
      exact ⟨[], List.Forall₂.nil, rfl⟩
  | cons group groups ih =>
      simp only [List.flatten_cons] at h
      obtain ⟨groupValues, restValues, rfl, hgroup, hrest⟩ :=
        forall₂_append_split h
      obtain ⟨restGroups, hrestGroups, hflat⟩ := ih restValues hrest
      exact ⟨groupValues :: restGroups,
        List.Forall₂.cons hgroup hrestGroups, by simp [hflat]⟩

theorem matches_zero_all (L0 L1 : Language beta)
    {tokens : List Bool} {pieces : List (Word beta)}
    (hzero : Token3.ZeroWord tokens)
    (hmatch : List.Forall₂ (Matches L0 L1) tokens pieces) :
    ∀ piece ∈ pieces, piece ∈ L0 := by
  intro piece hpiece
  induction hmatch with
  | nil => simp at hpiece
  | @cons token piece' tokens pieces hhead htail ih =>
      simp only [List.mem_cons] at hpiece
      have htoken : token = false := by
        cases token with
        | false => rfl
        | true => simp [Token3.ZeroWord] at hzero
      subst token
      rcases hpiece with rfl | hpiece
      · simpa [Matches] using hhead
      · apply ih
        · simpa [Token3.ZeroWord] using hzero
        · exact hpiece

theorem matches_zero_star (L0 L1 : Language beta)
    {tokens : List Bool} {pieces : List (Word beta)}
    (hzero : Token3.ZeroWord tokens)
    (hmatch : List.Forall₂ (Matches L0 L1) tokens pieces) :
    pieces.flatten ∈ Language.star L0 :=
  (mem_star_iff_factorizes L0 pieces.flatten).mpr
    ⟨pieces, ⟨matches_zero_all L0 L1 hzero hmatch, rfl⟩⟩

theorem matches_single_true (L0 L1 : Language beta)
    {pieces : List (Word beta)}
    (hmatch : List.Forall₂ (Matches L0 L1) [true] pieces) :
    ∃ piece, pieces = [piece] ∧ piece ∈ L1 := by
  cases hmatch with
  | cons hhead htail =>
      cases htail
      exact ⟨_, rfl, by simpa [Matches] using hhead⟩

theorem matches_single_false (L0 L1 : Language beta)
    {pieces : List (Word beta)}
    (hmatch : List.Forall₂ (Matches L0 L1) [false] pieces) :
    ∃ piece, pieces = [piece] ∧ piece ∈ L0 := by
  cases hmatch with
  | cons hhead htail =>
      cases htail
      exact ⟨_, rfl, by simpa [Matches] using hhead⟩

def PrefixGroup (L0 L1 : Language beta) (group : List (Word beta)) : Prop :=
  ∃ zeros last, group = zeros ++ [last] ∧
    (∀ word ∈ zeros, word ∈ L0) ∧ last ∈ L1

def TailGroup (L0 L1 : Language beta) (group : List (Word beta)) : Prop :=
  (∃ zero, zero ∈ L0 ∧ group = [zero]) ∨
    ∃ first zeros₁ second zeros₂ third,
      first ∈ L1 ∧ second ∈ L1 ∧ third ∈ L1 ∧
      (∀ word ∈ zeros₁, word ∈ L0) ∧
      (∀ word ∈ zeros₂, word ∈ L0) ∧
      group = first :: zeros₁ ++ second :: zeros₂ ++ [third]

theorem prefixGroup_of_matches (L0 L1 : Language beta)
    {tokens : List Bool} {pieces : List (Word beta)}
    (htokens : Token3.PrefixPiece tokens)
    (hmatch : List.Forall₂ (Matches L0 L1) tokens pieces) :
    PrefixGroup L0 L1 pieces := by
  rcases htokens with ⟨zeros, hzeros, rfl⟩
  obtain ⟨zeroPieces, lastPieces, hpEq, hzeroMatch, hlastMatch⟩ :=
    forall₂_append_split hmatch
  obtain ⟨last, rfl, hlast⟩ := matches_single_true L0 L1 hlastMatch
  exact ⟨zeroPieces, last, hpEq, matches_zero_all L0 L1 hzeros hzeroMatch, hlast⟩

theorem tailGroup_of_matches (L0 L1 : Language beta)
    {tokens : List Bool} {pieces : List (Word beta)}
    (htokens : Token3.TailPiece tokens)
    (hmatch : List.Forall₂ (Matches L0 L1) tokens pieces) :
    TailGroup L0 L1 pieces := by
  rcases htokens with rfl | ⟨zeros₁, zeros₂, hz₁, hz₂, rfl⟩
  · obtain ⟨zero, rfl, hzero⟩ := matches_single_false L0 L1 hmatch
    exact Or.inl ⟨zero, hzero, rfl⟩
  · change List.Forall₂ (Matches L0 L1)
      (true :: zeros₁ ++ true :: zeros₂ ++ [true]) pieces at hmatch
    have hshape : true :: zeros₁ ++ true :: zeros₂ ++ [true] =
        [true] ++ zeros₁ ++ [true] ++ zeros₂ ++ [true] := by simp
    rw [hshape] at hmatch
    obtain ⟨firstPieces, rest₁, hpEq₁, hfirstMatch, hrest₁⟩ :=
      forall₂_append_split (left := [true])
        (right := zeros₁ ++ [true] ++ zeros₂ ++ [true]) hmatch
    have hrest₁' : List.Forall₂ (Matches L0 L1)
        (zeros₁ ++ ([true] ++ zeros₂ ++ [true])) rest₁ := by
      simpa [List.append_assoc] using hrest₁
    obtain ⟨zeroPieces₁, rest₂, hpEq₂, hzeroMatch₁, hrest₂⟩ :=
      forall₂_append_split (left := zeros₁)
        (right := [true] ++ zeros₂ ++ [true]) hrest₁'
    obtain ⟨secondPieces, rest₃, hpEq₃, hsecondMatch, hrest₃⟩ :=
      forall₂_append_split (left := [true])
        (right := zeros₂ ++ [true]) hrest₂
    obtain ⟨zeroPieces₂, thirdPieces, hpEq₄, hzeroMatch₂, hthirdMatch⟩ :=
      forall₂_append_split (left := zeros₂) (right := [true]) hrest₃
    obtain ⟨first, rfl, hfirst⟩ := matches_single_true L0 L1 hfirstMatch
    obtain ⟨second, rfl, hsecond⟩ := matches_single_true L0 L1 hsecondMatch
    obtain ⟨third, rfl, hthird⟩ := matches_single_true L0 L1 hthirdMatch
    apply Or.inr
    refine ⟨first, zeroPieces₁, second, zeroPieces₂, third,
      hfirst, hsecond, hthird,
      matches_zero_all L0 L1 hz₁ hzeroMatch₁,
      matches_zero_all L0 L1 hz₂ hzeroMatch₂, ?_⟩
    rw [hpEq₁, hpEq₂, hpEq₃, hpEq₄]
    simp [List.append_assoc]

theorem flatten_prefixGroup_mem (L0 L1 : Language beta)
    (group : List (Word beta)) (hgroup : PrefixGroup L0 L1 group) :
    group.flatten ∈ Language.concat (Language.star L0) L1 := by
  rcases hgroup with ⟨zeros, last, rfl, hzeros, hlast⟩
  rw [List.flatten_append]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  exact ⟨zeros.flatten,
    (mem_star_iff_factorizes L0 zeros.flatten).mpr
      ⟨zeros, ⟨hzeros, rfl⟩⟩,
    last, hlast, rfl⟩

private theorem pair_mem (L0 L1 : Language beta) (first : Word beta)
    (zeros : List (Word beta)) (hfirst : first ∈ L1)
    (hzeros : ∀ word ∈ zeros, word ∈ L0) :
    first ++ zeros.flatten ∈ Language.concat L1 (Language.star L0) :=
  ⟨first, hfirst, zeros.flatten,
    (mem_star_iff_factorizes L0 zeros.flatten).mpr
      ⟨zeros, ⟨hzeros, rfl⟩⟩, rfl⟩

theorem flatten_tailGroup_mem (L0 L1 : Language beta)
    (group : List (Word beta)) (hgroup : TailGroup L0 L1 group) :
    group.flatten ∈ L0 ∪ Language.concat
      (Language.power (Language.concat L1 (Language.star L0)) 2) L1 := by
  rcases hgroup with ⟨zero, hzero, rfl⟩ |
      ⟨first, zeros₁, second, zeros₂, third, hfirst, hsecond, hthird,
        hzeros₁, hzeros₂, rfl⟩
  · exact Or.inl (by simpa using hzero)
  · apply Or.inr
    let pair₁ := first ++ zeros₁.flatten
    let pair₂ := second ++ zeros₂.flatten
    have hpair₁ : pair₁ ∈ Language.concat L1 (Language.star L0) :=
      pair_mem L0 L1 first zeros₁ hfirst hzeros₁
    have hpair₂ : pair₂ ∈ Language.concat L1 (Language.star L0) :=
      pair_mem L0 L1 second zeros₂ hsecond hzeros₂
    have hpairs : pair₁ ++ pair₂ ∈
        Language.power (Language.concat L1 (Language.star L0)) 2 :=
      (mem_power_iff_factorizes_length
        (Language.concat L1 (Language.star L0)) 2 (pair₁ ++ pair₂)).mpr
        ⟨[pair₁, pair₂], ⟨by
          intro piece hpiece
          simp only [List.mem_cons] at hpiece
          rcases hpiece with rfl | hpiece
          · exact hpair₁
          · rcases hpiece with rfl | hpiece
            · exact hpair₂
            · simp at hpiece
        , by simp⟩, by simp⟩
    refine ⟨pair₁ ++ pair₂, hpairs, third, hthird, ?_⟩
    simp [pair₁, pair₂, List.flatten_append, List.append_assoc]

theorem mem_countSide3_of_groups (L0 L1 : Language beta) (residue : Nat)
    (leading tail : List (List (Word beta)))
    (hleadingLength : leading.length = residue)
    (hleading : ∀ group ∈ leading, PrefixGroup L0 L1 group)
    (htail : ∀ group ∈ tail, TailGroup L0 L1 group) :
    leading.flatten.flatten ++ tail.flatten.flatten ∈
      Language.concat
        (Language.power (Language.concat (Language.star L0) L1) residue)
        (Language.star
          (L0 ∪ Language.concat
            (Language.power (Language.concat L1 (Language.star L0)) 2) L1)) := by
  have hleadingWords : ∀ word ∈ leading.map List.flatten,
      word ∈ Language.concat (Language.star L0) L1 := by
    intro word hword
    simp only [List.mem_map] at hword
    obtain ⟨group, hgroupMem, rfl⟩ := hword
    exact flatten_prefixGroup_mem L0 L1 group (hleading group hgroupMem)
  have htailWords : ∀ word ∈ tail.map List.flatten,
      word ∈ L0 ∪ Language.concat
        (Language.power (Language.concat L1 (Language.star L0)) 2) L1 := by
    intro word hword
    simp only [List.mem_map] at hword
    obtain ⟨group, hgroupMem, rfl⟩ := hword
    exact flatten_tailGroup_mem L0 L1 group (htail group hgroupMem)
  have hleadingPower :=
    (mem_power_iff_factorizes_length
      (Language.concat (Language.star L0) L1) leading.length
      (leading.map List.flatten).flatten).mpr
      ⟨leading.map List.flatten, ⟨hleadingWords, rfl⟩, by simp⟩
  have htailStar :=
    (mem_star_iff_factorizes
      (L0 ∪ Language.concat
        (Language.power (Language.concat L1 (Language.star L0)) 2) L1)
      (tail.map List.flatten).flatten).mpr
      ⟨tail.map List.flatten, ⟨htailWords, rfl⟩⟩
  have flatten_map_flatten : ∀ groups : List (List (Word beta)),
      (groups.map List.flatten).flatten = groups.flatten.flatten := by
    intro groups
    induction groups with
    | nil => rfl
    | cons group groups ih => simp [ih]
  rw [flatten_map_flatten] at hleadingPower htailStar
  rw [hleadingLength] at hleadingPower
  exact ⟨leading.flatten.flatten, hleadingPower,
    tail.flatten.flatten, htailStar, rfl⟩

theorem all_prefixGroups_of_forall₂ (L0 L1 : Language beta)
    {tokenGroups : List (List Bool)} {pieceGroups : List (List (Word beta))}
    (hrel : List.Forall₂ (List.Forall₂ (Matches L0 L1))
      tokenGroups pieceGroups)
    (htokens : ∀ group ∈ tokenGroups, Token3.PrefixPiece group) :
    ∀ group ∈ pieceGroups, PrefixGroup L0 L1 group := by
  induction hrel with
  | nil => simp
  | @cons tokenGroup pieceGroup tokenGroups pieceGroups hhead htail ih =>
      intro group hgroup
      simp only [List.mem_cons] at hgroup
      rcases hgroup with rfl | hgroup
      · exact prefixGroup_of_matches L0 L1
          (htokens tokenGroup (by simp)) hhead
      · exact ih (by
          intro other hother
          exact htokens other (by simp [hother])) group hgroup

theorem all_tailGroups_of_forall₂ (L0 L1 : Language beta)
    {tokenGroups : List (List Bool)} {pieceGroups : List (List (Word beta))}
    (hrel : List.Forall₂ (List.Forall₂ (Matches L0 L1))
      tokenGroups pieceGroups)
    (htokens : ∀ group ∈ tokenGroups, Token3.TailPiece group) :
    ∀ group ∈ pieceGroups, TailGroup L0 L1 group := by
  induction hrel with
  | nil => simp
  | @cons tokenGroup pieceGroup tokenGroups pieceGroups hhead htail ih =>
      intro group hgroup
      simp only [List.mem_cons] at hgroup
      rcases hgroup with rfl | hgroup
      · exact tailGroup_of_matches L0 L1
          (htokens tokenGroup (by simp)) hhead
      · exact ih (by
          intro other hother
          exact htokens other (by simp [hother])) group hgroup

variable [DecidableEq beta]

def tokensOf (label : beta) (pieces : List (Word beta)) : List Bool :=
  pieces.map fun piece => decide (piece ≠ [label])

theorem matches_tokensOf (L1 : Language beta) (label : beta)
    (pieces : List (Word beta))
    (hpieces : ∀ piece ∈ pieces,
      piece ∈ Language.letter label ∪ L1) :
    List.Forall₂ (Matches (Language.letter label) L1)
      (tokensOf label pieces) pieces := by
  induction pieces with
  | nil => exact List.Forall₂.nil
  | cons piece pieces ih =>
      apply List.Forall₂.cons
      · by_cases hp : piece = [label]
        · subst piece
          simp [Matches]
        · have hcode := hpieces piece (by simp)
          have hL1 : piece ∈ L1 := hcode.resolve_left (by
            intro hletter
            exact hp hletter)
          simp [Matches, hp, hL1]
      · apply ih
        intro other hother
        exact hpieces other (by simp [hother])

/-- Reverse normalization of the modulus-three count half: a codeword
factorization whose number of `L1` pieces has residue `residue` can be grouped
into the exact transfer expression. -/
theorem mem_countSide_three_of_factorization (L1 : Language beta) (label : beta)
    (residue : Nat) (hresidue : residue < 3)
    (pieces : List (Word beta))
    (hpieces : Factorizes (Language.letter label ∪ L1) pieces pieces.flatten)
    (hcount : otherCount label pieces % 3 = residue) :
    pieces.flatten ∈ Language.concat
      (Language.power
        (Language.concat (Language.star (Language.letter label)) L1) residue)
      (Language.star
        (Language.letter label ∪ Language.concat
          (Language.power
            (Language.concat L1 (Language.star (Language.letter label))) 2) L1)) := by
  let tokens := tokensOf label pieces
  have htokenCount : tokens.count true % 3 = residue := by
    simpa [tokens, tokensOf, otherCount, List.count, Function.comp_def] using hcount
  obtain ⟨leading, tail, hleadingLength, hleading, htail, hflat⟩ :=
    (Token3.countSide3_iff residue hresidue tokens).mpr htokenCount
  have hmatch : List.Forall₂ (Matches (Language.letter label) L1)
      tokens pieces := matches_tokensOf L1 label pieces hpieces.1
  have hgroupMatch : List.Forall₂ (Matches (Language.letter label) L1)
      (leading ++ tail).flatten pieces := by
    rw [List.flatten_append, hflat]
    exact hmatch
  obtain ⟨pieceGroups, hpieceGroups, hpieceFlat⟩ :=
    forall₂_flatten_split (leading ++ tail) pieces hgroupMatch
  obtain ⟨leadingPieces, tailPieces, hgroupsEq, hleadingRel, htailRel⟩ :=
    forall₂_append_split (left := leading) (right := tail) hpieceGroups
  have hresult := mem_countSide3_of_groups
    (Language.letter label) L1 residue leadingPieces tailPieces
    (by
      have := hleadingRel.length_eq
      simpa [hleadingLength] using this.symm)
    (all_prefixGroups_of_forall₂ (Language.letter label) L1 hleadingRel hleading)
    (all_tailGroups_of_forall₂ (Language.letter label) L1 htailRel htail)
  have hflatten : leadingPieces.flatten.flatten ++ tailPieces.flatten.flatten =
      pieces.flatten := by
    rw [← List.flatten_append, ← List.flatten_append, ← hgroupsEq, hpieceFlat]
  simpa [hflatten] using hresult

noncomputable def tokensOfPartition (L1 : Language beta)
    (pieces : List (Word beta)) : List Bool := by
  classical
  exact pieces.map fun piece => decide (piece ∈ L1)

omit [DecidableEq beta] in
theorem matches_tokensOfPartition (L0 L1 : Language beta)
    (pieces : List (Word beta))
    (hpieces : ∀ piece ∈ pieces, piece ∈ L0 ∪ L1) :
    List.Forall₂ (Matches L0 L1) (tokensOfPartition L1 pieces) pieces := by
  classical
  induction pieces with
  | nil => exact List.Forall₂.nil
  | cons piece pieces ih =>
      apply List.Forall₂.cons
      · by_cases hp : piece ∈ L1
        · simp [Matches, hp]
        · have hcode := hpieces piece (by simp)
          have hL0 : piece ∈ L0 := hcode.resolve_right hp
          simp [Matches, hp, hL0]
      · apply ih
        intro other hother
        exact hpieces other (by simp [hother])

omit [DecidableEq beta] in
/-- Reverse normalization for an arbitrary disjoint `L0/L1` partition. -/
theorem mem_countSide_three_of_partition (L0 L1 : Language beta)
    (residue : Nat) (hresidue : residue < 3)
    (pieces : List (Word beta))
    (hpieces : Factorizes (L0 ∪ L1) pieces pieces.flatten)
    (hcount : countIn L1 pieces % 3 = residue) :
    pieces.flatten ∈ Language.concat
      (Language.power (Language.concat (Language.star L0) L1) residue)
      (Language.star
        (L0 ∪ Language.concat
          (Language.power (Language.concat L1 (Language.star L0)) 2) L1)) := by
  classical
  let tokens := tokensOfPartition L1 pieces
  have htokenCount : tokens.count true % 3 = residue := by
    simpa [tokens, tokensOfPartition, countIn, List.count, Function.comp_def]
      using hcount
  obtain ⟨leading, tail, hleadingLength, hleading, htail, hflat⟩ :=
    (Token3.countSide3_iff residue hresidue tokens).mpr htokenCount
  have hmatch : List.Forall₂ (Matches L0 L1) tokens pieces :=
    matches_tokensOfPartition L0 L1 pieces hpieces.1
  have hgroupMatch : List.Forall₂ (Matches L0 L1)
      (leading ++ tail).flatten pieces := by
    rw [List.flatten_append, hflat]
    exact hmatch
  obtain ⟨pieceGroups, hpieceGroups, hpieceFlat⟩ :=
    forall₂_flatten_split (leading ++ tail) pieces hgroupMatch
  obtain ⟨leadingPieces, tailPieces, hgroupsEq, hleadingRel, htailRel⟩ :=
    forall₂_append_split (left := leading) (right := tail) hpieceGroups
  have hresult := mem_countSide3_of_groups L0 L1 residue leadingPieces tailPieces
    (by
      have := hleadingRel.length_eq
      simpa [hleadingLength] using this.symm)
    (all_prefixGroups_of_forall₂ L0 L1 hleadingRel hleading)
    (all_tailGroups_of_forall₂ L0 L1 htailRel htail)
  have hflatten : leadingPieces.flatten.flatten ++ tailPieces.flatten.flatten =
      pieces.flatten := by
    rw [← List.flatten_append, ← List.flatten_append, ← hgroupsEq, hpieceFlat]
  simpa [hflatten] using hresult

end TokenLift

/-- Exact modulus-three transfer semantics for any disjoint uniquely
decipherable partition `L0 ∪ L1`.  The counted pieces are those in `L0`.
`countIn` is definitionally a classical `List.countP` membership count. -/
theorem mem_formula_partition_three_iff (L0 L1 : Language alpha)
    (hdisjoint : Disjoint L0 L1)
    (hUnique : ∀ left right : List (Word alpha),
      Factorizes (L0 ∪ L1) left left.flatten →
      Factorizes (L0 ∪ L1) right right.flatten →
      left.flatten = right.flatten → left = right)
    (word : Word alpha) :
    word ∈ TransferCore.formula L0 L1 3 ↔
      ∃ pieces : List (Word alpha),
        Factorizes (L0 ∪ L1) pieces word ∧ countIn L0 pieces % 3 = 0 := by
  classical
  constructor
  · intro hword
    simp only [TransferCore.formula, Set.mem_iUnion] at hword
    obtain ⟨residue, hcell⟩ := hword
    have hboth : word ∈ Language.concat
          (Language.star (Language.power (L0 ∪ L1) 3))
          (Language.power (L0 ∪ L1) residue.1) ∧
        word ∈ Language.concat
          (Language.power (Language.concat (Language.star L0) L1) residue.1)
          (Language.star
            (L0 ∪ Language.concat
              (Language.power (Language.concat L1 (Language.star L0)) 2) L1)) := by
      simpa [TransferCore.cell] using hcell
    obtain ⟨lengthPieces, hlengthPieces, hlengthMod⟩ :=
      (mem_lengthSide_three_iff (L0 ∪ L1) residue.1 residue.isLt word).mp hboth.1
    obtain ⟨countPieces, hcountPieces, hcountMod⟩ :=
      mem_countSide_three_partition_imp L0 L1 hdisjoint
        residue.1 word hboth.2
    have hpEq : lengthPieces = countPieces :=
      hUnique lengthPieces countPieces
        ⟨hlengthPieces.1, rfl⟩ ⟨hcountPieces.1, rfl⟩
        (hlengthPieces.2.trans hcountPieces.2.symm)
    subst countPieces
    refine ⟨lengthPieces, hlengthPieces, ?_⟩
    have hpartition := countIn_partition L0 L1 hdisjoint
      lengthPieces hlengthPieces.1
    omega
  · rintro ⟨pieces, hpieces, hleftMod⟩
    let residue : Fin 3 := ⟨countIn L1 pieces % 3, Nat.mod_lt _ (by decide)⟩
    have hpartition := countIn_partition L0 L1 hdisjoint pieces hpieces.1
    have hlengthMod : pieces.length % 3 = residue.1 := by
      dsimp [residue]
      omega
    have hlength : word ∈ Language.concat
        (Language.star (Language.power (L0 ∪ L1) 3))
        (Language.power (L0 ∪ L1) residue.1) :=
      (mem_lengthSide_three_iff (L0 ∪ L1) residue.1 residue.isLt word).mpr
        ⟨pieces, hpieces, hlengthMod⟩
    have hcount : word ∈ Language.concat
        (Language.power (Language.concat (Language.star L0) L1) residue.1)
        (Language.star
          (L0 ∪ Language.concat
            (Language.power (Language.concat L1 (Language.star L0)) 2) L1)) := by
      have := TokenLift.mem_countSide_three_of_partition
        L0 L1 residue.1 residue.isLt pieces ⟨hpieces.1, rfl⟩ (by rfl)
      simpa [hpieces.2] using this
    simp only [TransferCore.formula, Set.mem_iUnion]
    refine ⟨residue, ?_⟩
    simpa [TransferCore.cell] using And.intro hlength hcount

/-- Complete modulus-three transfer semantics for a distinguished singleton
and a disjoint uniquely decipherable return-block language. -/
theorem mem_formula_letter_three_iff [DecidableEq alpha]
    (L1 : Language alpha) (label : alpha)
    (hdisjoint : ∀ word ∈ L1, word ≠ [label])
    (hUnique : ∀ left right : List (Word alpha),
      Factorizes (Language.letter label ∪ L1) left left.flatten →
      Factorizes (Language.letter label ∪ L1) right right.flatten →
      left.flatten = right.flatten → left = right)
    (word : Word alpha) :
    word ∈ TransferCore.formula (Language.letter label) L1 3 ↔
      ∃ pieces : List (Word alpha),
        Factorizes (Language.letter label ∪ L1) pieces word ∧
          pieces.count [label] % 3 = 0 := by
  have hpartition : Disjoint (Language.letter label) L1 := by
    apply Set.disjoint_left.2
    intro word hletter hL1
    exact hdisjoint word hL1 hletter
  rw [mem_formula_partition_three_iff
    (Language.letter label) L1 hpartition hUnique word]
  apply exists_congr
  intro pieces
  apply and_congr_right
  intro _
  rw [countIn_letter_eq_count]

end TransferSemantics

end GSH
