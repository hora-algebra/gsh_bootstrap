import GSH.Height.TransferSemantics
import Mathlib.Data.Nat.ModEq

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

theorem mem_countSide_modulus_partition_imp (L0 L1 : Language alpha)
    (modulus : Nat) (hmodulus : 0 < modulus)
    (hdisjoint : Disjoint L0 L1) (residue : Nat) (word : Word alpha)
    (hword : word ∈ Language.concat
      (Language.power (Language.concat (Language.star L0) L1) residue)
      (Language.star
        (L0 ∪ Language.concat
          (Language.power (Language.concat L1 (Language.star L0))
            (modulus - 1)) L1))) :
    ∃ pieces : List (Word alpha),
      Factorizes (L0 ∪ L1) pieces word ∧
        countIn L1 pieces % modulus = residue % modulus := by
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
  have hcycle : EncodesPartitionExact (L0 ∪ L1) L1
      (Language.concat
        (Language.power (Language.concat L1 (Language.star L0))
          (modulus - 1)) L1) modulus := by
    have hpairs := (hright.concat hleftStar).power (modulus - 1)
    have hencoded := hpairs.concat hright
    convert hencoded using 1
    all_goals omega
  rcases hword with ⟨preWord, hpref, tail, htail, rfl⟩
  obtain ⟨prefixPieces, hprefixPieces, hprefixCount⟩ := hprefix preWord hpref
  obtain ⟨tailCells, htailCells⟩ :=
    (mem_star_iff_factorizes
      (L0 ∪ Language.concat
        (Language.power (Language.concat L1 (Language.star L0))
          (modulus - 1)) L1) tail).mp htail
  have refineTail : ∀ cells : List (Word alpha),
      (∀ cell ∈ cells, cell ∈ L0 ∪ Language.concat
        (Language.power (Language.concat L1 (Language.star L0))
          (modulus - 1)) L1) →
      ∃ pieces : List (Word alpha),
        Factorizes (L0 ∪ L1) pieces cells.flatten ∧
          countIn L1 pieces % modulus = 0 := by
    intro cells
    induction cells with
    | nil =>
        intro _
        exact ⟨[], factorizes_nil (L0 ∪ L1), by simp [countIn]⟩
    | cons cell cells ih =>
        intro hall
        have hcell := hall cell (by simp)
        have hcellEncoded : ∃ pieces : List (Word alpha),
            Factorizes (L0 ∪ L1) pieces cell ∧
              countIn L1 pieces % modulus = 0 := by
          rcases hcell with hcell | hcell
          · obtain ⟨pieces, hp, hc⟩ := hleft cell hcell
            exact ⟨pieces, hp, by simp [hc]⟩
          · obtain ⟨pieces, hp, hc⟩ := hcycle cell hcell
            exact ⟨pieces, hp, by simp [hc]⟩
        obtain ⟨cellPieces, hcellPieces, hcellCount⟩ := hcellEncoded
        obtain ⟨restPieces, hrestPieces, hrestCount⟩ := ih (by
          intro other hmem
          exact hall other (by simp [hmem]))
        refine ⟨cellPieces ++ restPieces,
          factorizes_append hcellPieces hrestPieces, ?_⟩
        rw [countIn_append, Nat.add_mod]
        simp [hcellCount, hrestCount]
  obtain ⟨tailPieces, htailPieces, htailCount⟩ :=
    refineTail tailCells htailCells.1
  refine ⟨prefixPieces ++ tailPieces,
    factorizes_append hprefixPieces ?_, ?_⟩
  · simpa [htailCells.2] using htailPieces
  · rw [countIn_append, hprefixCount, Nat.add_mod]
    simp [htailCount]

namespace TokenMod

def ExactTailPiece (modulus : Nat) (word : List Bool) : Prop :=
  word = [false] ∨
    ∃ followers : List (List Bool),
      followers.length = modulus - 1 ∧
      (∀ piece ∈ followers, PrefixPiece piece) ∧
      word = true :: followers.flatten

def ExactCountSide (modulus residue : Nat) (word : List Bool) : Prop :=
  ∃ leading tail : List (List Bool),
    leading.length = residue ∧
    (∀ piece ∈ leading, PrefixPiece piece) ∧
    (∀ piece ∈ tail, ExactTailPiece modulus piece) ∧
    leading.flatten ++ tail.flatten = word

private theorem exists_falsePieces_exact : ∀ word : List Bool,
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

private theorem exists_prefixPieces_split_exact : ∀ k : Nat, ∀ word : List Bool,
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
      obtain ⟨pieces, tail, hlength, hpieces, hflat, htailCount⟩ :=
        ih rest (by omega)
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

private theorem exists_exactTailPieces_of_count
    (modulus : Nat) (hmodulus : 0 < modulus) :
    ∀ n : Nat, ∀ word : List Bool, word.count true = n → n % modulus = 0 →
      ∃ pieces : List (List Bool),
        (∀ piece ∈ pieces, ExactTailPiece modulus piece) ∧
        pieces.flatten = word := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih word hcount hmod
  by_cases hn : n = 0
  · have hwordZero : word.count true = 0 := by omega
    obtain ⟨pieces, hpieces, hflat⟩ := exists_falsePieces_exact word hwordZero
    exact ⟨pieces, (fun piece hp => Or.inl (hpieces piece hp)), hflat⟩
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hmodLe : modulus ≤ n :=
      Nat.le_of_dvd hnpos (Nat.dvd_iff_mod_eq_zero.mpr hmod)
    have hwordPositive : 0 < word.count true := by omega
    obtain ⟨zeros, afterFirst, hsplit, hzeros⟩ :=
      Counting.exists_first_occ true word
        (List.count_pos_iff.mp hwordPositive)
    have hafterCount : word.count true = 1 + afterFirst.count true := by
      rw [hsplit, List.count_append]
      simp [hzeros]
    have hfollowersLe : modulus - 1 ≤ afterFirst.count true := by omega
    obtain ⟨followers, rest, hfollowersLength, hfollowers, hfollowersFlat,
      hrestCount⟩ :=
        exists_prefixPieces_split_exact (modulus - 1) afterFirst hfollowersLe
    have hncount : n = modulus + rest.count true := by omega
    have hrestLt : rest.count true < n := by omega
    have hrestMod : rest.count true % modulus = 0 := by
      rw [hncount, Nat.add_mod] at hmod
      simpa using hmod
    obtain ⟨zeroPieces, hzeroPieces, hzeroFlat⟩ :=
      exists_falsePieces_exact zeros hzeros
    obtain ⟨tailPieces, htailPieces, htailFlat⟩ :=
      ih (rest.count true) hrestLt rest rfl hrestMod
    refine ⟨zeroPieces ++ (true :: followers.flatten) :: tailPieces, ?_, ?_⟩
    · intro piece hp
      simp only [List.mem_append, List.mem_cons] at hp
      rcases hp with hp | rfl | hp
      · exact Or.inl (hzeroPieces piece hp)
      · exact Or.inr ⟨followers, hfollowersLength, hfollowers, rfl⟩
      · exact htailPieces piece hp
    · rw [List.flatten_append, List.flatten_cons, hzeroFlat, htailFlat]
      simp only [List.cons_append]
      rw [hfollowersFlat]
      simpa [List.append_assoc] using hsplit.symm

private theorem exists_exactTailPieces (modulus : Nat) (hmodulus : 0 < modulus)
    (word : List Bool) (hmod : word.count true % modulus = 0) :
    ∃ pieces : List (List Bool),
      (∀ piece ∈ pieces, ExactTailPiece modulus piece) ∧
      pieces.flatten = word :=
  exists_exactTailPieces_of_count modulus hmodulus (word.count true) word rfl hmod

theorem count_exactTailPiece (modulus : Nat) (hmodulus : 0 < modulus)
    {word : List Bool} (hword : ExactTailPiece modulus word) :
    word.count true % modulus = 0 := by
  rcases hword with rfl | ⟨followers, hfollowersLength, hfollowers, rfl⟩
  · simp
  · have hcount : (true :: followers.flatten).count true =
        1 + followers.length := by
      simp [count_flatten_prefixPieces followers hfollowers, Nat.add_comm]
    rw [hcount, hfollowersLength]
    have : 1 + (modulus - 1) = modulus := by omega
    simp [this]

theorem count_flatten_exactTailPieces (modulus : Nat) (hmodulus : 0 < modulus)
    (pieces : List (List Bool))
    (hpieces : ∀ piece ∈ pieces, ExactTailPiece modulus piece) :
    pieces.flatten.count true % modulus = 0 := by
  induction pieces with
  | nil => simp
  | cons piece pieces ih =>
      have hp := count_exactTailPiece modulus hmodulus (hpieces piece (by simp))
      have hps : ∀ p ∈ pieces, ExactTailPiece modulus p := by
        intro p hpMem
        exact hpieces p (by simp [hpMem])
      rw [List.flatten_cons, List.count_append, Nat.add_mod]
      simp [hp, ih hps]

theorem exactCountSide_iff (modulus : Nat) (hmodulus : 0 < modulus)
    (residue : Nat) (hresidue : residue < modulus) (word : List Bool) :
    ExactCountSide modulus residue word ↔ word.count true % modulus = residue := by
  constructor
  · rintro ⟨leading, tail, hlength, hleading, htail, hflat⟩
    have hLeadingCount := count_flatten_prefixPieces leading hleading
    have hTailCount := count_flatten_exactTailPieces modulus hmodulus tail htail
    rw [← hflat, List.count_append, hLeadingCount, hlength, Nat.add_mod]
    simp [hTailCount, Nat.mod_eq_of_lt hresidue]
  · intro hmod
    have hresidueLe : residue ≤ word.count true := by
      rw [← hmod]
      exact Nat.mod_le _ _
    obtain ⟨leading, rest, hlength, hleading, hflat, hrestCount⟩ :=
      exists_prefixPieces_split_exact residue word hresidueLe
    have hdivision := Nat.mod_add_div (word.count true) modulus
    rw [hmod] at hdivision
    have hrestEq : rest.count true = modulus * (word.count true / modulus) := by
      omega
    have hrestMod : rest.count true % modulus = 0 := by simp [hrestEq]
    obtain ⟨tail, htail, htailFlat⟩ :=
      exists_exactTailPieces modulus hmodulus rest hrestMod
    exact ⟨leading, tail, hlength, hleading, htail, by simpa [htailFlat] using hflat⟩

end TokenMod

namespace TokenLift

variable {beta : Type u}

theorem prefixGroup_of_matches_mod (L0 L1 : Language beta)
    {tokens : List Bool} {pieces : List (Word beta)}
    (htokens : TokenMod.PrefixPiece tokens)
    (hmatch : List.Forall₂ (Matches L0 L1) tokens pieces) :
    PrefixGroup L0 L1 pieces := by
  rcases htokens with ⟨zeros, hzeros, rfl⟩
  obtain ⟨zeroPieces, lastPieces, hpEq, hzeroMatch, hlastMatch⟩ :=
    forall₂_append_split hmatch
  obtain ⟨last, rfl, hlast⟩ := matches_single_true L0 L1 hlastMatch
  have hzeros3 : Token3.ZeroWord zeros := by
    simpa [TokenMod.ZeroWord, Token3.ZeroWord] using hzeros
  exact ⟨zeroPieces, last, hpEq,
    matches_zero_all L0 L1 hzeros3 hzeroMatch, hlast⟩

theorem all_prefixGroups_of_forall₂_mod (L0 L1 : Language beta)
    {tokenGroups : List (List Bool)} {pieceGroups : List (List (Word beta))}
    (hrel : List.Forall₂ (List.Forall₂ (Matches L0 L1))
      tokenGroups pieceGroups)
    (htokens : ∀ group ∈ tokenGroups, TokenMod.PrefixPiece group) :
    ∀ group ∈ pieceGroups, PrefixGroup L0 L1 group := by
  induction hrel with
  | nil => simp
  | @cons tokenGroup pieceGroup tokenGroups pieceGroups hhead htail ih =>
      intro group hgroup
      simp only [List.mem_cons] at hgroup
      rcases hgroup with rfl | hgroup
      · exact prefixGroup_of_matches_mod L0 L1
          (htokens tokenGroup (by simp)) hhead
      · exact ih (by
          intro other hother
          exact htokens other (by simp [hother])) group hgroup

private theorem prefixGroups_chain_mem (L0 L1 : Language beta)
    (first : Word beta) (hfirst : first ∈ L1)
    (groups : List (List (Word beta)))
    (hgroups : ∀ group ∈ groups, PrefixGroup L0 L1 group) :
    first ++ groups.flatten.flatten ∈ Language.concat
      (Language.power (Language.concat L1 (Language.star L0)) groups.length) L1 := by
  induction groups generalizing first with
  | nil =>
      have hempty : [] ∈ Language.power
          (Language.concat L1 (Language.star L0)) 0 :=
        (mem_power_iff_factorizes_length
          (Language.concat L1 (Language.star L0)) 0 []).mpr
          ⟨[], factorizes_nil _, rfl⟩
      exact ⟨[], hempty, first, hfirst, by simp⟩
  | cons group groups ih =>
      obtain ⟨zeros, last, rfl, hzeros, hlast⟩ :=
        hgroups group (by simp)
      have hrest : ∀ other ∈ groups, PrefixGroup L0 L1 other := by
        intro other hother
        exact hgroups other (by simp [hother])
      obtain ⟨powerWord, hpower, lastWord, hlastWord, hflat⟩ :=
        ih last hlast hrest
      let pair := first ++ zeros.flatten
      have hpair : pair ∈ Language.concat L1 (Language.star L0) := by
        exact ⟨first, hfirst, zeros.flatten,
          (mem_star_iff_factorizes L0 zeros.flatten).mpr
            ⟨zeros, ⟨hzeros, rfl⟩⟩, rfl⟩
      have hpowerSucc : pair ++ powerWord ∈ Language.power
          (Language.concat L1 (Language.star L0)) (zeros.length * 0 + groups.length + 1) := by
        rw [show zeros.length * 0 + groups.length + 1 = Nat.succ groups.length by omega,
          Language.power_succ_left]
        exact ⟨pair, hpair, powerWord, hpower, rfl⟩
      refine ⟨pair ++ powerWord, ?_, lastWord, hlastWord, ?_⟩
      · simpa using hpowerSucc
      · simp [pair, List.flatten_append, hflat, List.append_assoc]

theorem flatten_exactTailPiece_mem (L0 L1 : Language beta)
    (modulus : Nat) {tokens : List Bool} {pieces : List (Word beta)}
    (htokens : TokenMod.ExactTailPiece modulus tokens)
    (hmatch : List.Forall₂ (Matches L0 L1) tokens pieces) :
    pieces.flatten ∈ L0 ∪ Language.concat
      (Language.power (Language.concat L1 (Language.star L0)) (modulus - 1)) L1 := by
  rcases htokens with rfl | ⟨followers, hlength, hfollowers, rfl⟩
  · obtain ⟨piece, rfl, hpiece⟩ := matches_single_false L0 L1 hmatch
    exact Or.inl (by simpa using hpiece)
  · obtain ⟨firstPieces, restPieces, hpEq, hfirstMatch, hrestMatch⟩ :=
      forall₂_append_split (left := [true])
        (right := followers.flatten) hmatch
    obtain ⟨first, rfl, hfirst⟩ := matches_single_true L0 L1 hfirstMatch
    obtain ⟨pieceGroups, hpieceGroups, hpieceFlat⟩ :=
      forall₂_flatten_split followers restPieces hrestMatch
    have hprefixGroups :=
      all_prefixGroups_of_forall₂_mod L0 L1 hpieceGroups hfollowers
    have hchain := prefixGroups_chain_mem L0 L1 first hfirst
      pieceGroups hprefixGroups
    have hgroupsLength : pieceGroups.length = modulus - 1 := by
      have := hpieceGroups.length_eq
      omega
    apply Or.inr
    rw [hgroupsLength, hpieceFlat] at hchain
    simpa [hpEq] using hchain

theorem mem_countSide_modulus_of_partition (L0 L1 : Language beta)
    (modulus : Nat) (hmodulus : 0 < modulus)
    (residue : Nat) (hresidue : residue < modulus)
    (pieces : List (Word beta))
    (hpieces : Factorizes (L0 ∪ L1) pieces pieces.flatten)
    (hcount : countIn L1 pieces % modulus = residue) :
    pieces.flatten ∈ Language.concat
      (Language.power (Language.concat (Language.star L0) L1) residue)
      (Language.star
        (L0 ∪ Language.concat
          (Language.power (Language.concat L1 (Language.star L0))
            (modulus - 1)) L1)) := by
  classical
  let tokens := tokensOfPartition L1 pieces
  have htokenCount : tokens.count true % modulus = residue := by
    simpa [tokens, tokensOfPartition, countIn, List.count, Function.comp_def]
      using hcount
  obtain ⟨leading, tail, hleadingLength, hleading, htail, hflat⟩ :=
    (TokenMod.exactCountSide_iff modulus hmodulus residue hresidue tokens).mpr
      htokenCount
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
  have hleadingGroups :=
    all_prefixGroups_of_forall₂_mod L0 L1 hleadingRel hleading
  have hleadingWords : ∀ word ∈ leadingPieces.map List.flatten,
      word ∈ Language.concat (Language.star L0) L1 := by
    intro word hword
    simp only [List.mem_map] at hword
    obtain ⟨group, hgroupMem, rfl⟩ := hword
    exact flatten_prefixGroup_mem L0 L1 group
      (hleadingGroups group hgroupMem)
  have htailWords : ∀ word ∈ tailPieces.map List.flatten,
      word ∈ L0 ∪ Language.concat
        (Language.power (Language.concat L1 (Language.star L0))
          (modulus - 1)) L1 := by
    intro word hword
    simp only [List.mem_map] at hword
    obtain ⟨group, hgroupMem, rfl⟩ := hword
    have findRel : ∀ tokenGroups pieceGroups,
        List.Forall₂ (List.Forall₂ (Matches L0 L1)) tokenGroups pieceGroups →
        (∀ tokenGroup ∈ tokenGroups,
          TokenMod.ExactTailPiece modulus tokenGroup) →
        ∀ pieceGroup ∈ pieceGroups,
          pieceGroup.flatten ∈ L0 ∪ Language.concat
            (Language.power (Language.concat L1 (Language.star L0))
              (modulus - 1)) L1 := by
      intro tokenGroups pieceGroups hrel
      induction hrel with
      | nil => simp
      | @cons tokenGroup pieceGroup tokenGroups pieceGroups hhead hrel ih =>
          intro htokens candidate hcand
          simp only [List.mem_cons] at hcand
          rcases hcand with rfl | hcand
          · exact flatten_exactTailPiece_mem L0 L1 modulus
              (htokens tokenGroup (by simp)) hhead
          · exact ih (by
              intro token htoken
              exact htokens token (by simp [htoken])) candidate hcand
    exact findRel tail tailPieces htailRel htail group hgroupMem
  have hleadingPower : (leadingPieces.map List.flatten).flatten ∈
      Language.power (Language.concat (Language.star L0) L1) residue := by
    apply (mem_power_iff_factorizes_length _ residue _).mpr
    refine ⟨leadingPieces.map List.flatten, ⟨hleadingWords, rfl⟩, ?_⟩
    have := hleadingRel.length_eq
    simpa [hleadingLength] using this.symm
  have htailStar : (tailPieces.map List.flatten).flatten ∈ Language.star
      (L0 ∪ Language.concat
        (Language.power (Language.concat L1 (Language.star L0))
          (modulus - 1)) L1) :=
    (mem_star_iff_factorizes _ _).mpr
      ⟨tailPieces.map List.flatten, ⟨htailWords, rfl⟩⟩
  have flatten_map_flatten : ∀ groups : List (List (Word beta)),
      (groups.map List.flatten).flatten = groups.flatten.flatten := by
    intro groups
    induction groups with
    | nil => rfl
    | cons group groups ih => simp [ih]
  rw [flatten_map_flatten] at hleadingPower htailStar
  have hflatten : leadingPieces.flatten.flatten ++ tailPieces.flatten.flatten =
      pieces.flatten := by
    rw [← List.flatten_append, ← List.flatten_append, ← hgroupsEq, hpieceFlat]
  exact ⟨leadingPieces.flatten.flatten, hleadingPower,
    tailPieces.flatten.flatten, htailStar, hflatten⟩

end TokenLift

/-- Exact transfer semantics for every positive modulus and every disjoint,
uniquely decipherable partition `L0 ∪ L1`. -/
theorem mem_formula_partition_iff (L0 L1 : Language alpha)
    (modulus : Nat) (hmodulus : 0 < modulus)
    (hdisjoint : Disjoint L0 L1)
    (hUnique : ∀ left right : List (Word alpha),
      Factorizes (L0 ∪ L1) left left.flatten →
      Factorizes (L0 ∪ L1) right right.flatten →
      left.flatten = right.flatten → left = right)
    (word : Word alpha) :
    word ∈ TransferCore.formula L0 L1 modulus ↔
      ∃ pieces : List (Word alpha),
        Factorizes (L0 ∪ L1) pieces word ∧
          countIn L0 pieces % modulus = 0 := by
  classical
  constructor
  · intro hword
    simp only [TransferCore.formula, Set.mem_iUnion] at hword
    obtain ⟨residue, hcell⟩ := hword
    have hboth : word ∈ Language.concat
          (Language.star (Language.power (L0 ∪ L1) modulus))
          (Language.power (L0 ∪ L1) residue.1) ∧
        word ∈ Language.concat
          (Language.power (Language.concat (Language.star L0) L1) residue.1)
          (Language.star
            (L0 ∪ Language.concat
              (Language.power (Language.concat L1 (Language.star L0))
                (modulus - 1)) L1)) := by
      simpa [TransferCore.cell] using hcell
    obtain ⟨lengthPieces, hlengthPieces, hlengthMod⟩ :=
      (mem_lengthSide_modulus_iff (L0 ∪ L1) modulus residue.1
        residue.isLt word).mp hboth.1
    obtain ⟨countPieces, hcountPieces, hcountMod⟩ :=
      mem_countSide_modulus_partition_imp L0 L1 modulus hmodulus hdisjoint
        residue.1 word hboth.2
    have hpEq : lengthPieces = countPieces :=
      hUnique lengthPieces countPieces
        ⟨hlengthPieces.1, rfl⟩ ⟨hcountPieces.1, rfl⟩
        (hlengthPieces.2.trans hcountPieces.2.symm)
    subst countPieces
    refine ⟨lengthPieces, hlengthPieces, ?_⟩
    have hpartition := countIn_partition L0 L1 hdisjoint
      lengthPieces hlengthPieces.1
    have hcountMod' : countIn L1 lengthPieces % modulus = residue.1 := by
      simpa [Nat.mod_eq_of_lt residue.isLt] using hcountMod
    have hmodEq : Nat.ModEq modulus (countIn L1 lengthPieces)
        (countIn L0 lengthPieces + countIn L1 lengthPieces) := by
      change countIn L1 lengthPieces % modulus =
        (countIn L0 lengthPieces + countIn L1 lengthPieces) % modulus
      rw [hpartition, hcountMod', hlengthMod]
    exact Nat.dvd_iff_mod_eq_zero.mp (Nat.right_modEq_add_iff.mp hmodEq)
  · rintro ⟨pieces, hpieces, hleftMod⟩
    let residue : Fin modulus :=
      ⟨countIn L1 pieces % modulus, Nat.mod_lt _ hmodulus⟩
    have hpartition := countIn_partition L0 L1 hdisjoint pieces hpieces.1
    have hlengthMod : pieces.length % modulus = residue.1 := by
      dsimp [residue]
      rw [← hpartition, Nat.add_mod, hleftMod]
      simp
    have hlength : word ∈ Language.concat
        (Language.star (Language.power (L0 ∪ L1) modulus))
        (Language.power (L0 ∪ L1) residue.1) :=
      (mem_lengthSide_modulus_iff (L0 ∪ L1) modulus residue.1
        residue.isLt word).mpr ⟨pieces, hpieces, hlengthMod⟩
    have hcount : word ∈ Language.concat
        (Language.power (Language.concat (Language.star L0) L1) residue.1)
        (Language.star
          (L0 ∪ Language.concat
            (Language.power (Language.concat L1 (Language.star L0))
              (modulus - 1)) L1)) := by
      have h := TokenLift.mem_countSide_modulus_of_partition
        L0 L1 modulus hmodulus residue.1 residue.isLt pieces
        ⟨hpieces.1, rfl⟩ (by rfl)
      simpa [hpieces.2] using h
    simp only [TransferCore.formula, Set.mem_iUnion]
    refine ⟨residue, ?_⟩
    simpa [TransferCore.cell] using And.intro hlength hcount

theorem mem_formula_letter_iff [DecidableEq alpha]
    (L1 : Language alpha) (label : alpha)
    (modulus : Nat) (hmodulus : 0 < modulus)
    (hdisjoint : ∀ word ∈ L1, word ≠ [label])
    (hUnique : ∀ left right : List (Word alpha),
      Factorizes (Language.letter label ∪ L1) left left.flatten →
      Factorizes (Language.letter label ∪ L1) right right.flatten →
      left.flatten = right.flatten → left = right)
    (word : Word alpha) :
    word ∈ TransferCore.formula (Language.letter label) L1 modulus ↔
      ∃ pieces : List (Word alpha),
        Factorizes (Language.letter label ∪ L1) pieces word ∧
          pieces.count [label] % modulus = 0 := by
  have hpartition : Disjoint (Language.letter label) L1 := by
    apply Set.disjoint_left.2
    intro word hletter hL1
    exact hdisjoint word hL1 hletter
  rw [mem_formula_partition_iff (Language.letter label) L1 modulus hmodulus
    hpartition hUnique word]
  apply exists_congr
  intro pieces
  apply and_congr_right
  intro _
  rw [countIn_letter_eq_count]

end TransferSemantics

end GSH
