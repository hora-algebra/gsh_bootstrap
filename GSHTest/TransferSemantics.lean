import GSH.Height.TransferSemantics

set_option autoImplicit false

open GSH

example {alpha : Type} (code : Language alpha) (n : Nat) (word : Word alpha) :
    word ∈ Language.power code n ↔
      ∃ pieces : List (Word alpha),
        TransferSemantics.Factorizes code pieces word ∧ pieces.length = n :=
  TransferSemantics.mem_power_iff_factorizes_length code n word

example {alpha : Type} (code : Language alpha) (word : Word alpha) :
    word ∈ Language.star code ↔
      ∃ pieces : List (Word alpha),
        TransferSemantics.Factorizes code pieces word :=
  TransferSemantics.mem_star_iff_factorizes code word

example {alpha : Type} (code : Language alpha)
    (leftPieces rightPieces : List (Word alpha))
    (leftWord rightWord : Word alpha)
    (hleft : TransferSemantics.Factorizes code leftPieces leftWord)
    (hright : TransferSemantics.Factorizes code rightPieces rightWord) :
    TransferSemantics.Factorizes code (leftPieces ++ rightPieces)
      (leftWord ++ rightWord) :=
  TransferSemantics.factorizes_append hleft hright

example {alpha : Type} (code : Language alpha) (word : Word alpha) :
    word ∈ Language.star (Language.power code 3) ↔
      ∃ pieces : List (Word alpha),
        TransferSemantics.Factorizes code pieces word ∧
          pieces.length % 3 = 0 :=
  TransferSemantics.mem_star_power_three_iff code word

example {alpha : Type} (code : Language alpha) (residue : Nat)
    (hresidue : residue < 3) (word : Word alpha) :
    word ∈ Language.concat
        (Language.star (Language.power code 3))
        (Language.power code residue) ↔
      ∃ pieces : List (Word alpha),
        TransferSemantics.Factorizes code pieces word ∧
          pieces.length % 3 = residue :=
  TransferSemantics.mem_lengthSide_three_iff code residue hresidue word

example {alpha : Type} [DecidableEq alpha]
    (L0 L1 : Language alpha) (label : alpha)
    (hL0 : L0 = Language.letter label)
    (hdisjoint : ∀ word ∈ L1, word ≠ [label])
    (residue : Nat) (word : Word alpha)
    (hword : word ∈ Language.concat
      (Language.power (Language.concat (Language.star L0) L1) residue)
      (Language.star
        (L0 ∪ Language.concat
          (Language.power (Language.concat L1 (Language.star L0)) 2) L1))) :
    ∃ pieces : List (Word alpha),
      TransferSemantics.Factorizes (L0 ∪ L1) pieces word ∧
        TransferSemantics.otherCount label pieces % 3 = residue % 3 :=
  TransferSemantics.mem_countSide_three_imp L0 L1 label hL0 hdisjoint
    residue word hword

example (residue : Nat) (hresidue : residue < 3) (word : List Bool) :
    TransferSemantics.Token3.CountSide3 residue word ↔
      word.count true % 3 = residue :=
  TransferSemantics.Token3.countSide3_iff residue hresidue word

example (residue : Nat) (hresidue : residue < 8) (word : List Bool) :
    TransferSemantics.TokenMod.CountSide 8 residue word ↔
      word.count true % 8 = residue :=
  TransferSemantics.TokenMod.countSide_iff 8 (by omega) residue hresidue word

example (residue : Nat) (hresidue : residue < 4) (word : List Bool) :
    TransferSemantics.TokenMod.CountSide 4 residue word ↔
      word.count true % 4 = residue :=
  TransferSemantics.TokenMod.countSide_iff 4 (by omega) residue hresidue word

example {alpha : Type} [DecidableEq alpha]
    (L1 : Language alpha) (label : alpha)
    (hdisjoint : ∀ word ∈ L1, word ≠ [label])
    (hUnique : ∀ left right : List (Word alpha),
      TransferSemantics.Factorizes (Language.letter label ∪ L1)
        left left.flatten →
      TransferSemantics.Factorizes (Language.letter label ∪ L1)
        right right.flatten →
      left.flatten = right.flatten → left = right)
    (word : Word alpha) :
    word ∈ TransferCore.formula (Language.letter label) L1 3 ↔
      ∃ pieces : List (Word alpha),
        TransferSemantics.Factorizes (Language.letter label ∪ L1) pieces word ∧
          pieces.count [label] % 3 = 0 :=
  TransferSemantics.mem_formula_letter_three_iff
    L1 label hdisjoint hUnique word

example {alpha : Type} (L0 L1 : Language alpha)
    (hdisjoint : Disjoint L0 L1)
    (hUnique : ∀ left right : List (Word alpha),
      TransferSemantics.Factorizes (L0 ∪ L1) left left.flatten →
      TransferSemantics.Factorizes (L0 ∪ L1) right right.flatten →
      left.flatten = right.flatten → left = right)
    (word : Word alpha) :
    word ∈ TransferCore.formula L0 L1 3 ↔
      ∃ pieces : List (Word alpha),
        TransferSemantics.Factorizes (L0 ∪ L1) pieces word ∧
          TransferSemantics.countIn L0 pieces % 3 = 0 :=
  TransferSemantics.mem_formula_partition_three_iff
    L0 L1 hdisjoint hUnique word
