import GSH.Height.TransferModulusSemantics

set_option autoImplicit false

open GSH

example {alpha : Type} (code : Language alpha) (word : Word alpha) :
    word ∈ Language.star (Language.power code 8) ↔
      ∃ pieces : List (Word alpha),
        TransferSemantics.Factorizes code pieces word ∧
          pieces.length % 8 = 0 :=
  TransferSemantics.mem_star_power_modulus_iff code 8 word

example {alpha : Type} (code : Language alpha) (residue : Fin 8)
    (word : Word alpha) :
    word ∈ Language.concat
        (Language.star (Language.power code 8))
        (Language.power code residue.1) ↔
      ∃ pieces : List (Word alpha),
        TransferSemantics.Factorizes code pieces word ∧
          pieces.length % 8 = residue.1 :=
  TransferSemantics.mem_lengthSide_modulus_iff
    code 8 residue.1 residue.isLt word

example {alpha : Type} (code : Language alpha) (residue : Fin 4)
    (word : Word alpha) :
    word ∈ Language.concat
        (Language.star (Language.power code 4))
        (Language.power code residue.1) ↔
      ∃ pieces : List (Word alpha),
        TransferSemantics.Factorizes code pieces word ∧
          pieces.length % 4 = residue.1 :=
  TransferSemantics.mem_lengthSide_modulus_iff
    code 4 residue.1 residue.isLt word

example {alpha : Type} (L0 L1 : Language alpha)
    (hdisjoint : Disjoint L0 L1)
    (hUnique : ∀ left right : List (Word alpha),
      TransferSemantics.Factorizes (L0 ∪ L1) left left.flatten →
      TransferSemantics.Factorizes (L0 ∪ L1) right right.flatten →
      left.flatten = right.flatten → left = right)
    (word : Word alpha) :
    word ∈ TransferCore.formula L0 L1 8 ↔
      ∃ pieces : List (Word alpha),
        TransferSemantics.Factorizes (L0 ∪ L1) pieces word ∧
          TransferSemantics.countIn L0 pieces % 8 = 0 :=
  TransferSemantics.mem_formula_partition_iff
    L0 L1 8 (by omega) hdisjoint hUnique word

example {alpha : Type} (L0 L1 : Language alpha)
    (hdisjoint : Disjoint L0 L1)
    (hUnique : ∀ left right : List (Word alpha),
      TransferSemantics.Factorizes (L0 ∪ L1) left left.flatten →
      TransferSemantics.Factorizes (L0 ∪ L1) right right.flatten →
      left.flatten = right.flatten → left = right)
    (word : Word alpha) :
    word ∈ TransferCore.formula L0 L1 4 ↔
      ∃ pieces : List (Word alpha),
        TransferSemantics.Factorizes (L0 ∪ L1) pieces word ∧
          TransferSemantics.countIn L0 pieces % 4 = 0 :=
  TransferSemantics.mem_formula_partition_iff
    L0 L1 4 (by omega) hdisjoint hUnique word

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
  TransferSemantics.mem_formula_partition_iff
    L0 L1 3 (by omega) hdisjoint hUnique word

/- The arbitrary-modulus theorem has exactly the old modulus-three result
type, so existing S3 consumers retain their semantic contract. -/
example {alpha : Type} (L0 L1 : Language alpha)
    (hdisjoint : Disjoint L0 L1)
    (hUnique : ∀ left right : List (Word alpha),
      TransferSemantics.Factorizes (L0 ∪ L1) left left.flatten →
      TransferSemantics.Factorizes (L0 ∪ L1) right right.flatten →
      left.flatten = right.flatten → left = right)
    (word : Word alpha) :
    TransferSemantics.mem_formula_partition_iff
        L0 L1 3 (by omega) hdisjoint hUnique word =
      TransferSemantics.mem_formula_partition_three_iff
        L0 L1 hdisjoint hUnique word := by
  apply Subsingleton.elim

/- Degenerate positive edge: modulus one has one residue and remains covered. -/
example {alpha : Type} (L0 L1 : Language alpha)
    (hdisjoint : Disjoint L0 L1)
    (hUnique : ∀ left right : List (Word alpha),
      TransferSemantics.Factorizes (L0 ∪ L1) left left.flatten →
      TransferSemantics.Factorizes (L0 ∪ L1) right right.flatten →
      left.flatten = right.flatten → left = right)
    (word : Word alpha) :
    word ∈ TransferCore.formula L0 L1 1 ↔
      ∃ pieces : List (Word alpha),
        TransferSemantics.Factorizes (L0 ∪ L1) pieces word ∧
          TransferSemantics.countIn L0 pieces % 1 = 0 :=
  TransferSemantics.mem_formula_partition_iff
    L0 L1 1 (by omega) hdisjoint hUnique word

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
    word ∈ TransferCore.formula (Language.letter label) L1 8 ↔
      ∃ pieces : List (Word alpha),
        TransferSemantics.Factorizes (Language.letter label ∪ L1) pieces word ∧
          pieces.count [label] % 8 = 0 :=
  TransferSemantics.mem_formula_letter_iff
    L1 label 8 (by omega) hdisjoint hUnique word
