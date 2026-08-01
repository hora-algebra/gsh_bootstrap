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
