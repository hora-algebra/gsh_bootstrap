import GSH.Height.D4FlipPairQuotients

set_option autoImplicit false

namespace GSHTest

open GSH
open GSH.D4ArrowArithmetic
open GSH.D4FlipPairQuotients

example (x y : D4PhaseOne) (residue : Fin 8) :
    Language.leftQuotient y.1
        (Language.leftQuotient x.1
          (d4PairResidue x y residue)) =
      d4PairResidue x y
        ⟨(residue.1 + 7) % 8, Nat.mod_lt _ (by omega)⟩ :=
  leftQuotient_pair_eq_pred x y residue

/-- Exact consumer for all eight actual phase-zero pair-count residues. -/
example (x y : D4PhaseOne) (hne : x.1 ≠ y.1) (residue : Fin 8) :
    HasHeightAtMost (d4PairResidue x y residue) 1 :=
  hasHeightAtMost_d4PairResidue x y hne residue

end GSHTest
