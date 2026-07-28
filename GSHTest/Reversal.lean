import GSH.Height.Reversal

/-!
# Compile-time acceptance tests for reversal closure

The `A4-FULL-01` proof uses the same height-one feature languages on the
reversed input word.  These examples pin the exact semantic and height
interfaces needed by its eventual Lean formalization.
-/

set_option autoImplicit false

namespace GSHTest

open GSH

universe u

example {α : Type u} (r : GRegex α) :
    GRegex.denote (GRegex.reverse r) =
      Language.reverse (GRegex.denote r) :=
  GRegex.denote_reverse r

example {α : Type u} (r : GRegex α) :
    GRegex.starHeight (GRegex.reverse r) = GRegex.starHeight r :=
  GRegex.starHeight_reverse r

example {α : Type u} {L : Language α} {n : Nat}
    (hL : HasHeightAtMost L n) :
    HasHeightAtMost (Language.reverse L) n :=
  hL.reverse

end GSHTest
