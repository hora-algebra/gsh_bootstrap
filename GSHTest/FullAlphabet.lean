import GSH.Height.FullAlphabet

/-!
# Compile-time acceptance tests for the full-alphabet reduction

These examples pin the three public consequences needed by the finite-group
ladder: alphabetic inverse images, one-letter left quotients, and reduction
from the full-alphabet identity fibre to all languages recognized by a finite
group.
-/

set_option autoImplicit false

namespace GSHTest

open GSH

universe u v

example {α : Type u} {β : Type v} [Fintype α] [DecidableEq β]
    (f : α → β) (r : GRegex β) :
    GRegex.starHeight (GRegex.inverseLetterMap f r) ≤ GRegex.starHeight r :=
  GRegex.starHeight_inverseLetterMap_le f r

example {α : Type u} {β : Type v} [Fintype α] [DecidableEq β]
    (f : α → β) {L : Language β} {n : Nat} (hL : HasHeightAtMost L n) :
    HasHeightAtMost (Language.inverseLetterMap f L) n :=
  hL.inverseLetterMap f

example {α : Type u} [DecidableEq α] (a : α) (r : GRegex α) :
    GRegex.starHeight (GRegex.derivative a r) ≤ GRegex.starHeight r :=
  GRegex.starHeight_derivative_le a r

example {α : Type u} [DecidableEq α] (a : α)
    {L : Language α} {n : Nat} (hL : HasHeightAtMost L n) :
    HasHeightAtMost (Language.leftQuotient a L) n :=
  hL.leftQuotient a

example {G : Type v} [Group G] [Fintype G]
    (h : HasHeightAtMost (fullIdentityFiber G) 1) :
    HeightOneForGroup.{u, v} G :=
  heightOneForGroup_of_fullIdentityFiber h

end GSHTest
