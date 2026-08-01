import GSH

set_option autoImplicit false

namespace GSHTest

open GSH

example : GRegex.starHeight (GRegex.star (GRegex.atom 'a')) = 1 := by
  rfl

example : GRegex.denote (GRegex.compl (GRegex.zero : GRegex Bool)) = Set.univ := by
  ext w
  simp [GRegex.denote, Language.compl, Language.empty]

example (M : DFA Bool Nat) (q : Nat) (u v : Word Bool) :
    M.run q (u ++ v) = M.run (M.run q u) v := by
  exact DFA.run_append M q u v

/-! ### Semantic checks on the counting construction

These guard against the height-one ladder being vacuous.  The first is the
concrete instance the abelian argument reduces to; the second checks that the
counting expression really does contain a star, so that the bound `≤ 1` is not
secretly a proof of star-freeness (which would be false — a nontrivial group
language is not star-free, by Schützenberger). -/

example : HasHeightAtMost {w : Word Bool | w.count true % 2 = 0} 1 :=
  Counting.hasHeightAtMost_count true (by norm_num)

example : GRegex.starHeight (Counting.cnt true 2 0) = 1 := by
  simp [Counting.cnt, Counting.blk, Counting.noA, Counting.hasA, Counting.univR,
    GRegex.starHeight, GRegex.pow]

/-! ### The order-five ladder is instantiable

`heightOneUpTo_five` is a statement about every group of order at most five;
these two check that it actually applies to concrete groups, in particular to a
non-cyclic one. -/

example : HeightOneForGroup (Multiplicative (ZMod 5)) :=
  heightOneUpTo_five _ (by simp)

example : HeightOneForGroup (Multiplicative (ZMod 2 × ZMod 2)) :=
  heightOneUpTo_five _ (by simp)

/-! ### The index-two input for the `S₃` route is instantiable

The missing step is still the Pin–Straubing–Thérien lift from the commutative
kernel to the whole semidirect product.  These checks pin down its concrete
`S₃` input without asserting the missing lift.
-/

example : HeightOneForGroup (alternatingGroup (Fin 3)) :=
  heightOne_A3

example :
    ∃ A : Subgroup (Equiv.Perm (Fin 3)),
      A.index = 2 ∧ HeightOneForGroup A :=
  s3_has_heightOne_index_two_subgroup

end GSHTest
