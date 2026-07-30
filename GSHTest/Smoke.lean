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

example : GRegex.starHeight A5Gen145.certificate = 1 :=
  A5Gen145.starHeight_certificate_eq

example : A4FullAlphabet.wordProblem =
    A4FullAlphabet.recognition.language := rfl

end GSHTest
