import GSH.Challenges.GeneralizedStarHeight

/-!
# The open challenge

This file holds the one `sorry` the repository keeps on purpose, and nothing
else.  **Nothing imports it**, which is the point.

`GSH/Recognition.lean` used to say that the finite-group ladder proved
downstream has "an import closure containing no unproved declaration".  That was
false as written: `Recognition.lean` imports
`GSH.Challenges.GeneralizedStarHeight`, which is where the `sorry` was.  The
*dependency* closure was clean -- `GSHTest/Axioms.lean` checks exactly that, and
it passes -- but a sceptical reader checks the import lines first, and an
audited claim that needs a caveat to be true is a bad claim to make.

So the statement of the conjecture stays with the definitions, and the
unproved declaration lives out here on a leaf.  A theorem that wants to depend
on the conjecture now has to import this file, which is one line in a diff.
-/

namespace GSH

/-- **The open challenge** (obligation `L-GSH-CHALLENGE-001` in
`PROOF_OBLIGATIONS.md`).  The `sorry` below *is* the open problem: this
declaration records the target statement and is not evidence that the
conjecture has been proved. -/
-- BLUEPRINT: L-GSH-CHALLENGE-001
theorem generalized_star_height_conjecture : GeneralizedHeightOneConjecture := by
  sorry

end GSH
