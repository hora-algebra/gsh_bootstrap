import GSHTest.Smoke
import GSHTest.A4Products
import GSHTest.FiniteBoolean
import GSHTest.FullAlphabet
import GSHTest.Nilpotent2
import GSHTest.Reversal
import GSHTest.SyntacticMonoid
import GSHTest.Axioms

/-! The test library.  `lakefile.toml` lists it in `defaultTargets`, so a bare
`lake build` compiles the axiom audit; before that the audit ran only from
`scripts/check.sh`, and `lake build` alone reported success without it. -/
