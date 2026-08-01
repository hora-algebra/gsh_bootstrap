import GSHTest.Smoke
import GSHTest.FiniteBoolean
import GSHTest.FullAlphabet
import GSHTest.Reversal
import GSHTest.SyntacticMonoid
import GSHTest.D4ArrowAssembly
import GSHTest.Q8FullFiber
import GSHTest.Q8Height
import GSHTest.D5FullFiber
import GSHTest.D5ArrowCoordinates
import GSHTest.Axioms

/-! The test library.  `lakefile.toml` lists it in `defaultTargets`, so a bare
`lake build` compiles the axiom audit; before that the audit ran only from
`scripts/check.sh`, and `lake build` alone reported success without it. -/
