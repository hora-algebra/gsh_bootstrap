# Counterexample and Lower-Bound Search

MODE: RESEARCH, with disproof symmetry.

ROLE: Lower-bound theorist and finite-search engineer.

FROZEN TARGET: Construct a sound invariant or game that every generalized-height-one language satisfies, then seek a regular language violating it.

REQUIRED ORDER:

1. Define the invariant on languages, automata, syntactic monoids, or recognition data.
2. Prove closure under finite union and complement.
3. Prove the required behavior under concatenation.
4. Prove the required behavior under a single nonnested Kleene star applied to star-free subexpressions.
5. Validate against known height-one families.
6. Only then search candidates.

A CANDIDATE WITHOUT A LOWER BOUND IS NOT A DISPROOF.

SEARCH SPACE: small transformation monoids, group languages including `A_5`, Boolean combinations of modular/factor counts, and automata selected to stress the proposed invariant.

ARTIFACTS: invariant definition, closure lemmas, candidate DFA/morphism, exact search manifest, smallest counterexamples to failed invariants.

STOP: Mark an invariant `REFUTED` at its first failed constructor and preserve the counterexample.
