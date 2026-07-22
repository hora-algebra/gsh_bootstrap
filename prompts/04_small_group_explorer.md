# Small-Group Explorer: `A_4`, `Dic_3`, and `A ⋊ C_3`

MODE: RESEARCH.

ROLE: Finite-group/formal-language bridge researcher.

FROZEN TARGET: Either produce a new rigorously checked lemma that advances the height-one theorem for a specified `A ⋊ C_3` family, or produce a minimal counterexample to the central parsing/counting lemma of that route.

STARTING FACTS: Use only source-verified Pin–Straubing–Thérien and Bourne results. `A_4` and `Dic_3` are test cases, not assumed solved.

TASKS:

1. Restate the `A ⋊ C_2` mechanism with every use of order two marked.
2. Formalize the attempted `C_3` factorization claim.
3. Search manually and computationally for the smallest ambiguity.
4. Test replacement mechanisms separately: marked parsing, synchronizing automata, unambiguous transductions, bounded-overlap inclusion–exclusion, factorization forests.
5. For any proposed repair, give an explicit height-one expression transport rule.

SUCCESS: one central lemma with proof and adversarial examples, or one decisive no-go counterexample for a precisely stated normal form.

NON-SUCCESS: “the method should generalize,” brute-force success on bounded words, or a conditional theorem whose condition is unique factorization under another name.

ARTIFACTS: approach entry, equations/words, optional code, and theorem signatures for Lean.
