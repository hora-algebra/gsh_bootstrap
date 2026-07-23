# Cross-Disciplinary Glossary

| Term | Meaning in this project | Common trap |
|---|---|---|
| alphabet `A` | finite type/set of letters | forgetting finiteness when constructing automata |
| word | finite list of letters, element of `A*` | using `A+` and losing the empty word |
| language | subset of `A*` | treating a finite sample as the language |
| generalized expression | regex with Boolean complement relative to `A*` | complementing relative to a sampled universe |
| expression height | nesting depth of Kleene star in a syntax tree | confusing with language height |
| language height | minimum expression height over all equivalent generalized expressions | using the height of one expression as a lower bound |
| star-free | language denoted without Kleene star | not the same as finite or aperiodic automaton graph |
| recognition by `M` | `L = φ⁻¹(P)` for a monoid morphism `φ : A* → M` and `P ⊆ M` | claiming the syntactic monoid is `M` |
| syntactic monoid | quotient of `A*` by two-sided contextual equivalence for `L` | constructing quotient before proving congruence |
| divisor of a monoid | homomorphic image of a submonoid | confusing subgroup, quotient, and divisor |
| group language | language recognized by a finite group | not every regular language is a group language |
| `HeightOneForGroup G` | every language recognized by `G` has generalized height ≤1 | does not say syntactic group exactly `G` |
| `A_4` | alternating group on four points, `(C2 × C2) ⋊ C3` | skipping it in favor of `A_5` despite the order-12 barrier |
| `Dic_3` | dicyclic/binary dihedral group of order 12 in the thesis notation | notation differs across sources |
| `A_5` | alternating group on five points, simple and non-solvable | proving an `A_5` case is not the global theorem |
| cocycle | function satisfying a specified cohomological identity for a stated action/module | using “cocycle” without coefficients or action |
| certificate | finite data checked by a small deterministic verifier | trusting generated prose or an unchecked regex |
| formalized | accepted by the pinned Lean kernel with declared assumptions | a theorem signature containing `sorry` |
