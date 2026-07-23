# Survey: Generalized Star Height and the Finite-Group Program

**Survey date:** 22 July 2026  
**Scope:** regular languages of finite words; generalized regular expressions with complement; emphasis on algebraic recognition, Pin-Straubing-Thérien, small finite groups, and a possible `A_5` program.

## 1. Status and exact problem statement

Let `A` be a finite alphabet. A generalized regular expression is built from `∅`, `ε`, and letters in `A` using finite union, concatenation, complement relative to `A*`, and Kleene star. Its generalized star-height is the maximum number of nested stars. The height of a language is the minimum height of an expression denoting it.

The term “generalized star-height problem” has two closely related meanings:

- **Decision problem:** Given a regular language, compute its generalized star-height.
- **Height-one collapse conjecture:** Every regular language has generalized star-height at most one.

The second is the sharper workshop target. No regular language of generalized star-height greater than one is known. Place and Zeitoun's survey-level introduction states that the decision problem remains open and that even the existence of a language of height greater than one is unknown. Bourne's thesis and the 2016 Bourne-Ruškuc paper state the same. A 2022 logic paper still describes the collapse question as unresolved, and a December 2025 seminar program lists new work on “Tackling the generalised star-height problem.” This bootstrap's search located no published resolution through 22 July 2026.

Do not confuse this with the **restricted** star-height problem, where complement is unavailable. Restricted star-height is unbounded, and its decision problem was solved by Hashiguchi. Those results do not settle the generalized problem because complement can eliminate stars in nonlocal ways.

## 2. Height zero: the established base case

Generalized star-height zero languages are the **star-free languages**. Schützenberger proved that a regular language is star-free exactly when its syntactic monoid is aperiodic. McNaughton and Papert gave the logical characterization by first-order logic over word positions with order.

This base case matters operationally:

- a proof of height-one collapse would make exact height computation binary: height zero versus height one;
- a counterexample must first survive the decidable aperiodicity/star-free test;
- the Lean project should formalize star-free syntax and the syntactic congruence before attempting any height-one theorem.

## 3. Pin, Straubing, and Thérien (1989/1992)

The 1992 paper *Some Results on the Generalized Star-Height Problem* is the main algebraic starting point. Its results include:

1. **Closure at bounded height** under left and right quotients, inverse alphabetic morphisms, and injective star-free substitutions.
2. **Commutative groups:** languages recognized by finite commutative groups have generalized star-height at most one.
3. **Nilpotent groups of class two:** the commutative result extends to finite nilpotent groups of class at most two.
4. **A semidirect-product family:** the result extends to groups dividing a semidirect product of a commutative group by a finite elementary abelian 2-group.
5. **Candidate elimination:** a language long conjectured to have height two is shown to have height one.
6. **Pseudovariety results:** one obtains height-one bounds for languages recognized by monoids in pseudovarieties generated using aperiodic monoids and commutative groups via wreath products.
7. **Universality observation:** every rational language is an inverse image, under a free-monoid morphism, of a language of restricted star-height one. This is structurally striking but does not decide generalized height.

### Why the proof technology is relevant to a workshop

The paper's successful arguments repeatedly turn a group-recognition problem into explicit counting languages, then use closure under inverse morphisms and substitutions. This suggests a three-layer formal architecture:

- **combinatorial layer:** exact/modular counting of letters, factors, or automaton arrows;
- **algebraic layer:** decomposition of recognizing groups/monoids;
- **closure layer:** transport of a height-one certificate through quotients, inverse morphisms, and substitutions.

Each layer is independently formalizable and independently testable.

## 4. Bourne and Ruškuc: factor counting and Rees matrix semigroups

Bourne and Ruškuc prove that, in several factor-counting cases, exact-count languages are star-free and modular-count languages have generalized star-height at most one. They apply these combinatorial expressions to show:

> Every language recognized by a finite Rees (zero-)matrix semigroup over an abelian group has generalized star-height at most one.

The paper is especially useful for formalization because it contains explicit expressions rather than only an abstract existence proof. Such expressions can become machine-checkable certificates.

Bourne's thesis extends the same program to Rees zero-matrix semigroups over finite monogenic semigroups and develops “count arrows” for cyclic automata.

## 5. The first unresolved finite-group barrier is order 12

A crucial correction to an `A_5`-first plan is documented in Bourne's thesis.

- Pin-Straubing-Thérien imply that every language recognized by a group of order less than 12 has generalized star-height at most one.
- At order 12, three of the five groups are covered by preceding results.
- The remaining groups are
  - `A_4 ≅ (C_2 × C_2) ⋊ C_3`, and
  - `Dic_3 ≅ C_3 ⋊ C_4` in the notation used by Bourne.
- Bourne attempts to extend the `A ⋊ C_2` proof to `A ⋊ C_3`. The route fails because words cannot be uniquely factorized into the required consecutive non-overlapping subwords. The thesis therefore leaves `A_4`, `Dic_3`, and more generally `A ⋊ C_r` for `r ≥ 3` open in that approach.

### Workshop implication

The lowest-risk publishable milestone is not `A_5`. It is one of:

1. a height-one theorem for languages recognized by `A_4`;
2. a height-one theorem for `Dic_3`;
3. a repair or replacement of the failed unique-factorization mechanism for `A ⋊ C_3`;
4. a rigorous obstruction showing why the entire cyclic-automaton/count-arrow template cannot extend in a specified form.

A Lean formalization of the failure itself would also be useful: it prevents future agents from repeatedly rediscovering the same blocked route.

## 6. Why `A_5` remains strategically attractive

`A_5` is the smallest nonabelian simple finite group and a canonical first non-solvable group. It is a natural stress test because:

- induction on abelian or nilpotent extensions cannot directly decompose it;
- it has concrete permutation actions and a manageable subgroup lattice;
- mathlib already realizes it as `alternatingGroup (Fin 5)` and contains a simplicity theorem;
- its conjugacy classes and low-dimensional representations are small enough for exact computation;
- any successful `A_5` theorem would show that height-one methods are not confined to solvable recognition groups.

However, an `A_5` theorem would still address only **group languages recognized by `A_5`**, not all regular languages. It should be presented as a structural milestone, not as a resolution of the global problem unless accompanied by a reduction from arbitrary syntactic monoids.

## 7. Cohomology: a disciplined speculative program

No surveyed preceding work establishes a cohomological invariant that detects generalized star-height. The following are research questions, not facts.

### 7.1 Extension classes as proof-search coordinates

For an extension

```text
1 -> N -> G -> Q -> 1,
```

the Lyndon-Hochschild-Serre viewpoint organizes group information by the action of `Q` on cohomology of `N` and by extension classes. A language-theoretic theorem could become inductive if one proves a transport principle of the form:

```text
height-one for N + height-one for Q + control of the extension cocycle
  => height-one for G.
```

The first task is not to invoke a spectral sequence. It is to define the coefficient object that actually records recognition data and to show that the cocycle controls a concrete factorization/counting formula.

### 7.2 Candidate coefficient objects

Explore, separately:

- permutation modules generated by transition states or accepting fibers;
- modules generated by letter-count or arrow-count functions;
- the augmentation ideal of a group algebra of the recognizing group;
- functions on conjugacy classes or coset spaces;
- bimodules attached to syntactic monoids, leading to Hochschild rather than group cohomology.

For each candidate, require an exact map from words or automaton paths to cocycles/coboundaries. If no such map is given, “use cohomology” is only vocabulary.

### 7.3 `A_5` decomposition matrix

The `A_5` track should test restriction to proper subgroups, induction from coset actions, and compatibility across overlaps. One possible matrix is:

| Object | Language question | Cohomological question | Certificate target |
|---|---|---|---|
| cyclic subgroups | modular counts | periodic cocycles | explicit height-one regex |
| Klein four subgroups | class-2/abelian formulas | restriction and invariants | Boolean combination of counts |
| `A_4` subgroups | first unresolved ladder case | extension by `C_3` | repaired arrow-count formula |
| dihedral subgroups | semidirect `C_n ⋊ C_2` formulas | transfer/restriction | Pin-style certificate |
| coset action on 5 points | permutation automata | induced modules | DFA/regex equivalence certificate |
| whole `A_5` | gluing across subgroup data | obstruction or vanishing class | theorem or explicit counterexample |

The program is successful even before a global theorem if it produces a sharp obstruction class whose nonzero value is provably incompatible with an existing height-one construction.

## 8. Proof routes worth keeping alive

### Route P1: repair the `C_3` arrow-count argument

Replace unique factorization by one of:

- unambiguous rational transductions;
- marked factorization forests;
- inclusion-exclusion over bounded overlaps;
- automata with a canonical parsing state;
- a finite-state synchronization code that turns overlapping factors into disjoint events.

Acceptance criterion: an explicit height-one expression or a compositional certificate for the relevant `ModCount` language.

### Route P2: pseudovariety closure theorem

Seek a closure operation on finite monoids/groups that:

- contains the known abelian and class-2 nilpotent cases;
- includes `A_4` or a meaningful `A_5`-related family;
- preserves height-one recognizability;
- is expressible as a finite algebraic construction that Lean can formalize.

Acceptance criterion: a theorem with exact hypotheses and a proof that transports certificates.

### Route P3: factorization forest / profinite identity

Try to characterize height-one languages by identities, a finite-index congruence, or a game. This is attractive for lower bounds because explicit-expression methods are naturally one-sided: they prove upper bounds but rarely prove that height one is impossible.

Acceptance criterion: a sound invariant `I(L)` that every height-one language satisfies, together with a candidate language violating it.

### Route P4: direct finite-group synthesis

For a fixed finite group and generating alphabet, enumerate recognizing morphisms up to automorphism and search for height-one expressions. Use exact equivalence checking against the minimal DFA.

Acceptance criterion: a verified expression certificate. Failure to find one is not evidence of height greater than one.

### Route P5: cohomological induction/gluing

Use subgroup restrictions to generate local height-one certificates and identify a gluing obstruction.

Acceptance criterion: a theorem that states and proves either (a) local certificates glue under an explicit vanishing condition, or (b) a nonvanishing class obstructs a specified normal form of height-one expressions.

## 9. Disproof routes

A true disproof of height-one collapse needs both:

1. an explicit regular language; and
2. a rigorous lower bound showing that no height-one generalized expression denotes it.

Candidate generation can use `A_5`, transformation monoids, or small syntactic monoids, but the decisive object is a **lower-bound invariant**. Plausible sources include:

- an Ehrenfeucht-Fraïssé or expression-size/height game specialized to generalized expressions;
- profinite identities satisfied by all height-one languages;
- a topological invariant of the Boolean algebra generated by starred star-free languages;
- a categorical obstruction preserved by union, complement, concatenation, and one nonnested use of star;
- a cohomological invariant with a proven closure calculus.

The project should not spend most of its computation budget enumerating candidates before it has at least one plausible lower-bound mechanism.

## 10. Lean formalization priorities

1. Words and languages as `List A` and `Set (List A)`.
2. Generalized regular expressions, semantics, and star-height.
3. Deterministic finite automata and equivalence certificates.
4. Recognition by finite monoids/groups.
5. Syntactic congruence and quotient monoid.
6. Star-free syntax and Schützenberger interface.
7. Closure operations used by Pin-Straubing-Thérien.
8. Exact/modular factor-count languages and explicit certificates.
9. Cyclic automata and arrow-count languages.
10. Small groups (`A_4`, `Dic_3`) before the full `A_5` track.
11. `A_5 = alternatingGroup (Fin 5)` and subgroup/representation data.
12. Only then: formal cohomology interfaces needed by a concrete proof.

## 11. Reading order by role

### Formal-language theorists

1. Pin-Straubing-Thérien (1992), especially closure operations and Sections 7–8.
2. Bourne-Ruškuc (2016), for explicit factor-count certificates.
3. Bourne thesis Chapters 4–5, especially the failed `C_3` extension.
4. Sakarovitch for standard automata/monoid background.

### Group/number theorists

1. `docs/textbook_number_theorists.pdf`.
2. The precise recognition definition and syntactic-monoid distinction.
3. Pin-Straubing-Thérien's nilpotent/semidirect-product proofs.
4. Bourne's order-12 table and failure analysis.
5. Only then the `A_5` subgroup/cohomology matrix.

### Lean experts

1. `docs/textbook_lean_experts.pdf`.
2. `GSH/Challenges/GeneralizedStarHeight.lean` (words/languages and generalized expressions, consolidated in one file 2026-07-23).
3. `GSH/Recognition.lean` (recognition, syntactic congruence, aperiodicity) before finite-group APIs.
4. Mathlib's `Mathlib.GroupTheory.SpecificGroups.Alternating`.

## 12. Core references

- L. C. Eggan, “Transition Graphs and the Star-Height of Regular Events,” *Michigan Mathematical Journal* 10 (1963), 385–397.
- K. Hashiguchi, “Algorithms for Determining Relative Star Height and Star Height,” *Information and Computation* 78 (1988), 124–169.
- M.-P. Schützenberger, “On Finite Monoids Having Only Trivial Subgroups,” *Information and Control* 8 (1965), 190–194.
- R. McNaughton and S. Papert, *Counter-Free Automata*, MIT Press, 1971.
- J.-É. Pin, H. Straubing, and D. Thérien, “Some Results on the Generalized Star-Height Problem,” *Information and Computation* 101(2) (1992), 219–250. DOI: 10.1016/0890-5401(92)90063-L.
- T. Bourne and N. Ruškuc, “On the Star-Height of Subword Counting Languages and Their Relationship to Rees Zero-Matrix Semigroups,” *Theoretical Computer Science* 653 (2016), 87–96. DOI: 10.1016/j.tcs.2016.09.024.
- T. Bourne, *Counting Subwords and Other Results Related to the Generalised Star-Height Problem for Regular Languages*, PhD thesis, University of St Andrews, 2017.
- T. Place and M. Zeitoun, “Generic Results for Concatenation Hierarchies,” arXiv:1710.04313.
- J. Sakarovitch, *Elements of Automata Theory*, Cambridge University Press, 2009.

### Online sources used for status verification

- Place-Zeitoun PDF: https://arxiv.org/pdf/1710.04313
- Pin-Straubing-Thérien record: https://hal.science/hal-00019978v1
- Bourne thesis: https://hdl.handle.net/10023/12024
- Bourne-Ruškuc open version: https://hdl.handle.net/10023/11811
- Mathlib alternating-group module: https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/SpecificGroups/Alternating.html
