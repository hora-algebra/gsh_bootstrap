# Scenarios for the Generalized Star-Height Project

This file is a decision tree for the workshop. It distinguishes a proof of height-one collapse, a disproof by an explicit height-greater-than-one language, structural partial results, formalization-only outcomes, and failure modes. It should be read before launching long-running agents.

## 0. What counts as resolution?

### Global affirmative resolution

A proof that every regular language over every finite alphabet has generalized star-height at most one.

A complete proof must provide:

1. a precise representation of regular languages (DFA, syntactic monoid, or generalized expression);
2. a construction or existence theorem for a height-one generalized expression;
3. a proof that the construction preserves semantics for all words, not only bounded samples;
4. treatment of the empty word and complement relative to the working alphabet;
5. all closure and induction steps with their exact hypotheses;
6. independent mathematical review and, for the formalized route, a clean Lean build without undeclared axioms.

### Global negative resolution

An explicit regular language `L` together with a proof that `L` has generalized star-height at least two.

A complete disproof must provide:

1. a finite alphabet;
2. a concrete DFA or recognizing morphism for `L`;
3. an upper-bound expression proving regularity;
4. a lower-bound invariant applying to **all** height-one generalized expressions;
5. a proof that `L` violates that invariant;
6. independent reconstruction of the lower-bound argument.

A failed bounded expression search is not item 4.

### Decision-problem resolution

An algorithm that computes the exact generalized star-height of every regular language, with a termination and correctness proof. This is stronger than producing one height-two language and logically different from height-one collapse.

## 1. Proof scenarios

### P1. Universal normalization to height one

**Shape.** Define a semantics-preserving normalization that transforms an arbitrary generalized regular expression into one in which no star occurs under another star.

**Promising mechanisms.** Derivatives, systems of language equations, factorization forests, Boolean algebra of quotients, unambiguous transductions, or a fixed-point elimination theorem.

**Key danger.** The normalization silently pushes complement through star or assumes a distributivity law that fails for language concatenation.

**Minimum workshop artifact.** A theorem for one nontrivial syntactic fragment, with a counterexample suite for every rewrite rule and a Lean semantics proof.

**Global success criterion.** A terminating measure and a semantics proof for all constructors.

### P2. Algebraic induction on finite syntactic monoids

**Shape.** Prove height one by induction through a decomposition theorem for finite monoids, using known base cases and certificate-preserving closure operations.

**Variants.** Krohn-Rhodes decomposition, local divisors, Rees matrix structure, Mal'cev/wreath products, or induction on Green's relations.

**Key danger.** The decomposition uses an operation that does not preserve the height-one class, or the proof handles recognition by factors but not the exact language.

**Minimum workshop artifact.** A formally stated preservation theorem for one algebraic construction, with a certificate transformer.

**Global success criterion.** The closure theorem covers all finite syntactic monoids.

### P3. Finite-group ladder to a new non-solvable family

**Shape.** Extend Pin-Straubing-Thérien from abelian, nilpotent-class-2, and `A ⋊ C_2` families to `A_4`, `Dic_3`, `A_5`, or a broader class.

**Key danger.** Solving languages recognized by `A_5` is presented as solving the global problem. It is a major milestone but not a global reduction.

**Minimum workshop artifact.** One explicit theorem such as `HeightOneForGroup A4`, with its recognition quantifiers and closure dependencies fully stated.

**Strong success criterion.** A new closure mechanism that survives passage from solvable to simple groups.

### P4. Cohomological vanishing or gluing theorem

**Shape.** Attach a cohomology class to recognition data. Prove that all height-one certificates have vanishing class, or that local height-one certificates glue when a specified class vanishes.

**Key danger.** Group cohomology is invoked without defining a coefficient module or a map from words/paths to cocycles. A spectral sequence alone does not produce a language expression.

**Minimum workshop artifact.** A worked finite example where the proposed class is computed from an automaton and shown to control a concrete factorization or certificate.

**Global success criterion.** A closure calculus under union, complement, concatenation, and one-level star.

### P5. Game or profinite identity characterization

**Shape.** Characterize height-one languages by a game, topology, or family of identities. Then prove every regular language satisfies it.

**Key danger.** The characterization is only one-way or has a resource parameter that grows with the language.

**Minimum workshop artifact.** A soundness theorem for the invariant and exact evaluation on known height-one families.

**Global success criterion.** Completeness plus a proof that all finite syntactic monoids satisfy the criterion.

### P6. Certificate-generating algorithm

**Shape.** Given a DFA, synthesize a height-one expression and verify it by automata equivalence.

**Key danger.** The synthesis always terminates on tested inputs but no global termination proof exists; expression size grows without a bound.

**Minimum workshop artifact.** A proof-producing solver for a bounded family, with a small trusted checker.

**Global success criterion.** Termination and completeness for arbitrary finite DFAs.

## 2. Disproof scenarios

### D1. `A_5` group-language counterexample

**Shape.** Choose a generating alphabet, a surjective morphism `A* -> A_5`, and an accepting subset. Prove the resulting language is not height one.

**Why attractive.** `A_5` is finite, concrete, non-solvable, and already represented in mathlib.

**Why difficult.** Candidate generation is easy; a universal lower bound against all height-one expressions is the unresolved part.

**Required lower-bound artifact.** A game, identity, cohomological obstruction, or other invariant with a formal closure theorem.

### D2. Smaller monoid counterexample

**Shape.** Enumerate small transformation monoids or syntactic monoids and prioritize candidates outside all known height-one pseudovarieties.

**Key danger.** “Not covered by known theorems” is mistaken for “height greater than one.”

**Useful output even on failure.** A database of minimal monoids, known upper-bound certificates, and equivalence classes under division/duality.

### D3. Infinite hierarchy from an operation

**Shape.** Find an operation `T` that provably raises generalized star-height and iterate it.

**Key danger.** Height is minimized over all equivalent expressions; a syntactically nested construction does not prove a semantic lower bound.

**Minimum artifact.** An invariant whose value strictly increases under `T` and is bounded by height.

### D4. Topological/profinite separation

**Shape.** Show that height-one languages form a proper closed class described by profinite equations or a topology, then exhibit a regular language outside it.

**Key danger.** Closure is established only under Boolean operations and quotients, not concatenation or star.

### D5. Cohomological obstruction

**Shape.** Define a nonzero class for a candidate language and prove all height-one languages have zero class.

**Key danger.** The invariant depends only on the recognizing group and would therefore label known height-one group languages incorrectly.

**Sanity check.** It must vanish on abelian, class-2 nilpotent, and `A ⋊ C_2` examples already covered by published theorems.

## 3. Valuable partial-success scenarios

### S1. Resolve the order-12 barrier

Prove height one for `A_4`, `Dic_3`, or both. This is a coherent publication-scale result and a strong test of AI-assisted proof development.

### S2. Formalize Pin-Straubing-Thérien base cases

A Lean library for generalized expressions, recognition, syntactic monoids, star-free languages, counting languages, and the published closure operations would be reusable even without a new theorem.

### S3. Formalize the failed `C_3` route

Turn Bourne's unique-factorization obstruction into a precise counterexample to a proposed lemma. This prevents repeated wasted search and may expose the exact missing structure.

### S4. Build a verified certificate checker

A small kernel that accepts a generalized expression plus DFA equivalence certificate and proves a height bound is a meaningful tool. It separates untrusted synthesis from trusted verification.

### S5. Exhaust a bounded search space rigorously

Examples:

- every language recognized by a fixed group and a fixed generating alphabet has a height-one expression below an explicit size bound;
- every DFA up to `n` states in a normalized class is solved by the certificate generator;
- every proposed obstruction in a finite list fails on a known height-one language.

State bounds exactly. Do not extrapolate.

### S6. Identify a new obstruction to a proof architecture

A theorem showing that a broad family of “count only fixed-length non-overlapping factors” methods cannot handle a specified group is negative methodological progress, not failure.

### S7. Produce a formal cross-disciplinary dictionary

The three textbooks, glossary, theorem dependency graph, and stabilized Lean definitions may be the realistic output of a short conference. This is success if claims are accurate and future work becomes cheaper.

## 4. Mathematical failure modes

### M1. Restricted/generalized confusion

Symptoms: Eggan's theorem or ordinary regex lower bounds are cited as generalized lower bounds; complement is omitted from the syntax; a proof counts syntactic star nesting without minimizing over equivalent expressions.

Mitigation: every theorem statement includes `restricted` or `generalized`; CI grep rejects unqualified “star height” in designated source files unless the file header fixes the convention.

### M2. Recognition/syntactic-monoid confusion

Symptoms: a language recognized by `G` is assumed to have syntactic monoid `G`; a property is transferred in the wrong direction under division.

Mitigation: write the recognizing morphism and accepting subset explicitly. Use a separate predicate for syntactic monoid.

### M3. Complement universe mismatch

Symptoms: complement is taken relative to all lists over an ambient type rather than the selected finite alphabet; alphabet-changing morphisms invalidate complement equations.

Mitigation: parameterize languages by the alphabet type and record finiteness/nonemptiness hypotheses at interfaces.

### M4. Empty-word edge case

Symptoms: semigroup-language results over `A+` are imported into monoid languages over `A*` without handling `ε`.

Mitigation: maintain separate `A+` and `A*` lemmas or explicitly add/remove `{ε}` with a height-zero operation.

### M5. Nonunique parsing

Symptoms: a word is claimed to factor uniquely into counted blocks, but overlaps or infinite component languages create multiple parses.

Mitigation: require an unambiguity theorem or use automaton states that certify the parse. Test against Bourne's `C_3` obstruction.

### M6. Local-to-global gap

Symptoms: all subgroup restrictions have height one, so the whole `A_5` language is declared height one.

Mitigation: state the gluing theorem as a separate obligation. Compute overlap compatibility or an obstruction class.

### M7. Lower-bound invariant not closed under all constructors

Symptoms: an invariant is preserved by Boolean operations but not concatenation; or by concatenation but not a one-level star.

Mitigation: a candidate invariant is not promoted until its closure matrix is complete.

### M8. Computational upper bound treated as minimality

Symptoms: a synthesized height-one expression proves height exactly one without checking star-freeness; failure to synthesize proves height at least two.

Mitigation: separate `upper_bound`, `star_free_test`, and `lower_bound` fields in every experiment record.

### M9. Circular structural lemma

Symptoms: a reduction ends at a statement equivalent to height-one collapse and is called “almost complete.”

Mitigation: adversarial referee checks theorem strength and known equivalences before assigning progress credit.

## 5. Technical failure modes

### T1. Lean API drift

Symptoms: imports or declaration names changed; agents spend the workshop repairing unrelated version differences.

Mitigation: pin Lean/mathlib; cache dependencies before the event; assign one API scout; forbid simultaneous version upgrades.

### T2. Quotient types too early

Symptoms: the team becomes blocked on setoid/quotient monoid instances before semantics or congruence lemmas are stable.

Mitigation: prove all list-context congruence lemmas first; keep a relation-level interface; instantiate the quotient only after tests pass.

### T3. Giant foundational import

Symptoms: every file imports `Mathlib`, builds are slow, and hidden dependencies proliferate.

Mitigation: allow `Mathlib` during the first day, then run import minimization after APIs stabilize.

### T4. Untrusted certificate format

Symptoms: a Python/SAT solver outputs a regex that is accepted by convention rather than checked.

Mitigation: use a parser, AST, height computation, and DFA-equivalence checker with a soundness theorem.

### T5. Nonreproducible search

Symptoms: no seed, no exact model prompt, no commit hash, no resource limit, or no candidate archive.

Mitigation: each run gets a manifest with prompt hash, branch, tool versions, start/end time, random seed, and output paths.

### T6. Context rot and prompt drift

Symptoms: long agents forget the exact theorem, conflate `A_4` with `A_5`, or silently relax acceptance criteria.

Mitigation: short `AGENTS.md`; task-local context packs; checkpoint summaries; restart from artifacts rather than extending a polluted chat.

### T7. Parallel write conflicts

Symptoms: agents edit the same Lean core definitions, merge semantics diverge, and proof terms no longer typecheck.

Mitigation: parallelize exploration; serialize core-definition changes; use worktrees and an integration agent.

### T8. Budget exhaustion before verification

Symptoms: most tokens are spent generating a long proof; no budget remains for tests and adversarial repair.

Mitigation: reserve at least 30% of the run budget for checking. Stop generation when the reserve is reached.

### T9. “Sorry” becomes invisible debt

Symptoms: a formalized theorem is advertised although the decisive lemma remains `sorry`.

Mitigation: CI scans proof holes; every hole has an ID, owner, dependency, and status in `PROOF_OBLIGATIONS.md`.

## 6. Sociological failure modes

### H1. AI prestige overwhelms mathematical caution

A dramatic agent output receives more attention than a quiet objection. Mitigation: anonymous or role-separated adversarial review; claims advance by evidence, not source prestige.

### H2. Lean experts become a service desk

Formalizers are asked to encode unstable mathematics after decisions are made elsewhere. Mitigation: Lean experts participate in theorem design and may reject statements with poor interfaces.

### H3. Domain hierarchy suppresses questions

Number theorists may hesitate to ask basic automata questions; formal-language theorists may avoid challenging cohomological language; junior members may not flag gaps. Mitigation: glossary-first sessions, rotating “naive question” role, and explicit permission to stop a proof at any undefined map.

### H4. Credit ambiguity

Prompts, computational searches, mathematical ideas, formalization, and exposition have different contributors. Mitigation: maintain a contribution log from day one; agree on authorship and acknowledgement criteria before a result exists.

### H5. Premature publicity

A candidate result is posted before external review, creating pressure to defend it. Mitigation: publication gate: internal reconstruction, adversarial audit, formal check where applicable, citation audit, then external experts.

### H6. Partial progress is discarded by benchmark-style prompts

The unit-distance and Jacobian prompts use strict binary return contracts to prevent agents from stopping early. Applied literally to a human workshop, this can erase valuable lemmas and demoralize participants. Mitigation: maintain two ledgers—`resolution` and `research value`. Agents may have a binary final contract; humans preserve all verified intermediate results.

### H7. Secrecy blocks reproducibility

Fear of being scooped prevents sharing prompts, negative results, or code. Mitigation: decide in advance which branches are private, when they become shareable, and how timestamps/contributions are recorded.

### H8. Over-orchestration

The group spends more time maintaining dashboards and agents than doing mathematics. Mitigation: one claims ledger, one obligation ledger, one daily synthesis meeting. Add infrastructure only after a concrete failure demands it.

## 7. Scenario-dependent next actions

| Observation | Interpretation | Next action |
|---|---|---|
| A complete height-one expression is found for a new group family | Upper-bound progress | Verify DFA equivalence; isolate reusable closure theorem; Lean-check certificate. |
| An agent finds a candidate `A_5` language with no small expression | Candidate only | Search for an invariant; do not scale enumeration yet. |
| A proposed invariant fails on a known abelian language | Invariant unsound | Archive counterexample; repair closure theorem or terminate route. |
| All local subgroup restrictions are solved | Local data | Focus exclusively on gluing/obstruction, not more local enumeration. |
| Lean quotient work stalls | Technical bottleneck | Return to relation-level lemmas; ask API scout; avoid changing mathematics. |
| `A_4` proof succeeds | Major milestone | Generalize mechanism to `A ⋊ C_3`; then test `A_5` subgroup gluing. |
| Cohomology produces no explicit word/path map | Vocabulary-only route | Mark `BLOCKED`; require a concrete coefficient object before resuming. |
| A lower-bound game is sound but incomplete | Valuable partial result | Test completeness on height zero and known height-one families. |
| The workshop ends with stable definitions and no theorem | Infrastructure success | Publish/open the formalization roadmap and schedule targeted follow-up. |

## 8. Termination and announcement gates

### Stop a route when

- its missing lemma is theorem-strength equivalent to the original problem;
- the same mechanism has failed under three genuinely different formulations;
- no exact acceptance test can be stated;
- evidence contradicts a required closure property;
- the remaining compute/token budget cannot cover one verification cycle.

### Announce a theorem only when

1. the exact theorem statement is frozen;
2. all cited results are checked against primary sources;
3. two people independently reconstruct the central argument;
4. an adversarial checklist tailored to generalized star height is complete;
5. computational artifacts are reproducible;
6. Lean files compile if formalization is claimed;
7. remaining assumptions and `sorry`s are disclosed in the title/abstract, not hidden in appendices.
