# Suggestions for Conducting the Project

This document is written for mathematicians who may not be familiar with agentic AI. The objective is not to make the workshop “AI-first.” It is to make every AI-assisted step mathematically inspectable, budget-aware, and reversible.

## 1. Use AI in four roles, not one

### Scout

Searches literature, mathlib APIs, examples, and counterexamples to proposed lemmas. A scout should return locations and exact statements, not a narrative survey unless asked.

### Builder

Writes a small artifact: a Lean definition, a certificate checker, a worked example, a proof skeleton, or a conversion script.

### Explorer

Runs a bounded portfolio of proof and disproof routes. Explorers are allowed to fail, but must state the exact obstruction and preserve concrete intermediate lemmas.

### Referee

Tries to break a proposed result using a domain-specific checklist. The referee should not have authored the proof and should initially be shielded from the preferred interpretation.

Do not ask one long-running agent to be all four. The same model that invented an argument is poorly positioned to notice its own hidden assumption.

## 2. Start with a completion contract

The most useful feature of the public unit-distance and Jacobian prompts is not their length. It is their exact definition of completion.

For this project, every task prompt should include:

1. **Objects and notation.** Alphabet, language model, complement universe, recognition morphism, and height convention.
2. **One frozen target.** A theorem, counterexample, API repair, or certificate—not “make progress.”
3. **Proof/disproof symmetry where appropriate.** State what would count on either side.
4. **Nonexamples.** List tempting outputs that do not satisfy the target.
5. **Concrete return artifacts.** Exact files, theorem names, expressions, equations, test logs, or counterexamples to sublemmas.
6. **Verification route.** The command or mathematical check the agent can run.
7. **Stop conditions.** When to mark a route blocked instead of spending the remaining budget.

A good task is: “Prove the `run_append` lemma for `DFA.run`, add two tests, and make `lake env lean GSH/Recognition.lean` pass.” A bad task is: “Formalize automata theory.”

## 3. Keep the human workshop and the search benchmark distinct

Strict prompts such as “partial progress does not count” can be useful for preventing an autonomous search agent from returning after an elegant reduction. They are not a sensible rule for valuing human research.

Maintain two ledgers:

- **Resolution ledger:** does the artifact prove/disprove the frozen target?
- **Research-value ledger:** new lemma, counterexample to a sublemma, failed mechanism, reusable code, corrected citation, formal interface, or negative computational result.

This preserves useful work without letting a partial result masquerade as a solution.

## 4. Use the simplest orchestration that works

Anthropic's engineering guidance recommends simple, composable patterns and increasing complexity only when needed. Their Claude Code guidance also emphasizes giving an agent an executable check, exploring before planning and coding, and managing context aggressively. OpenAI's Codex documentation similarly recommends small persistent `AGENTS.md` instructions, tests and linters as enforcement, subagents for bounded independent work, and worktrees for parallel edits.

For the conference, use this ladder:

1. one carefully specified agent call;
2. one call plus an independent referee;
3. two or three independent agents on genuinely different approaches;
4. a root/orchestrator agent only when the task registry is already clear;
5. large multiagent search only for a target with cheap verification and enough remaining budget.

Do not begin with 64 agents merely because a public prompt did. Parallel agents multiply token use and coordination overhead.

## 5. Prepare a long run before launching it

The user has limited weekly Codex budget. Treat the final 10% as verification capital, not as more brainstorming.

### Long-run launch packet

Before launching, create a directory containing:

- `TASK.md`: exact target and completion contract;
- `CONTEXT.md`: only the definitions and lemmas needed;
- `SOURCES.md`: primary references with page/theorem numbers;
- `ACCEPTANCE.md`: pass/fail checks;
- `KNOWN_FAILURES.md`: routes not to repeat without a new mechanism;
- `RETURN_SCHEMA.md`: required summary fields;
- `manifest.json`: prompt hash, commit hash, model/tool settings, time limit, and budget reserve.

### Budget partition

A reasonable default for one expensive run:

- 15%: source/API reconnaissance;
- 20%: independent approach generation;
- 30%: one selected implementation/proof route;
- 20%: adversarial checking and repair;
- 15%: integration, tests, and concise reporting.

Do not allow generation to consume the verification reserve. If the selected route has not produced a testable central lemma by 65% of budget, stop and return the best obstruction.

### Checkpoint policy

Every 20–40 minutes or after a major theorem/API transition, the agent writes:

```text
Frozen target:
Current strongest artifact:
What has been verified:
Largest remaining gap:
New assumptions introduced:
Budget remaining:
Continue / redirect / stop:
```

A new session should restart from these artifacts, not from an enormous transcript.

## 6. Preserve early independence

The public Jacobian prompt explicitly keeps several incompatible routes alive and delays cross-pollination. The reason is practical: once every agent sees a favored idea, they tend to reproduce its blind spots.

For the first search wave:

- assign one agent to Pin-style counting and substitutions;
- one to factorization forests/unambiguous parsing;
- one to pseudovarieties/profinite identities;
- one to `A_4/Dic_3` finite-group decomposition;
- one to `A_5` subgroup/representation structure;
- one to lower-bound games or invariants;
- one adversarial agent to search for false lemmas.

Each returns a concrete lemma, construction, or obstruction. Only then should the root agent synthesize.

## 7. Keep an approach registry by mathematical mechanism

Do not create entries such as “Agent 1,” “Agent 2,” or “cohomology idea.” Use entries such as:

```text
ID: P-C3-UNAMBIGUOUS-TRANSDUCTION
Target: replace Bourne's failed unique factorization
Mechanism: finite-state canonical parsing
Strongest lemma: ...
Counterexample suite: ...
Status: ACTIVE / BLOCKED / REFUTED / VERIFIED
Blocker: ...
Resumption condition: ...
```

Two agents using different vocabulary but the same missing factorization lemma belong to one approach family. This prevents the illusion of diversity.

## 8. Demand artifacts, not confidence

Useful returns include:

- a generalized expression and a DFA-equivalence certificate;
- an exact morphism `A* -> G` and accepting subset;
- a theorem statement with all quantifiers;
- a cocycle formula and a proof it is a cocycle;
- a counterexample word to a factorization lemma;
- a Lean file that compiles;
- a minimal failing test and API diagnosis;
- a source quotation with theorem/page number.

Not useful:

- “promising avenue” without a next lemma;
- “standard argument applies” without the map it applies to;
- a 20-page proof with no statement-level dependency graph;
- a candidate counterexample supported only numerically;
- a status report that cannot be checked.

## 9. Verification should be layered

### Layer 1: executable local check

Lean build, unit test, DFA equivalence, exact determinant, finite enumeration, or a small symbolic identity.

### Layer 2: domain-specific adversarial checklist

For generalized star height:

- generalized versus restricted;
- minimum over equivalent expressions;
- complement relative to the correct alphabet;
- `A*` versus `A+` and the empty word;
- recognition versus syntactic monoid;
- closure under every constructor used;
- unique/unambiguous factorization;
- direction of inverse morphisms and divisions;
- local-to-global gluing;
- no lower bound inferred from bounded search.

### Layer 3: independent reconstruction

A mathematician or separate agent reconstructs the central argument from the theorem statement and cited lemmas, without reading the original prose line by line.

### Layer 4: formal or certificate verification

Lean proof or a small trusted checker. Formalization should expose assumptions; it should not be used as a decorative final step.

### Layer 5: external expert review

The OpenAI unit-distance report describes automated output followed by AI grading, internal human examination, and external specialists. The important lesson is the sequence of increasingly independent checks—not the claim that AI grading is sufficient.

## 10. Lean should shape theorem design from the beginning

Lean experts should attend mathematical decomposition meetings. They can identify:

- a theorem stated at the wrong abstraction level;
- hidden choice or finiteness assumptions;
- quotient constructions that should be delayed;
- an explicit certificate that is easier to verify than an existential proof;
- a computational sublemma that can be reflected;
- library components already present in mathlib.

A healthy workflow is:

1. informal theorem with exact quantifiers;
2. Lean interface with placeholders;
3. proof decomposition agreed by all roles;
4. executable base cases;
5. informal proof and formal proof advance together.

Do not hand the Lean team a polished 30-page proof after the conference and ask them to “translate it.”

## 11. Separate untrusted synthesis from trusted checking

For expression search, use this architecture:

```text
untrusted generator (AI / SAT / search)
        |
        v
JSON certificate: alphabet, regex AST, claimed height, DFA
        |
        v
small checker
  - parses AST
  - computes height
  - compiles expression to automaton
  - checks language equivalence
        |
        v
Lean soundness theorem / independently audited checker
```

This permits aggressive experimentation without putting the research claim inside a model's prose.

## 12. Assign roles explicitly during group work

A six-person cell can use:

- **problem owner:** freezes the statement and decides scope;
- **source auditor:** checks every cited theorem;
- **proof explorer:** develops one mechanism;
- **counterexample explorer:** attacks lemmas and searches for negative evidence;
- **formalizer:** maintains Lean interfaces and tests;
- **referee/integrator:** controls the ledger and merge gate.

Rotate roles daily. In particular, the same person should not permanently own both the proof narrative and the claims ledger.

## 13. Run short synthesis meetings

Twice daily, no more than 30 minutes:

1. one sentence per active route;
2. strongest verified artifact;
3. exact blocker;
4. whether the route continues, redirects, or stops;
5. new conflicts in definitions or citations;
6. token/compute budget remaining.

Do not read agent transcripts aloud. The transcript is not the artifact.

## 14. Record negative results

A negative-result entry should include:

- precise failed lemma;
- smallest counterexample;
- whether the failure is mathematical, API-related, or resource-related;
- which nearby variants remain possible;
- a test that prevents regression;
- conditions under which the route may be resumed.

This is especially important for the `A ⋊ C_3` unique-factorization route and for speculative cohomological invariants.

## 15. Protect credit and psychological safety

Before serious work begins, agree on:

- authorship criteria for mathematical ideas, computation, Lean, and exposition;
- how AI use will be disclosed;
- whether prompts and transcripts will be published;
- when outside experts are contacted;
- how confidential branches are timestamped;
- how junior participants can anonymously flag a gap.

A workshop that invites cross-disciplinary questions must not treat elementary clarification as low status. Many decisive errors are hidden in “obvious” translations between fields.

## 16. A practical 90-minute preflight

### Minutes 0–15: freeze the target

Choose one: global collapse, `A_4`, `Dic_3`, an explicit `A_5` subgroup calculation, a formalization milestone, or a lower-bound invariant. Do not combine them.

### Minutes 15–30: source packet

Record the exact published theorem, page, hypotheses, and known failed route.

### Minutes 30–45: acceptance tests

Write mathematical and executable checks before prompts.

### Minutes 45–60: independent prompts

Prepare at most three genuinely different approach prompts plus one referee prompt.

### Minutes 60–75: budget and stop rules

Reserve verification budget and define the first checkpoint.

### Minutes 75–90: dry run

Give the prompt to a cheap/fast model or a human participant. Any ambiguity found now is cheaper than ambiguity after an eight-hour run.

## 17. Final checklist before claiming progress

- [ ] The exact language class and alphabet are fixed.
- [ ] “Generalized” appears in every relevant theorem statement.
- [ ] All recognition morphisms and accepting subsets are explicit.
- [ ] Every cited theorem was checked in a primary source.
- [ ] Computational claims include bounds, seed, and code version.
- [ ] A lower-bound claim has a universal invariant, not search failure.
- [ ] The independent referee has not authored the route.
- [ ] Every Lean `sorry` is visible in the obligation ledger.
- [ ] The formal build or certificate checker passes from a clean checkout.
- [ ] The contribution log and AI disclosure are current.
- [ ] The public statement says exactly what was proved—no broader group, monoid, or global conclusion.

## 18. Sources on agent practice and recent prompt design

Official and primary sources used in preparing these suggestions:

- Anthropic, “Building effective agents”: https://www.anthropic.com/engineering/building-effective-agents
- Anthropic, “Best practices for Claude Code”: https://code.claude.com/docs/en/best-practices
- Anthropic, “Create custom subagents”: https://code.claude.com/docs/en/sub-agents
- OpenAI, “Custom instructions with AGENTS.md”: https://learn.chatgpt.com/docs/agent-configuration/agents-md
- OpenAI, “Subagents”: https://learn.chatgpt.com/docs/agent-configuration/subagents
- OpenAI, “Codex-maxxing for long-running work”: https://openai.com/index/codex-maxxing-long-running-work/
- OpenAI unit-distance proof and original prompt: https://cdn.openai.com/pdf/74c24085-19b0-4534-9c90-465b8e29ad73/unit-distance-proof.pdf
- Public Jacobian prompt shared by Aaron Lou: https://aaronlou.com/jacobian_counterexample_prompt.pdf
- Reproducible derivation accompanying that prompt: https://aaronlou.com/jacobian_counterexample_derivation.pdf
