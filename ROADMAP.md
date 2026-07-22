# Roadmap: From Conference Theme to Auditable Research Program

This roadmap separates what can be finished during a short workshop from what would constitute a publishable mathematical result. Dates are relative to the first group-work session.

## North-star target

The global structural conjecture is:

> Every regular language has generalized star-height at most one.

The repository does not pretend that a workshop can schedule a solution. It schedules progressively stronger, independently useful milestones whose verification cost is known in advance.

## Success levels

| Level | Deliverable | Resolution value | Verification gate |
|---|---|---:|---|
| L0 | Reproducible repository and corrected survey | infrastructure | clean bootstrap, source audit |
| L1 | Lean definitions and executable certificate checker | infrastructure | build/tests and reviewer reconstruction |
| L2 | Reproduction of one published height-one construction | formalized prior work | source-by-source comparison |
| L3 | New lemma repairing a documented failure | publishable partial result | adversarial examples and independent proof |
| L4 | `A_4` or `Dic_3` height-one theorem | major structural result | complete proof, formal/certificate check, external review |
| L5 | `A_5` height-one theorem | major non-solvable test case | same as L4, plus subgroup/gluing audit |
| L6 | explicit language of height greater than one | disproof of collapse | rigorous lower-bound invariant, not bounded search |
| L7 | global height-one theorem | proof of collapse | full proof and independent formal reconstruction |
| L8 | exact decision algorithm | full decision problem | correctness and termination proof |

## Pre-conference: one organizer, 90 minutes

1. Run `./scripts/bootstrap.sh` and `./scripts/check.sh` on a machine with Lean and network access.
2. Record all API failures in `PROOF_OBLIGATIONS.md`; do not repair them silently in chat.
3. Print or share the three role primers and the one-page target statement from the blueprint.
4. Create names for five roles: formal-language lead, group/cohomology lead, Lean lead, computational lead, independent referee.
5. Freeze one conference target. Recommended default: reproduce the `A \rtimes C_2` mechanism and isolate the precise `C_3` failure in both mathematics and code.
6. Reserve at least 30% of available model budget for checking and synthesis.

## Workshop day 1

### Session 1: common language (60 minutes)

- Formal-language lead gives definitions: generalized expression, semantic height, recognition, syntactic monoid.
- Group lead explains the finite-group ladder: abelian, nilpotent class two, `A \rtimes C_2`, then the order-12 barrier.
- Lean lead maps each noun to a proposed type or theorem interface.
- Referee writes a list of ambiguous quantifiers and forbidden conflations.

**Exit artifact:** a frozen theorem statement in `PROOF_OBLIGATIONS.md`, with explicit alphabet, morphism, accepting set, and intended height bound.

### Session 2: independent route generation (90 minutes)

Run small independent groups without cross-pollination:

1. Pin-style count/substitution route.
2. Canonical parsing or unambiguous-transduction repair.
3. Pseudovariety/factorization route.
4. Lower-bound invariant route.
5. `A_5` subgroup/cohomology exploratory route.

Each group must return one of: a proved lemma, an explicit counterexample to a lemma, a finite certificate, or a sharply stated blocker.

**Exit artifact:** one approach-registry entry per mathematical mechanism.

### Session 3: triage and executable checks (90 minutes)

- Merge duplicate mechanisms.
- Run all explicit expressions through `scripts/check_certificate.py`.
- Translate the strongest central lemma into a Lean theorem signature, even if the proof remains `sorry`.
- Referee tests empty-word, complement-universe, and nonunique-factorization edge cases.

**Exit artifact:** a ranked route list with verification cost estimates.

### Session 4: select one route (60 minutes)

Selection rule:

```text
expected mathematical leverage
× availability of an independent check
÷ central unproved assumptions
```

Do not choose by rhetorical attractiveness or by the seniority of the proposer.

## Workshop day 2

### Proof route

- Decompose the selected claim into named lemmas.
- Assign one prover and one breaker to every central lemma.
- Keep the Lean statement synchronized with the informal statement.
- Require examples and nonexamples before abstraction.

### Disproof route

- Freeze an explicit regular language and minimal DFA.
- Separate candidate generation from lower-bound proof.
- State the proposed invariant and prove its closure under each height-one constructor.
- Test the invariant against known height-one languages before applying it to the candidate.

### Formalization route

- Stabilize word/language and generalized-expression semantics.
- Prove `DFA.run_append` and language-operation lemmas.
- Formalize certificate soundness before importing large generated certificates.
- Delay quotient monoids until the underlying congruence lemmas are clean.

**Day-2 exit artifact:** either a verified new lemma, a verified obstruction, or a minimal formal kernel plus a precise research blocker. “Promising discussion” is not an exit artifact.

## First 48 hours after the conference

1. Lock the conference branch; no retrospective rewriting of failed experiments.
2. Independent referee reconstructs the strongest claim from the statement and cited lemmas.
3. Run source audit: every historical theorem gets theorem/page/DOI metadata.
4. Run proof-hole and claim-ledger checks.
5. Publish an internal report distinguishing `VERIFIED`, `REFUTED`, `BLOCKED`, and `UNREVIEWED` artifacts.
6. Decide whether the result is suitable for public release, continued private work, or archival as a failed route.

## Twelve-week research program

### Weeks 1–2: foundations

- Compile and stabilize all Lean foundation files.
- Validate Python certificate checker against hand examples.
- Reproduce star-free/aperiodic interfaces without overformalizing the full theorem initially.
- Produce a theorem dependency graph for Pin-Straubing-Thérien closure operations.

### Weeks 3–4: published certificate reproduction

- Encode exact and modular factor-count examples from Bourne–Ruškuc.
- Verify regex/DFA equivalence computationally.
- Formalize one closure transport theorem.
- Document every mismatch between paper notation and the repository model.

### Weeks 5–6: order-12 barrier

- Implement `A_4` and `Dic_3` group-recognition examples.
- Reconstruct Bourne's failed `C_3` argument and generate smallest counterexamples to unique parsing.
- Test replacement mechanisms: marked parsing, bounded-overlap inclusion–exclusion, and unambiguous transductions.

### Weeks 7–8: theorem or obstruction

- Select the strongest replacement mechanism.
- Prove its soundness on a nontrivial family or prove a no-go theorem for the specified normal form.
- Begin Lean formalization of the central lemma, not just supporting definitions.

### Weeks 9–10: `A_5` matrix

- Enumerate subgroup restrictions and coset actions.
- Record which restricted languages are already covered by known group families.
- Define one concrete coefficient module and one exact word-to-cochain map, or close the cohomology route as underspecified.

### Weeks 11–12: synthesis and external review

- Produce a preprint-quality informal proof or obstruction report.
- Remove all undeclared proof holes.
- Obtain one formal-language and one finite-group review from people not involved in the route.
- Release code and certificate data with exact toolchain versions.

## Decision points

### Continue a mathematical route when

- it has a central lemma strictly weaker than the global conjecture;
- the lemma has independently testable consequences;
- failures produce new counterexamples rather than repeated syntax repair;
- proof and disproof agents disagree on a concrete statement that can be settled.

### Stop or redirect when

- the “missing lemma” restates height-one collapse in new language;
- a cohomological object has no explicit map from words or recognizing morphisms;
- bounded search is being interpreted as a lower bound;
- the formalization is consuming time on general library design unrelated to the frozen theorem;
- all routes depend on the same unverified unique-factorization claim.

## Release checklist

A public mathematical claim requires all of:

- exact theorem statement and scope;
- complete source and dependency audit;
- independent reconstruction;
- adversarial edge-case review;
- deterministic code/certificate reproduction when computation is used;
- clean Lean build for any claim advertised as formalized;
- explicit list of axioms and classical principles;
- authorship and contribution record agreed before announcement.
