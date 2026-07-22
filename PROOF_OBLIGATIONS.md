# Proof Obligations and Formalization Queue

An entry is closed only when its acceptance test passes and the corresponding claim-ledger row is updated. A `sorry` may exist during scaffolding, but it must be named here.

## Status vocabulary

- `OPEN`: well specified, unassigned or incomplete.
- `ACTIVE`: assigned and under work.
- `BLOCKED`: exact obstruction recorded.
- `REVIEW`: implementation/proof exists; independent review pending.
- `CLOSED`: acceptance test and review completed.

## Lean foundation

| ID | Obligation | Depends on | Acceptance test | Status |
|---|---|---|---|---|
| L-WORD-001 | Compile basic word/language operations and prove elementary membership lemmas. | none | `lake env lean GSH/Language/Basic.lean` | OPEN |
| L-REGEX-001 | Compile generalized-expression syntax, semantics, and syntactic height. | L-WORD-001 | `lake env lean GSH/Regex/Generalized.lean` | OPEN |
| L-REGEX-002 | Prove semantics of n-ary/sugar constructors used by certificates. | L-REGEX-001 | Lean file plus unit examples | OPEN |
| L-DFA-001 | Compile DFA definition and prove `run_append`. | L-WORD-001 | `lake env lean GSH/Automata/DFA.lean` | OPEN |
| L-DFA-002 | Define reachable/minimal or equivalence interface without committing to a full minimization library. | L-DFA-001 | theorem signatures reviewed by language lead | OPEN |
| L-REC-001 | Compile monoid recognition structure and inverse-image language. | L-WORD-001 | `lake env lean GSH/Monoid/Recognition.lean` | OPEN |
| L-SYN-001 | Prove syntactic equivalence is a two-sided congruence. | L-WORD-001 | reflexive/symmetric/transitive and append-compatibility compile | OPEN |
| L-SYN-002 | Construct the syntactic quotient monoid or provide a clean interface to mathlib quotient monoids. | L-SYN-001 | multiplication well-defined; quotient map monoid hom | OPEN |
| L-SF-001 | Define aperiodicity and a theorem interface for Schützenberger. | L-SYN-002 | no false claim that interface is a proof | OPEN |
| L-CERT-001 | Formalize certificate AST and checker soundness boundary. | L-REGEX-001, L-DFA-001 | explicit theorem: checker acceptance implies language equality and height bound | OPEN |
| L-GRP-001 | Compile `HeightOneForGroup` with exact alphabet finiteness and morphism quantifiers. | L-REGEX-001, L-REC-001 | group lead approves statement; Lean compiles | OPEN |
| L-A5-001 | Compile the `A5` abbreviation and expose existing simplicity instance/theorem. | L-GRP-001 | `lake env lean GSH/Groups/A5.lean` | OPEN |

## Published mathematics reproduction

| ID | Obligation | Acceptance artifact | Status |
|---|---|---|---|
| M-PST-001 | Extract exact closure-theorem hypotheses from Pin–Straubing–Thérien. | theorem statements with page/number and notation map | OPEN |
| M-PST-002 | Reconstruct the commutative-group height-one expression in repository notation. | complete hand proof plus at least two checked finite examples | OPEN |
| M-PST-003 | Reconstruct the `A ⋊ C_2` mechanism and identify every use of order two. | dependency graph and formal lemma signatures | OPEN |
| M-BR-001 | Encode one exact-count and one modular-count expression from Bourne–Ruškuc. | JSON certificates accepted by checker | OPEN |
| M-C3-FAIL-001 | Produce the smallest explicit ambiguity/counterexample to the attempted `C_3` unique factorization. | words, factors, and independent verification | OPEN |

## New theorem routes

| ID | Target | Central missing lemma | Falsification test | Status |
|---|---|---|---|---|
| N-C3-001 | Height one for a specified `A ⋊ C_3` family. | canonical or unambiguous parsing replacing unique factorization | enumerate smallest overlaps and test claimed parser | OPEN |
| N-A4-001 | `HeightOneForGroup A4`. | transport theorem for `(C2 × C2) ⋊ C3` | all recognition morphisms for small generating alphabets; not a proof but a bug finder | OPEN |
| N-DIC3-001 | `HeightOneForGroup Dic3`. | transport through `C3 ⋊ C4` or alternative decomposition | same | OPEN |
| N-A5-001 | local certificates for all selected proper-subgroup restrictions. | precise restriction/gluing calculus | incompatible local accept sets | OPEN |
| N-A5-002 | `HeightOneForGroup A5`. | global gluing theorem not equivalent to target | adversarial subgroup intersections and coset actions | OPEN |
| N-LOWER-001 | sound invariant satisfied by all height-one languages. | closure under union, complement, concatenation, and one-level star | test against broad known height-one suite | OPEN |
| N-COH-001 | concrete cohomological transport lemma. | coefficient module and word/path-to-cocycle map | verify cocycle identity and behavior under language constructors | BLOCKED |

**Blocker for N-COH-001:** no coefficient object or exact map has yet been selected. Invoking an LHS spectral sequence before closing this gap is out of scope.

## First-build repair log

The source was generated without a local Lean installation. On the first real build, append every failure here in this format:

```text
### YYYY-MM-DD / file / declaration
- toolchain and commit:
- exact error:
- expected API:
- repair attempted:
- semantic statement changed? yes/no; if yes, why:
- status:
```
