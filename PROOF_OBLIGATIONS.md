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
| L-WORD-001 | Compile basic word/language operations and prove elementary membership lemmas. (2026-07-23: definitions moved unchanged from `GSH/Language/Basic.lean` into `GSH/Challenges/GeneralizedStarHeight.lean` §1 during the single-file consolidation.) | none | `lake env lean GSH/Challenges/GeneralizedStarHeight.lean` | OPEN |
| L-REGEX-001 | Compile generalized-expression syntax, semantics, and syntactic height. (2026-07-23: definitions moved unchanged from `GSH/Regex/Generalized.lean` into `GSH/Challenges/GeneralizedStarHeight.lean` §2–§4 during the single-file consolidation.) | L-WORD-001 | `lake env lean GSH/Challenges/GeneralizedStarHeight.lean` | OPEN |
| L-REGEX-002 | Prove semantics of n-ary/sugar constructors used by certificates. | L-REGEX-001 | Lean file plus unit examples | OPEN |
| L-DFA-001 | Compile DFA definition and prove `run_append`. (2026-07-23: moved unchanged from `GSH/Automata/DFA.lean` into `GSH/Recognition.lean` §1.) | L-WORD-001 | `lake env lean GSH/Recognition.lean` | OPEN |
| L-DFA-002 | Define reachable/minimal or equivalence interface without committing to a full minimization library. | L-DFA-001 | theorem signatures reviewed by language lead | OPEN |
| L-REC-001 | Compile monoid recognition structure and inverse-image language. (2026-07-23: moved unchanged from `GSH/Monoid/Recognition.lean` into `GSH/Recognition.lean` §2; the syntactic-congruence and aperiodicity interfaces from `GSH/Monoid/Syntactic.lean` / `GSH/StarFree/Aperiodic.lean` are §3–§4 of the same file, and `HeightOneForMonoid` / `HeightOneForGroup` from `GSH/GroupLanguages/Basic.lean` are §5.) | L-WORD-001 | `lake env lean GSH/Recognition.lean` | OPEN |
| L-SYN-001 | Prove syntactic equivalence is a two-sided congruence. | L-WORD-001 | reflexive/symmetric/transitive and append-compatibility compile | OPEN |
| L-SYN-002 | Construct the syntactic quotient monoid or provide a clean interface to mathlib quotient monoids. | L-SYN-001 | multiplication well-defined; quotient map monoid hom | OPEN |
| L-SF-001 | Define aperiodicity and a theorem interface for Schützenberger. | L-SYN-002 | no false claim that interface is a proof | OPEN |
| L-CERT-001 | Formalize certificate AST and checker soundness boundary. | L-REGEX-001, L-DFA-001 | explicit theorem: checker acceptance implies language equality and height bound | OPEN |
| L-GRP-001 | Compile `HeightOneForGroup` with exact alphabet finiteness and morphism quantifiers. | L-REGEX-001, L-REC-001 | group lead approves statement; Lean compiles | OPEN |
| L-A5-001 | Compile the `A5` abbreviation and expose existing simplicity instance/theorem. (2026-07-23: moved unchanged from `GSH/Groups/A5.lean` into `GSH/Groups.lean`, together with `GSH/Groups/SmallGroups.lean` and the milestone names from `GSH/Blueprint.lean`.) | L-GRP-001 | `lake env lean GSH/Groups.lean` | OPEN |
| L-GSH-CHALLENGE-001 | Prove the generalized star-height-one conjecture recorded in `GSH/Challenges/GeneralizedStarHeight.lean` (ledger row GLOBAL-ONE); until then, preserve the statement as an explicitly open challenge. **Consolidation recorded 2026-07-23:** the complete definition chain (`Word`/`Language` + operations, `GRegex`, `denote`, `starHeight`, `HasHeightAtMost`, `IsRegular`, `HeightOneCollapse`, `GeneralizedHeightOneConjecture`) was moved **unchanged** into the challenge file, which now imports only mathlib and is readable top-to-bottom; the former locations `GSH/Language/Basic.lean`, `GSH/Regex/Generalized.lean` were deleted and all importers repointed; the conjecture definition moved out of `GSH/Blueprint.lean` (that file was removed the same day; the milestone names now live in `GSH/Groups.lean`). The theorem statement `generalized_star_height_conjecture : GeneralizedHeightOneConjecture` is textually and definitionally identical to before. (Same day, earlier — withdrawn approach, kept for the record: a from-scratch self-contained restatement plus a `sorry`-free Lean proof of its equivalence, at every universe, with `∀ (α : Type u) [Fintype α], GSH.HeightOneCollapse α` was drafted and compiled, then withdrawn at maintainer request to avoid duplicate definitions; neither artifact was committed. Withdrawal was a design decision, not a mathematical obstruction.) Expert approval still pending. | L-WORD-001, L-REGEX-001 (same file) | statement approved by a formal-language expert; `lake env lean GSH/Challenges/GeneralizedStarHeight.lean` compiles (passes 2026-07-23, full `lake build` 1451 jobs green; only registered `sorry` warnings) | OPEN |

## Published mathematics reproduction

| ID | Obligation | Acceptance artifact | Status |
|---|---|---|---|
| M-PST-001 | Extract exact closure-theorem hypotheses from Pin–Straubing–Thérien. | theorem statements with page/number and notation map | OPEN |
| M-PST-002 | Reconstruct the commutative-group height-one expression in repository notation. | complete hand proof plus at least two checked finite examples | OPEN |
| M-PST-003 | Reconstruct the `A ⋊ C_2` mechanism and identify every use of order two. | dependency graph and formal lemma signatures | OPEN |
| M-BR-001 | Encode one exact-count and one modular-count expression from Bourne–Ruškuc. | JSON certificates accepted by checker | OPEN |
| M-C3-FAIL-001 | Produce the smallest explicit ambiguity/counterexample to the attempted `C_3` unique factorization. | words, factors, and independent verification | OPEN |
| M-WEIS-001 | Audit the exact definitions of Weis's four candidate languages (esp. L2) against Weis 2011 (UMass thesis, "Expressiveness and Succinctness of First-Order Logic on Finite Words"), incl. the "order-48 group" attribution and Weis's own height-one proofs. | definition transcript with page/theorem numbers; syntactic monoid recomputed from the audited definition; comparison with the stage-2 family theorem (RESULTS.md §5.9) | BLOCKED |

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
| N-L2-M3-001 | height ≤ 1 for stage-3 (phases mod 3) staged `ba*b` pair counts. | a certified height-1 feature reaching `T2 mod 2`: single-run-covering prefix codes are integrality-locked to the `(2·T1+T2) mod 3` combination, and the `(T1+T2)`-type combination needs the token `a`, which prefix-collides with the filler `aaa` | candidate feature suites judged exactly by `python3 scripts/weis_l2_family.py --m3` (currently: all stage-3 pair atoms NOT a function of LC/flags/flat code counts incl. cascade `Z3`/W atoms mod 6) | OPEN |

**Blocker for N-COH-001:** no coefficient object or exact map has yet been selected. Invoking an LHS spectral sequence before closing this gap is out of scope.

**Blocker for M-WEIS-001:** the primary source is unreachable from the 2026-07-22 session environment — the network policy denies scholarworks.umass.edu, arxiv.org, irif.fr, people.cs.umass.edu, and web.archive.org (only search-engine snippets were available; see notes/weis_l2_stage2_height1.md §6). Needs a human with library access. Secondary evidence (2009 UMass theory-seminar abstract, ledger row WEIS-TALK-01): Weis showed all four of his candidate languages have generalized star height one.

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

### 2026-07-22 / GSH/Monoid/Recognition.lean / Recognition
- toolchain and commit: leanprover/lean4:v4.32.0, mathlib v4.32.0; no git commit (repository not yet under version control)
- exact error: `Recognition.lean:18:13: failed to synthesize instance of type class MulOne (List α)`
- expected API: mathlib puts no `MulOneClass` on raw `List α`; the free monoid is `FreeMonoid α`, a definitional synonym for `List α` with `FreeMonoid.ofList : List α ≃ FreeMonoid α` the identity equivalence (`Mathlib.Algebra.FreeMonoid.Basic`)
- repair attempted: field retyped `List α →* M` → `FreeMonoid α →* M`; `language` and `mem_language_iff` now apply the morphism through `FreeMonoid.ofList`; added import
- semantic statement changed? yes at type level only: the original field did not elaborate; the repaired type is the intended "monoid morphism from the free monoid of words", and `ofList` is the identity equivalence, so recognized languages are unchanged
- status: compiles; follow-up sorry warnings previously reported at 26:4/29:16/29:2 were error-recovery artifacts and are gone
- note: downstream users must write `R.morphism (FreeMonoid.ofList w)`; consider a `Word`-level wrapper when stabilizing L-REC-001

### 2026-07-22 / GSH/Monoid/Syntactic.lean / syntacticMonoidInst
- toolchain and commit: as above
- exact error: `Syntactic.lean:70:4: Unknown identifier Monoid` (autoImplicit off)
- expected API: `Monoid` lives in `Mathlib.Algebra.Group.Defs`; `GSH.Language.Basic` only imports `Data.Set.Lattice` and `Data.List.Basic`
- repair attempted: added `import Mathlib.Algebra.Group.Defs`
- semantic statement changed? no
- status: compiles; registered `sorry` (L-SYN-002) unchanged

### 2026-07-22 / GSH/Certificates/RegexCertificate.lean / checker_sound
- toolchain and commit: as above
- exact error: `RegexCertificate.lean:39:5: Unknown identifier Fintype`
- expected API: `Mathlib.Data.Fintype.Basic`
- repair attempted: added the import
- semantic statement changed? no
- status: compiles

### 2026-07-22 / GSH/GroupLanguages/Basic.lean / HeightOneForMonoid, HeightOneForGroup
- toolchain and commit: as above
- exact error: (1) `Basic.lean:16:18: Unknown identifier Fintype`; (2) after the import fix, `Basic.lean:20:0: declaration HeightOneForGroup contains universe level metavariables (HeightOneForMonoid.{?u.6, v})`
- expected API: `Mathlib.Data.Fintype.Basic`; the alphabet universe `u` quantified inside `HeightOneForMonoid` must be bound explicitly in any definition that mentions it
- repair attempted: added the import; `HeightOneForGroup` now reads `HeightOneForMonoid.{u, v} G`
- semantic statement changed? no: `u` was already a universe parameter of the original declaration block; it is now named explicitly instead of being silently unbound
- status: compiles

### 2026-07-22 / GSH/Groups/SmallGroups.lean, GSH/Groups/A5.lean, GSH/Blueprint.lean / A4HeightOneTarget, A5HeightOneTarget, SmallGroupMilestone, A5Milestone
- toolchain and commit: as above
- exact error: `declaration contains universe level metavariables` at each use of `HeightOneForGroup`/the target props
- expected API: same universe-binding discipline as above
- repair attempted: each target prop declares `universe u` and instantiates `.{u}` explicitly
- semantic statement changed? no (same quantification, universe parameter made explicit)
- status: compiles

### 2026-07-22 / GSH/Groups/A5.lean / a5_isSimple
- toolchain and commit: as above
- exact error: `Tactic decide failed for proposition 5 ≤ Nat.card (Fin 5)` (`Nat.card` is classically defined and does not reduce)
- expected API: `alternatingGroup.isSimpleGroup (hα : 5 ≤ Nat.card α)`; mathlib's own deprecated `Fin 5` instances discharge the bound with `simp` (`Nat.card_fin`)
- repair attempted: `(by decide)` → `(by simp)`
- semantic statement changed? no
- status: compiles

**First-build result (2026-07-22, macOS/darwin, lean4 v4.32.0 + mathlib v4.32.0):** after the repairs above, `./scripts/check.sh` passes end to end: full `lake build` (1446 jobs), smoke file, 5 Python unit tests, 2 certificate checks, claims lint (19 rows), proof-hole lint (exactly the 2 registered placeholders L-SYN-002 / Aperiodic). L-WORD-001, L-REGEX-001, L-DFA-001, L-REC-001, L-A5-001 acceptance commands now succeed; semantic review is still pending before closing them.
