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
| L-RED-001 | Formalize Proposition 3.1 (full-alphabet reduction) via the two §3.5 lemmas: height-preserving Brzozowski derivative and literal-inverse-morphism substitution for generalized expressions. | L-REGEX-001 | Lean statements compile; lemma proofs discharge without `sorry`; group lead approves the quantifiers | OPEN |
| L-GSH-CHALLENGE-001 | Prove the generalized star-height-one conjecture recorded in `GSH/Challenges/GeneralizedStarHeight.lean` (ledger row GLOBAL-ONE); until then, preserve the statement as an explicitly open challenge. **Consolidation recorded 2026-07-23:** the complete definition chain (`Word`/`Language` + operations, `GRegex`, `denote`, `starHeight`, `HasHeightAtMost`, `IsRegular`, `HeightOneCollapse`, `GeneralizedHeightOneConjecture`) was moved **unchanged** into the challenge file, which now imports only mathlib and is readable top-to-bottom; the former locations `GSH/Language/Basic.lean`, `GSH/Regex/Generalized.lean` were deleted and all importers repointed; the conjecture definition moved out of `GSH/Blueprint.lean` (that file was removed the same day; the milestone names now live in `GSH/Groups.lean`). The theorem statement `generalized_star_height_conjecture : GeneralizedHeightOneConjecture` is textually and definitionally identical to before. (Same day, earlier — withdrawn approach, kept for the record: a from-scratch self-contained restatement plus a `sorry`-free Lean proof of its equivalence, at every universe, with `∀ (α : Type u) [Fintype α], GSH.HeightOneCollapse α` was drafted and compiled, then withdrawn at maintainer request to avoid duplicate definitions; neither artifact was committed. Withdrawal was a design decision, not a mathematical obstruction.) Expert approval still pending. | L-WORD-001, L-REGEX-001 (same file) | statement approved by a formal-language expert; `lake env lean GSH/Challenges/GeneralizedStarHeight.lean` compiles (passes 2026-07-23, full `lake build` 1451 jobs green; only registered `sorry` warnings) | OPEN |

| L-CORE2-EQV-001 | Define the scalar CORE2 statement `∀ A B C D ∈ SF, (A ∪ B D* C)* ∈ GH1` over each finite alphabet and formalize its equivalence with `GeneralizedHeightOneConjecture`, following the external elementary-expansion cut compiler. Keep the result as an equivalence, not a proof of either side. | L-GSH-CHALLENGE-001, L-REGEX-001 | theorem statements compile without duplicate language definitions; both implications have no `sorry`; exact quantifiers and the erasing-letter step are approved by a formal-language expert | OPEN |

## Published mathematics reproduction

| ID | Obligation | Acceptance artifact | Status |
|---|---|---|---|
| M-PST-001 | Extract exact closure-theorem hypotheses from Pin–Straubing–Thérien. | theorem statements with page/number and notation map | OPEN |
| M-PST-002 | Reconstruct the commutative-group height-one expression in repository notation. | complete hand proof plus at least two checked finite examples | OPEN |
| M-PST-003 | Reconstruct the `A ⋊ C_2` mechanism and identify every use of order two. | dependency graph and formal lemma signatures | OPEN |
| M-BR-001 | Encode one exact-count and one modular-count expression from Bourne–Ruškuc. | JSON certificates accepted by checker | OPEN |
| M-C3-FAIL-001 | Produce the smallest explicit ambiguity/counterexample to the attempted `C_3` unique factorization. | words, factors, and independent verification | OPEN |
| M-RED-001 | Independent human review of the self-contained closure lemmas (note §3.5: Brzozowski derivative, literal-inverse-morphism substitution) behind Proposition 3.1, and of the `Dic_3 ↪ (C_3×C_4)⋊C_2` order-12 audit in `RESULTS.md` §3. One AI adversarial pass (2026-07-23) found no gaps; machine companions `scripts/closure_lemmas_check.py`, `scripts/dic3_embedding.py` pass. | reviewer sign-off recorded in the ledger rows FULL-ALPH-RED-01, DIC3-RED-01, ORD12-ALL-01 | REVIEW |
| M-WEIS-001 | Audit the exact definitions of Weis's candidate languages (esp. L2) against Weis 2011 (UMass thesis, DOI 10.7275/2177022), incl. the "order-48 group" attribution and Weis's own height-one proofs. | definition transcript with page/theorem numbers (`notes/weis_2011_primary_audit.md`, DONE 2026-07-23); syntactic monoid recomputed from the audited definition (DONE: 48 ≅ C₂×S₄, `scripts/weis_l2_actual.py`); comparison with the stage-2 family theorem (DONE 2026-07-23: full L2 is NOT a function of the certified family or its tested extensions, exact witnesses in `scripts/weis_l2_actual.py`, ledger WEIS-L2-NOTFN-01); human cross-check of the audit note pending | REVIEW |
| M-EXP-PR2-001 | Independently audit and replay the imported `exploring-math` PR #2 claims used in `RESULTS.md` §6.1 (finite 4096 family, binary finite-code KR obstruction, fixed A5 raw stamp, and C4 one-marker boundaries). | checker commits and dependency hashes pinned; normal/`-O` outputs reproduced where applicable; proof notes checked against the exact merged commit; ledger rows CORE2-4096-EXT-01, GH1-KR-EXT-01, CORE2-A5-RAW-EXT-01, CORE2-SCH1-EXT-01 upgraded only claim-by-claim | REVIEW |

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

| N-L3-ANCHOR-001 | height ≤ 1 for Weis's L3 (syntactic monoid `S_5`, left open in Weis 2011). | a transitive action of the syntactic group in which every letter moves exactly the anchor pair, as the four-diagonal action does for L2 (`WEIS-L2-GSH-01`, RESULTS.md §5.10); for `S_5` the candidate actions are 5 points, the 6 cosets of `PGL_2(5)`, the 10 pairs, and the 15 involutions | for each candidate action: compute the induced permutations of the two letters, test the anchor criterion (`scripts/a5_frontier.py` style), then attempt the fiber separation with letter parities and compile-and-compare exactly as in `scripts/weis_l2_full_gsh1.py` | OPEN |
| N-L2-AUDIT-001 | independent human re-derivation and program audit of `WEIS-L2-GSH-01` / `WEIS-L2-RSH-01`. | a reader who checks the diagonal construction by hand on short words and audits the DFA compiler (`compile_dfa`, `d_star`, `d_min`) rather than trusting the three-path agreement | rerun `python3 scripts/weis_l2_full_gsh1.py` and `python3 scripts/weis_l2_restricted_height.py` after any compiler edit; both must stay green with the manifest hashes in `data/experiments/weis_l2_full_gsh1.md` | OPEN |
| N-F20-001 | `HeightOneForGroup F_20`, `F_20 = C_5 ⋊ C_4` with faithful action — the smallest non-abelian group outside the PST class (`FRONTIER-ORD20-01`, order 20). **Progress 2026-07-25**: the two-generator word problem is settled, gsh = 1 (`F20-STD-01`, `RESULTS.md` §5.11), via the W-atom scheme at phases mod 4 and counts mod 5 (`WATOM-45-01`). What remains is exactly the full 20-letter alphabet, which by `FULL-ALPH-RED-01` is equivalent to the obligation. | **Narrowed 2026-07-25 by `F20-FULL-OBS-01`**: the §5.5 mechanism fails on all 291 cut patterns, and the obstruction is exactly the five `ε = 2` letters — `Z/4` is composite, so their phase orbit `{0,2}` lets them bounce `1 ↔ 3` without meeting the cut phase. The `A_4` mechanism required a phase group of *prime* order. The GF(5) linear algebra is NOT the bottleneck: formally, `β` is determined. So what is missing is a cut construction that survives a composite phase group | **Route (ii) BLOCKED 2026-07-25 by `F20-SUB10-OBS-01`** (was: "first close the 15-letter sub-alphabet `ε ∈ {0,1,3}`, where the base cut already certifies"). Exact obstruction: on the 10-letter sub-alphabet `ε ∈ {0,1}`, which already generates `F_20`, **no pair pattern is certifiable at all** (period 2, or 4 for same-letter pairs), so the mechanism cannot order two distinct letters with equal `ε` and different `β`; the words `k u₀ u₁ k` and `k u₁ u₀ k` agree on every certified feature in both directions but differ in the group image. The witness contains no `ε = 3` letter, so the 50 pair patterns the 15-letter alphabet does certify never fire, and it is still not separated there. Adding 555 uncertified `Σε = 0` patterns for free does not help. **Route (i) is also insufficient on its own**: a filtration of the phase group does not address the ordering of two letters that carry the *same* `ε`. Remaining routes, none started: (iii) abandon phase-arrival cuts for a finite-code block decomposition in the style of the §5.9 cascade code, so that the ordering information is confined inside a block whose `β` contribution is extractable; (iv) exploit closure properties other than reversal — inverse *alphabetic* morphisms preserve height, so reconstruct the full alphabet as an intersection of reduced-alphabet instances (non-alphabetic inverse morphisms do NOT preserve height, PST 1992 item 7); (v) switch to the lower-bound side and target height ≥ 2, noting that no generalized-star-height lower bound above 1 is known for any language, so this is not to be started lightly | OPEN |
| N-C7C3-001 | `HeightOneForGroup (C_7 ⋊ C_3)` — smallest odd-order group outside the PST class (order 21), and the minimal instance of Bourne's failed `A ⋊ C_3` step (`SMALL-C3-FAIL`). **Progress 2026-07-25 (`C7C3-FULL-01`, `RESULTS.md` §5.14)**: the `A4-FULL-01` multi-mover mechanism transposes to the **full 21-letter alphabet** — which by `FULL-ALPH-RED-01` is the whole obligation — with all 288 cut patterns aperiodic, GF(7) rank 6/6, and exact reconstruction of the identity fibre on all 204205 words of length ≤ 4. The phase group is `Z/3`, of prime order, so the `Z/4` obstruction of `F20-FULL-OBS-01` does not arise. | **Narrowed 2026-07-25**: what is missing is no longer a mechanism but a *proof*. `C7C3-FULL-01` is `COMPUTED`: agreement on finitely many words is not language equality, and no height-one regular expression has been built or compiled | (1) construct the height-one expression from the certified features and prove language equality against the 21-state Cayley automaton by complete product reachability, reusing the AST, `compile_dfa`, `d_min` and `equivalence_counterexample` of `scripts/weis_l2_full_gsh1.py` exactly as `scripts/f20_word_problem.py` does — this is the whole remaining task and would raise the row to `PROVED`; (2) if (1) fails, fall back to the original route: enumerate the transitive actions (7 points, 3 cosets of `C_7`, 21 points) and test the anchor criterion on each, noting that `C_7 ⋊ C_3` has no subgroup of index 2 so parity-based fiber separation is unavailable | OPEN |
| N-S4-001 | `HeightOneForGroup S_4` (order 24, outside the PST class), and then `HeightOneForGroup (C_2 × S_4)`. | a mechanism for a non-cyclic quotient: `S_4 / V_4 ≅ S_3`; `WEIS-L2-GSH-01` settled one `C_2×S_4`-recognized language, not the whole family | the full-alphabet reduction (`FULL-ALPH-RED-01`) makes the 24-letter identity fibre the single target; attack it with the diagonal-anchor pipeline of `scripts/weis_l2_full_gsh1.py` | OPEN |

**Blocker for N-COH-001:** no coefficient object or exact map has yet been selected. Invoking an LHS spectral sequence before closing this gap is out of scope.

**M-WEIS-001 unblocked (2026-07-23):** the full thesis PDF (143 pages) was retrieved via the Wayback Machine and the 2009 seminar abstract directly; URLs, bibliographic data, verbatim quotes, and the corrections they force (L2 was proposed by PST 1992; full L2 and L3 are left OPEN in the thesis; the order-48 monoid is real, ≅ C₂×S₄) are in `notes/weis_2011_primary_audit.md`. The earlier claim "Weis showed all four candidates have height one" survives only as a statement about the 2009 abstract, not about the thesis. Remaining: the §5.9-family vs actual-L2 comparison and a human cross-check of the audit.

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
