# Claims Ledger

Every nontrivial statement used by the project belongs here. The status labels are:

- `PROVED`: proved in this repository, with a file/theorem location.
- `CITED`: taken from a named source, with theorem/page information where available.
- `COMPUTED`: established by a deterministic program and preserved input/output manifest.
- `CONJECTURAL`: a precise mathematical conjecture.
- `SPECULATIVE`: a research direction not yet precise enough to be a conjecture.
- `REFUTED`: false; counterexample recorded.
- `UNREVIEWED`: imported or generated statement awaiting audit.

Do not upgrade a status by editing prose. Add the verification artifact.

| ID | Claim | Status | Evidence / location | Owner | Last review |
|---|---|---|---|---|---|
| GSH-STATUS-01 | No regular language of generalized star-height greater than one is currently known in the surveyed literature. | CITED | Place–Zeitoun 2017, introduction; Bourne 2017, introduction; `SURVEY.md` §1 | survey lead | 2026-07-22 |
| GSH-BASE-01 | Generalized star-height zero equals the class of star-free languages. | CITED | definition plus Schützenberger 1965 interface; `SURVEY.md` §2 | language lead | 2026-07-22 |
| GSH-BASE-02 | A regular language is star-free iff its syntactic monoid is aperiodic. | CITED | Schützenberger 1965 | language lead | 2026-07-22 |
| PST-CL-01 | Bounded generalized star-height is closed under left/right quotients, inverse alphabetic morphisms, and injective star-free substitutions under the hypotheses in Pin–Straubing–Thérien. | CITED | Pin–Straubing–Thérien 1992; exact hypotheses must be checked before formal use | source auditor | 2026-07-22 |
| PST-GRP-01 | Every language recognized by a finite commutative group has generalized star-height at most one. | CITED | Pin–Straubing–Thérien 1992 | group lead | 2026-07-22 |
| PST-GRP-02 | The height-one result extends to finite nilpotent groups of class at most two. | CITED | Pin–Straubing–Thérien 1992, Theorem 7.3 as indexed in the open version | group lead | 2026-07-22 |
| PST-GRP-03 | The published semidirect-product result covers divisors of a semidirect product of a commutative group by an elementary abelian 2-group. | CITED | Pin–Straubing–Thérien 1992 | group lead | 2026-07-22 |
| BR-REES-01 | Languages recognized by finite Rees (zero-)matrix semigroups over abelian groups have generalized star-height at most one. | CITED | Bourne–Ruškuc 2016 | language lead | 2026-07-22 |
| SMALL-12-01 | In Bourne's finite-group ladder, all groups of order below 12 are covered; `A_4` and `Dic_3` are the unresolved order-12 cases in that program. | CITED | Bourne 2017, group-order discussion | group lead | 2026-07-22 |
| SMALL-C3-FAIL | The direct extension of the cited `A ⋊ C_2` argument to `A ⋊ C_3` fails at a unique-factorization step. | CITED | Bourne 2017, failure analysis | source auditor | 2026-07-22 |
| A5-SCOPE-01 | A theorem for languages recognized by `A_5` would not by itself settle the global generalized star-height problem. | PROVED | immediate from scope of the quantified theorem; `README.md` | referee | 2026-07-22 |
| A5-MATHLIB-01 | Mathlib provides `alternatingGroup (Fin 5)` and a simplicity theorem for degree five. | CITED | mathlib module `Mathlib.GroupTheory.SpecificGroups.Alternating` | Lean lead | 2026-07-22 |
| COH-01 | Group or monoid cohomology supplies an established invariant of generalized star-height. | REFUTED | no such theorem found in surveyed sources; never assume this statement | referee | 2026-07-22 |
| COH-02 | A concrete word-to-cochain map may organize extension/gluing arguments. | SPECULATIVE | `SURVEY.md` §7; requires coefficient object and closure theorem | cohomology lead | 2026-07-22 |
| CERT-01 | The Python checker accepts only when the supplied generalized expression has the claimed height bound and its compiled DFA is equivalent to the target DFA. | PROVED | `tools/regex_cert.py`, `tests/test_regex_cert.py`; proof is program audit, not Lean | computational lead | pending first CI |
| LEAN-LANG-01 | Language concatenation and star definitions in `GSH/Language/Basic.lean` match the mathematical definitions in the blueprint. | UNREVIEWED | Lean source; compiled in first local build 2026-07-22 (`PROOF_OBLIGATIONS.md` repair log); semantic review pending | Lean lead | 2026-07-22 |
| LEAN-DFA-01 | `DFA.run_append` is formalized. | UNREVIEWED | `GSH/Automata/DFA.lean`; compiled in first local build 2026-07-22; semantic review pending | Lean lead | 2026-07-22 |
| LEAN-A5-01 | The repository's `A5` abbreviation reduces to `alternatingGroup (Fin 5)`. | UNREVIEWED | `GSH/Groups/A5.lean`; compiled in first local build 2026-07-22 (simplicity hypothesis discharged via `Nat.card_fin`); semantic review pending | Lean lead | 2026-07-22 |
| GLOBAL-ONE | Every regular language has generalized star-height at most one. | CONJECTURAL | workshop north-star target | all | 2026-07-22 |
| A4-STD-01 | With the morphism φ(a) = (123), φ(b) = (12)(34) generating `A_4`, the language { w ∈ {a,b}* : φ(w) = e } has generalized star-height at most one. | COMPUTED | `RESULTS.md` §5–§6; atoms proved by exhaustive product-automaton search (`scripts/a4_attempt.py`), end-to-end agreement on all words of length ≤ 16 plus 30k random words (`scripts/a4_final.py`); commit dd316b4; run manifest in `data/experiments/` still pending | Kazumi Kasaura | 2026-07-22 |
| A4-FULL-01 | For the alphabet consisting of all twelve elements of `A_4` under the evaluation morphism, the word-problem language { w : eval(w) = e } has generalized star-height at most one. | COMPUTED | `RESULTS.md` §5.5; 93 token languages certified aperiodic, reachability = f(P, N[g,p]) proved by exhaustive 384-state product-automaton search (`scripts/a4_full3.py`), reconstruction checks exhaustive to bounded length plus random sampling (`scripts/a4_full12.py`); commit f4258df; run manifest in `data/experiments/` still pending | Kazumi Kasaura | 2026-07-22 |
| A4-ANYGEN-01 | For every monoid morphism φ from a free monoid over a finite alphabet to `A_4`, the language φ⁻¹(e) has generalized star-height at most one. | UNREVIEWED | `RESULTS.md` §6 note; follows from A4-FULL-01 via inverse-alphabetic-morphism closure (PST-CL-01) once the exact hypotheses of that closure are checked | Kazumi Kasaura | 2026-07-22 |
| LAAB-04-01 | The language L(aab,0,4) = { w ∈ {a,b}* : binom(w, aab) ≡ 0 mod 4 } has generalized star-height at most one. | COMPUTED | `RESULTS.md` §3, §5; proved W atoms plus arithmetic reduction, composite checked on all words of length ≤ 13 plus 150k random words; commit dd316b4; run manifest in `data/experiments/` still pending | Kazumi Kasaura | 2026-07-22 |

## Update template

```text
| ID | Fully quantified claim. | STATUS | exact source, theorem, code, or counterexample | owner | YYYY-MM-DD |
```

For `COMPUTED` claims also record: commit hash, command, input hash, output hash, and resource bound in `data/experiments/`.
