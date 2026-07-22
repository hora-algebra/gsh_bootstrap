# Generalized Star-Height Workshop Bootstrap

This repository is a prepared workspace for a mixed group of formal-language theorists, group/number theorists, and Lean contributors working on the **generalized star-height problem**.

## The target, stated precisely

For a finite alphabet `A`, generalized regular expressions are built from `∅`, `ε`, and letters using union, concatenation, complement (relative to `A*`), and Kleene star. The generalized star-height of an expression is the maximum nesting depth of Kleene star; the generalized star-height of a language is the minimum height of any generalized expression defining it.

The workshop separates two questions that are often conflated:

1. **Height-one collapse conjecture:** every regular language has generalized star-height at most one.
2. **Decision problem:** compute the generalized star-height of an input regular language.

No language of generalized star-height greater than one is currently known. A proof of height-one collapse would reduce exact computation to the decidable star-free-versus-height-one distinction. A counterexample to height-one collapse would not by itself solve the full decision problem, but it would resolve the central structural conjecture.

## Why the repository starts below `A_5`

`A_5` is a strategically important non-solvable test case, and mathlib already contains `alternatingGroup (Fin 5)` and its simplicity theorem. It is not, however, the first unresolved group-order case in the published program. Bourne's 2017 thesis identifies the order-12 groups `A_4` and `Dic_3` as the first unresolved hurdle in that line of work. This repo therefore runs two tracks:

- **Track S (small-group ladder):** reproduce and extend the abelian, nilpotent-class-2, `A ⋊ C_2`, `A_4`, and `Dic_3` arguments.
- **Track A5 (ambitious structural track):** use subgroup structure, extensions, representations, and carefully specified cohomological experiments to attack languages recognized by `A_5`.

The cohomology track is explicitly exploratory. No preceding result surveyed here identifies group cohomology as an established generalized-star-height invariant.

## Quick start

```bash
./scripts/bootstrap.sh
./scripts/check.sh
```

The pinned toolchain is Lean `v4.32.0` with mathlib `v4.32.0`. The first command installs project dependencies and downloads the mathlib cache through Lake. The second command builds the Lean library, runs the smoke file, checks the claims ledger, and scans for undeclared proof holes.

> Generation note: the repository was created in an environment without Lean/elan, so the Lean source was statically reviewed but not compiled here. The bootstrap and CI files are intended to make the first real build deterministic. The first workshop task is to run `./scripts/check.sh` and record every API repair in `PROOF_OBLIGATIONS.md`.

## Main files

| File | Purpose |
|---|---|
| `SURVEY.md` | Preceding work, verified claims, and a reading order. |
| `SCENARIOS.md` | Proof, disproof, partial-success, and failure scenarios. |
| `SUGGESTIONS.md` | How to run the project with mathematicians who are not AI specialists. |
| `ROADMAP.md` | 48-hour workshop plan and 12-week research plan. |
| `AGENTS.md` / `CLAUDE.md` | Durable instructions for coding/research agents. |
| `CLAIMS_LEDGER.md` | Every mathematical claim classified as proved, cited, computed, conjectural, or speculative. |
| `PROOF_OBLIGATIONS.md` | Lean holes and mathematical dependencies with owners and acceptance tests. |
| `prompts/` | Budget-aware prompts for literature, proof search, disproof search, Lean, and adversarial review. |
| `docs/blueprint.{tex,pdf}` | Formalization blueprint. |
| `docs/textbook_*.{tex,pdf}` | Three role-specific primers. |
| `GSH/` | Lean skeleton, executable definitions, and theorem interfaces. |

## Non-negotiable research rules

1. **Do not call a computationally resistant candidate a lower bound.** Failure to synthesize a height-one expression up to a size bound is only a search result.
2. **Do not identify “recognized by `M`” with “having syntactic monoid `M`.”** The former is existential and stable under division; the latter is minimal.
3. **Do not import restricted-star-height arguments without checking complementation.** This repo uses “star-height” to mean generalized star-height unless explicitly marked `restricted`.
4. **No proof is announced from an AI transcript.** A result must survive domain-specific adversarial review, independent reconstruction, reference audit, and—where in scope—a clean Lean build.
5. **Partial progress is preserved.** Search-agent prompts may demand a binary final answer, but the human project maintains a separate ledger for lemmas, failed mechanisms, counterexamples to sublemmas, and reusable formal infrastructure.

## Recommended first assignments

- Formal-language theorist: verify `SURVEY.md` and write a one-page correction list.
- Group/number theorists: work through `docs/textbook_number_theorists.pdf`, then choose either the `A_4/Dic_3` extension problem or the `A_5` subgroup/cohomology matrix.
- Lean team: run the build, stabilize `Language.Basic`, `Regex.Generalized`, `Automata.DFA`, and `Monoid.Syntactic`, and replace API-sensitive placeholders with compiling declarations.
- One independent referee: read only `SCENARIOS.md`, `CLAIMS_LEDGER.md`, and candidate outputs; do not join the favored route during the first search wave.

## License

Code is released under MIT. Documentation is released under CC BY 4.0 unless a cited source imposes different terms. The included Ryuya template and bibliography remain source materials and are copied for workshop use.
