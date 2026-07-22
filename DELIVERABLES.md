# Deliverables and verification status

Generated on 22 July 2026 for the ZMC generalized star-height working group.

## Required artifacts

- `docs/blueprint.tex` and `docs/blueprint.pdf`: Lean formalization blueprint.
- `docs/textbook_number_theorists.tex` and `.pdf`: formal-language primer for number/group theorists.
- `docs/textbook_formal_language_theorists.tex` and `.pdf`: finite groups and cohomology primer for formal-language theorists.
- `docs/textbook_lean_experts.tex` and `.pdf`: project semantics and architecture primer for Lean experts.
- `SCENARIOS.md`: proof, disproof, partial-success, mathematical, technical, and sociological scenarios.
- `SUGGESTIONS.md`: workshop and AI-use protocol.
- `SURVEY.md`: preceding-work survey and research routes.
- `prompts/`: role-specific coding/research prompts and a long-run launch protocol.
- `GSH/`: Lean definitions and theorem interfaces.
- `tools/regex_cert.py`: exact generalized-expression/DFA certificate checker.

## Verification completed in the generation environment

- All four TeX documents compiled with `latexmk` and `biber`.
- All four PDFs were rendered to PNG and visually inspected at 150 dpi.
- Five Python unit tests passed.
- Both example JSON certificates passed exact equivalence checks.
- Claim-ledger lint passed for 19 rows.
- Proof-hole lint found exactly two registered Lean placeholders and no unregistered holes.

## Verification not completed here

Lean and Lake were not installed in the generation container, and outbound DNS was unavailable when the official elan installer was attempted. The Lean files were statically reviewed but were not compiled in this environment. Run `./scripts/bootstrap.sh --install-elan` or use the included GitHub Actions workflow on a networked machine. Record any pinned-mathlib API repair in `PROOF_OBLIGATIONS.md`.
