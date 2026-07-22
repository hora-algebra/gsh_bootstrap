# Lessons from Public Jacobian and Unit-Distance Runs

This file extracts workflow patterns, not mathematical content.

## Publicly visible patterns

OpenAI's public Jacobian-conjecture prompt used an exact complete-proof-or-disproof contract, maintained several incompatible approaches, delayed convergence, required an approach registry, emphasized theorem-strength missing lemmas, scheduled adversarial audits, and reserved a synthesis phase. The public unit-distance account similarly separated automated generation from AI grading, internal human examination, external expert checking, and human-edited exposition.

The transferable lessons are:

1. Freeze the mathematical statement and quantifiers.
2. Keep proof and disproof routes alive.
3. Require mechanism-level diversity rather than many paraphrases of one idea.
4. Treat the strongest missing lemma as a first-class object.
5. Alternate construction and attack.
6. Preserve reproducible artifacts, not just transcripts.
7. Escalate verification through increasingly independent layers.
8. Make the final synthesis smaller and more auditable than the search trace.

## Adaptation to generalized star height

A large run should not merely ask “solve generalized star height.” It should partition into:

- Pin-style explicit expression construction;
- repair of the `C_3` unique-factorization failure;
- pseudovariety/factorization-forest route;
- lower-bound invariant route;
- small-group (`A_4`, `Dic_3`) route;
- `A_5` subgroup and representation route;
- cohomology route only after an explicit word-to-cochain map exists;
- Lean/API and certificate-verification route;
- independent referee route.

The final orchestrator may announce a resolution only when a complete argument survives all checks. It should still return rigorous partial artifacts to the human research ledger when the completion contract is not met.

## Source links

- OpenAI, public Jacobian-conjecture prompt and derivation (20 July 2026).
- OpenAI, unit-distance problem report and proof materials.
- OpenAI Codex documentation on `AGENTS.md`, worktrees, subagents, and long-running tasks.
- Anthropic engineering guidance on simple composable agents, executable feedback, context management, and subagents.

Stable links are recorded in `docs/gsh_additions.bib`.
