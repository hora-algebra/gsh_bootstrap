# CLAUDE.md

@AGENTS.md

## Claude-specific operating notes

- Keep this file small; procedures live in `prompts/` and `scripts/`.
- Use Explore/Plan subagents for high-volume literature or API reconnaissance, then return summaries rather than logs.
- Before coding: inspect, plan, name tests, then implement.
- Use a cheaper/faster subagent for grep, import discovery, and repetitive test repair; reserve the strongest model for theorem decomposition and adversarial audit.
- Create checkpoints before quotient-type or finite-group API work.
- Never let auto-memory turn a conjecture into a fact. Durable mathematical status belongs only in `CLAIMS_LEDGER.md`.
