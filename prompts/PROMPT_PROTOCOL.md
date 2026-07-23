# Prompt Protocol for Mathematical and Coding Agents

The project uses two prompt modes. Never blend them silently.

## Resolution mode

Use when the agent is being benchmarked against a frozen yes/no theorem.

- Demand a complete proof or complete disproof of the exact statement.
- Say explicitly that a reformulation, heuristic, computational search, or conditional theorem does not satisfy the completion contract.
- Still require the agent to preserve any rigorous partial artifacts in the return packet.
- Reserve an adversarial verification phase and require a final dependency audit.

## Research mode

Use for ordinary workshop work.

- Target one lemma, counterexample, source extraction, API repair, or certificate.
- Reward sharp blockers and reusable negative results.
- Require an acceptance test and a bounded return artifact.
- Stop before context or budget is exhausted.

## Required prompt fields

```text
MODE:
ROLE:
FROZEN TARGET:
DEFINITIONS AND CONVENTIONS:
AVAILABLE SOURCES/FILES:
KNOWN RESULTS ALLOWED:
KNOWN FAILURE MODES:
WHAT COUNTS AS SUCCESS:
WHAT DOES NOT COUNT:
REQUIRED ARTIFACTS:
VERIFICATION:
BUDGET AND CHECKPOINTS:
STOP CONDITIONS:
RETURN SCHEMA:
```

## Context policy

Give the agent the smallest coherent source packet. Prefer exact theorem extracts and local file paths over a repository dump. Ask it to explore the relevant files before proposing edits. For long runs, store state in files (`manifest.json`, checkpoint notes, test logs) rather than relying on an enormous conversation.

## Independence policy

During the first wave, do not reveal the favored route to all agents. Assign genuinely different mechanisms. Cross-pollinate only after each route returns its strongest lemma and sharpest obstruction.

## Verification policy

Every prompt names a check. Examples:

- `lake env lean GSH/Recognition.lean`;
- `python3 scripts/check_certificate.py certificate.json`;
- a page/theorem-number source comparison;
- an explicit finite counterexample suite;
- independent reconstruction by a referee agent.

“Use your best judgment” is not a verification plan.

## Budget policy for the remaining 10% of Codex quota

The expensive run should begin only when the task packet is complete. Default allocation:

- 15% reconnaissance;
- 20% independent routes;
- 30% selected route;
- 20% attack/repair;
- 15% integration and report.

At 65% consumed, continue only if a central lemma has an executable or line-by-line check. Never spend the final verification reserve on more brainstorming.
