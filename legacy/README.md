# Legacy

Work that a later artifact replaced. It is kept because `AGENTS.md` forbids
deleting failed approaches: a route that was tried and did not work is a result,
and the next person to have the same idea should be able to find out that it was
already had. Nothing here is run by CI, nothing here is evidence for a live
claim in `CLAIMS_LEDGER.md`, and nothing here should be extended.

If you are looking for the current version of one of these, follow the
"replaced by" column.

## `legacy/scripts/`

| File | What it was | Replaced by |
|---|---|---|
| `a4_full.py` | The first multi-mover attempt at full-alphabet `A_4`, using existential parsing with marks. It could not determine the entry phase of a token, and `RESULTS.md` §5.5 keeps it as the record of that failure. | `a4_full2.py`, then `a4_full3.py` |
| `a4_full2.py` | Pattern-conditioned cut features with aperiodicity certification. Forward direction only, so a partial success: some of `N[u,p]`, `N[d,p]` stay undetermined. | `scripts/research/a4_full3.py`, which decides the `{u,d,k}` version on all 384 states |
| `search.py` | The first computer search over candidate languages (`RESULTS.md` §4). | `tools/height_search.py`, which enumerates by size with a certificate |
| `verify.py` | Deep verification of promising pairs, by agreement on random long words. | Nothing: the method itself was retired. The 2026-07-25 completeness audit stopped accepting bounded-length and random-word agreement as evidence, so this script's kind of output is now `EMPIRICAL` by definition — it can refute, and it did, but it cannot establish. |

`verify.py` is the interesting one. It was not superseded by a better program;
its whole approach was reclassified. Keeping it visible is the point.

## `legacy/prompts/` — deleted 2026-07-25, recoverable at `230cde4`

Fourteen role prompts from the original multi-agent setup — orchestrator,
literature auditor, Lean API scout, definition engineer, small-group explorer,
`A_5` cohomology, counterexample search, proof synthesizer, adversarial referee,
formalization agent, integration agent, long-run budget, plus
`PROMPT_PROTOCOL.md` and `JACOBIAN_UNIT_DISTANCE_LESSONS.md`.

They were **process history rather than mathematics**, which is why deleting
them does not violate the rule against deleting failed approaches: no ledger row
and no proof obligation ever depended on one. The durable rules ended up in
`AGENTS.md`, and the checks ended up in `scripts/ci/`, which is where a rule
belongs once you want it obeyed. Nothing outside this file had referenced them
for a long time.

Two are worth knowing about before you go looking:

- `08_adversarial_referee.md` specified a structured `VERDICT:` output that no
  consumer was ever written for. That is the same idea `tools/verdict.py` now
  implements — against programs instead of agents, which is the version that
  works, because a program cannot be persuaded to report a verdict it did not
  compute.
- `TASK_PACKET.md`, the one prompt still in use, is not deleted. It moved to
  `scripts/ci/templates/` next to the `new_task.py` that reads it.

`git show 230cde4:legacy/prompts/<name>` retrieves any of the others.
