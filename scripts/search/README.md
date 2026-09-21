# Long searches and negative results

`scripts/ci/run_research.py` re-runs **every** program in `scripts/research/`
on each push, under a 300-second cap, and treats a non-zero exit as a
regression. The programs here break one or both of those assumptions on
purpose, so they live outside that sweep rather than being exempted one flag at
a time:

| script | why it is not in `scripts/research/` |
|---|---|
| `a4_aggregate_cstar.py` | size-ordered enumeration of star-free expressions; minutes to hours, and it is a search, so exhausting the size bound without a hit *is* the result |
| `a4_cstar_intersect.py` | same, for intersections of star-free supersets |
| `a4_cstar_slt.py` | same, for the locally-testable forms |
| `a4_pair_recovery_identity.py` | exhaustive + random check of the GF(2) recovery identity over 4 071 078 words; roughly ten minutes |
| `a4_easy_feature_span.py` | **exits 1 on success**: its result is the negative one — the easy feature basis does not separate `N[g,p]`, and it prints the length-4 collision that proves it |

All five are single-threaded and the three searches take `--duty` (default
`0.5`), which sleeps between work slices so the process stays under half of one
core.

The `A_4` programs whose exit code *is* meaningful and which finish quickly —
`a4_cstar_block_code.py`, `a4_cstar_search.py`, `a4_hard_cstar_forms.py`,
`a4_hard_cstar_forms2.py`, `a4_pattern_token_starfree.py`, and
`a4_first_return_token.py` (slow tier, 32 s) — are in `scripts/research/` and
are covered by the sweep.
