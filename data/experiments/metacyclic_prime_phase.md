# Run manifest: the prime-phase metacyclic family of Family A

Claims: `C13C3-FULL-01`, `C11C5-FULL-01`, `C19C3-FULL-01` (all `EMPIRICAL`),
supporting evidence for `FAMILY-A-PRED-01` (`CONJECTURAL`). Obligation
`N-FAMILY-A-001`.

Derivation and the scope limits: `notes/metacyclic_prime_phase.md`.
Base commit: `17337f0`.

## Commands

```bash
python3 scripts/research/metacyclic_full_alphabet.py                  # (7,3), the positive control
python3 scripts/research/metacyclic_full_alphabet.py --target C13C3
python3 scripts/research/metacyclic_full_alphabet.py --target C11C5
python3 scripts/research/metacyclic_full_alphabet.py --target C19C3
python3 scripts/research/metacyclic_full_alphabet.py --target F20    # must exit 1
```

No flags were used for any run in the table below: no length caps, no reduced
sweeps, nothing truncated. The no-argument run is `(7, 3)` on purpose, so the
run `scripts/ci/run_research.py` makes is the positive control; the script is
registered in that file's `SLOW` set because it takes longer than the fast-tier
threshold.

`--target F20` exits **1**. That is the intended result and the script is not
in the set CI runs by default at that target.

## Environment

- Python 3.14.6, macOS (darwin 25.5.0), standard library only, no network.
- The three new groups were run concurrently, so their wall clocks are longer
  than they would be in isolation.

## Result

| group | p, q, r | letters | candidate patterns certified | GF(p) rank | mutations broken | membership base rate | wall clock |
|---|---|---|---|---|---|---|---|
| `C_7 : C_3` | 7, 3, 2 | 21 | 288 / 288 | 6/6 on each of 2 classes | 84 / 84, 0 survived | 464/9724 (0.048) | 6.4 s |
| `C_13 : C_3` | 13, 3, 3 | 39 | 1002 / 1002 | 6/6 on each of 2 classes | 168 / 168, 0 survived | 1562/60880 (0.026) | 63.4 s |
| `C_11 : C_5` | 11, 5, 3 | 55 | 2388 / 2388 | 10/10 on each of 4 classes | 440 / 440, 0 survived | 3082/169456 (0.018) | 1485.1 s |
| `C_19 : C_3` | 19, 3, 7 | 57 | 2148 / 2148 | 6/6 on each of 2 classes | 252 / 252, 0 survived | 3308/188500 (0.018) | 379.8 s |
| `F_20 = C_5 : C_4` | 5, 4, 2 | 20 | **0 / 291** | not reached | not reached | not reached | exit 1 |

Every figure above is from a run made while writing this manifest, not copied
from a report of an earlier one. The three new groups ran concurrently, which
is why their wall clocks are longer than they would be alone.

The reconstruction of section 5 is exhaustive to length 3 — 9724, 60880,
169456 and 188500 words respectively — and then a fixed-seed sample of 20000
words of lengths 4 to 400. **The exhaustive part is bounded, so section 5 is a
sample and it caps each row at `EMPIRICAL`.** Section 2, the aperiodicity
table, is not bounded: each candidate's transition monoid is enumerated
completely.

The same-letter pure-power patterns, which the mechanism excludes and which
must fail, do fail everywhere: 26 of 26 for `C_13 : C_3` (period 3), 44 of 44
for `C_11 : C_5` (period 5), 38 of 38 for `C_19 : C_3` (period 3), 15 of 15 for
`F_20` (period 4). A judge that could not answer no would report the same
successes above.

## Section 7: the reconstruction, decided

Added 2026-07-28. The bounded-plus-sampled reconstruction of section 5 is
replaced by a decision: BFS the product of the certified-feature machine with
the group element, and require agreement at every reachable state.

| group | reachable product states | feature cells | coefficient mutations rejected |
|---|---|---|---|
| `C_7 : C_3` | 442 | 442 | 84 / 84, 0 survived |
| `C_13 : C_3` | 1522 | 1522 | 168 / 168, 0 survived |
| `C_11 : C_5` | 3026 | 3026 | 440 / 440, 0 survived |
| `C_19 : C_3` | 3250 | 3250 | 252 / 252, 0 survived |

Cells equal states in every case, so the map from feature cell to group element
is injective and the agreement is an equality rather than mere constancy on
cells. The cap is 20,000,000 states and the largest run reached 3250, so
nothing was truncated; `--section7-cap 100` exits 1 with
`BLOCKED: state cap 100 reached after 6 states; nothing is decided.` and writes
no verdict, which is the no-silent-truncation path exercised.

**The rows stay `EMPIRICAL` anyway.** Section 7(a) decides a machine; section
7(c), which checks that machine against section 5's own
`prefix_beta_from_certified_features`, is bounded and sampled. That single
comparison is now the only sampled link, and it is `N-METACYC-TRANS-001`.

No verdict file is committed. `--write-verdict` exists but is off by default: a
verdict backs a `COMPUTED` row, no row here reaches `COMPUTED`, and
`lint_claims.py` correctly refuses a verdict file that no script in
`scripts/ci/` regenerates — the four targets together take about half an hour
and cannot run in `check.sh`.

## Controls

| Control | Result |
|---|---|
| positive: `(7,3)` reproduces `c7c3_full_alphabet.py` | every result line identical; differences are two header lines, one cross-check line, the concluding sentence and the runtime |
| negative: `F_20` at `(5,4)`, `q` composite | `exact total=291; certified=0; failed=291`, exit 1, `witness=g(e=2,b=0)` and `period=2` on all 14 signatures — `F20-FULL-OBS-01` reproduced |
| same-letter pure-power patterns must fail | fired for every group, successes included |
| every solved coefficient mutated | no survivors for any group |
| membership base rate reported | not near-constant for any group |
| count-only witness pair exhibited | found at length 4 for each of the four prime-phase groups |
| section 7 brittleness: every solved coefficient mutated, BFS re-decided from scratch | 84 / 168 / 440 / 252 rejected, 0 survivors |
| section 7 transcription broken 8 ways (phase shifts, dropped pair conditions, reversed product order) | 8 / 8 detected by 7(c) |
| sections 1–6 unchanged by adding section 7 | identical line for line at `(7,3)`, verified by diff |

## Hashes

| Artifact | sha256 |
|---|---|
| `scripts/research/metacyclic_full_alphabet.py` | `53bf60b73eb301c206c31934f025513586c403478ed0ade6aac10e7a21815dc3` |
| `tests/test_metacyclic_cli.py` | `4c2e469086e3f0b2a0e1b18aeb9d83923a75910333ae5fb9bcd6dcda74116704` |
