# Run record: exhaustive height-≤1 synthesis search for even_a

- Date: 2026-07-22 (JST). Code commit: c2f5928 (tools at that revision).
- Command: `python3 -m tools.height_search --target even_a --max-size 13 --max-states 0`
- Target: `even_a` = { w ∈ {a,b}* : |w|_a even }, minimal DFA: 2 states.
- Grammar: generalized regexes with *binary* union/concat, unary compl/star,
  atoms {∅, ε, a, b}; syntactic star height ≤ 1; size = AST node count.
- Machine: macOS (darwin 25.5.0), CPython 3.x, single process, no pruning
  (`--max-states 0`), so every completed size is a complete enumeration
  up to language equivalence.

## Result

No expression of size ≤ 12 defines even_a.  Distinct languages seen after
completing size 12: 196,810 (kept per size: 4, 6, 9, 35, 77, 251, 642, 1908,
5579, 15725, 47827, 137529); wall time ≈ 40 s, pruned = 0.

Size 13: see the final line of this file (filled after the run).

## Upper bound (hand-built, independently checked)

`(b | a ~(~0 a ~0) a)*` — star height 1 — was verified equivalent to even_a
by `tools.regex_cert.check_certificate` (n-ary concat AST size 13; the same
shape written with binary concatenation has 15 nodes).  Together with the
exhaustive result: the minimal binary-AST size of a height-≤1 generalized
expression for even_a lies in [14, 15].

Interpretation note: in *generalized* star height, `b*` costs a star; the
familiar `(b|ab*a)*` therefore has syntactic height 2, which is why the
minimal height-1 expression is this large.  None of this says anything about
star height ≥ 2 for any language (README rule 1); even_a has height exactly 1
(it is non-aperiodic, hence not height 0, and height ≤ 1 by the certificate
`data/certificates/height1_even_a.json`).

## Size 13 outcome

Not found up to size 13, complete (pruned = 0).  New distinct languages at
size 13: 396,765 (= 593,575 − 196,810); expressions kept at size 13 as
printed by the tool: 419,310 (the tool's "kept" counts retained canonical
expressions, which exceeds the distinct-language increment).  Distinct
languages total 593,575; wall time 134.3 s.  Hence the minimal binary-AST
size is ≥ 14, and ≤ 15 by the hand-built witness above.

## Reproducibility manifest (independent rerun, 2026-07-22 17:05 JST)

- Command: `python3 -m tools.height_search --target even_a --max-size 13 --max-states 0`
- Code at commit c2f5928 (identical modules also present at 97b38d0):
  - `tools/height_search.py` sha256 `951a3a3be6a104c9f60b0b0e9eca87e3fcb07db21f758302a2f1d3be962dab1f`
  - `tools/targets.py` sha256 `d37eb89f1277506da176960166215c84c9993155184eacb6def5365f56c9531e`
  - `tools/regex_cert.py` sha256 `9f3e3f2ec4ab6ffbdfb5915201c8a98629cf63897330e3bad40da01e39787fe2`
- Input: none beyond the code (the target DFA for `even_a` is built
  deterministically by `tools.targets`; 2 states).
- Result: all per-size kept counts and the distinct-language total (593,575)
  identical to the original run; wall time 128.3 s on the same machine
  (timings vary, counters are deterministic).
- Output hash: sha256 of the full stdout with wall-clock timings stripped
  (`sed -E 's/, [0-9.]+s\)/)/; s/ \| [0-9.]+s$//'`):
  `ebe76b06d12da0af0cb1ae1669fe634781df0aaaff4ec0160a6b328d47d99c79`
