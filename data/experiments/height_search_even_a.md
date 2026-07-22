# Run record: exhaustive height-≤1 synthesis search for even_a

- Date: 2026-07-22 (JST). Code commit: c2f5928 (tools at that revision).
- Command: `python3 -m tools.height_search --target even_a --max-size <N>`
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

Not found up to size 13, complete (pruned = 0).  Kept at size 13: 396,765;
distinct languages total 593,575; wall time 134.3 s.  Hence the minimal
binary-AST size is ≥ 14, and ≤ 15 by the hand-built witness above.
