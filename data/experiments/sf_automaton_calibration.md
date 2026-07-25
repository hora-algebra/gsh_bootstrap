# Run manifest: star-free-labelled automata, calibration

Claims: `SFA-EGGAN-01` (`PROVED`), `SFA-STAR-ONLY-01` (`PROVED`),
`SFA-CORE2-RANK-01` (`UNREVIEWED`), `SFA-L2-MEASURE-01` (`COMPUTED`).

Derivation and proofs: `notes/sf_labeled_automata.md`.
Base commit: `1f6c307` (merge of PR #28).

## Commands

```bash
python3 scripts/research/sf_automaton_calibration.py                # checks only
python3 scripts/research/sf_automaton_calibration.py --certificate  # also emits certificates
python3 -m unittest tests.test_sf_automaton -v             # acceptance tests
```

No third-party packages; Python standard library only.

## Environment

- Python 3.14.6, macOS (darwin 25.5.0), single process, no network.
- Wall clock: about 0.04 seconds. Peak memory: a few MB.

## Hashes

| Artifact | sha256 |
|---|---|
| `tools/sf_automaton.py` | `6536c061da7a9771409fbaa569353a0768bce59bd2cb2a46529c5aa1e0944d1e` |
| `scripts/research/sf_automaton_calibration.py` | `6605f71d0cfd9f03d9609905a7ad8593437cf5628b9fa2c3ed9e59061195841b` |
| stdout of the default run | `db656f5bdf81c57afa36947d2aa16fedc6b3b728ef667cf1041fab1c44510cdb` |

The tool hash changed on 2026-07-25 (letter-alphabet validation in
`__post_init__`, plus `apply_star`); the stdout hash is unchanged, since
neither addition alters what this script computes.

Reproduce the output hash with

```bash
python3 scripts/research/sf_automaton_calibration.py | shasum -a 256
```

The output is deterministic: no randomness, no sampling, no length cutoffs.
All vertex collections are ordered tuples and every union is built in a fixed
insertion order, so state elimination emits the same expression on every run.

## What the run checks

1. **Ground truth.** The printed Weis 2011 p.115 expression
   `(ab*a | ba*b(ab*a)*ba*b)*` is compiled by exact subset construction and
   Moore minimization, and asserted equal to the six-state walk automaton of
   `a = (0 1)(3 4)`, `b = (0 2 3 5)` with `start = accept = v0`. Nothing
   downstream depends on a hand-entered automaton.
2. **Letter-labelled `L2`.** The minimal DFA of `L2`, viewed as an
   SF-automaton, has cycle rank exactly 2 (exhaustive vertex-deletion
   recursion, no heuristics), and state elimination returns a star-height-2
   expression proved language-equal to `L2` by product reachability.
3. **The four-diagonal graph.** Cycle rank exactly 1 after absorbing the two
   `a`-self-loops into the incoming edges via the star-free `a* = ¬(⊤b⊤)`.
   For both anchors `D2` and `D3`, the eliminated first-return language and
   all three escape languages are asserted star-free (syntactic height 0) and
   proved language-equal, by DFA equivalence, to the expressions printed in
   `notes/weis_l2_full_height_one.md` §3. This is a check of the published
   note by an independently written eliminator, not a re-print of it.
4. **The eight anchor-walk atoms.** For `d ∈ {D2, D3}` and each of the four
   diagonals `x`, the automaton `(graph, start = d, accept = x)` has cycle
   rank 1, eliminates to star height ≤ 1, and is proved language-equal to the
   exact four-state diagonal walk DFA.
5. **The two parity atoms.** `even_a` and `even_b` are built as rank-1
   SF-automata (the filler letter absorbed into the incoming edges of every
   residue state) and proved language-equal to the corresponding word-problem
   DFAs of `tools/targets.py`.
6. **The rank bound is re-checked everywhere.** `SFAutomaton.to_expression`
   compares the syntactic star height of its own output against the cycle
   rank on every call and raises on violation, so Theorem 2.1 of the note is
   exercised by each of the items above and by every case in
   `tests/test_sf_automaton.py`.

## Emitted certificates

| Path | Language | Verdict from `scripts/ci/check_certificate.py` |
|---|---|---|
| `data/certificates/height1_weis_l2_anchor_atom.json` | `K_{D2} = (R_{D2})*`, the anchor-walk atom | `PASS: equivalent; height=1 <= 1; minimal states expression=4, target=4` |
| `data/certificates/height1_z3_sf_automaton.json` | `{ w : \|w\|_a ≡ 0 mod 3 }` | `PASS: equivalent; height=1 <= 1; minimal states expression=3, target=3` |

Both are re-verified by `tools/regex_cert.py` (`CERT-01`), an implementation
independent of `tools/sf_automaton.py`, on every run of `./scripts/check.sh`.

## Verdict

    rank 1 SF-automaton  ⟹  gsh ≤ 1                       (unconditional)
    r_SF(L2) ≤ 2                                          (measured)
    L2 ∈ BoolComb(rank-1 SF-automata)                     (all 4 atom families certified)

## Known gaps

- **No lower bound.** No rank-1 SF-automaton for `L2` is known, but the labels
  range over all star-free languages, so this is a search result and never a
  star-height lower bound (README research rule 1). In particular
  `r_SF(L2) = 2` is **not** claimed.
- `r_SF` is not claimed to be computable; minimizing over all star-free
  labellings is an infinite search.
- The self-loop absorption used for the diagonal graph is checked by hand
  here (the closure `a*` of the loop label `a` is supplied literally);
  `tools.sf_automaton.check_closure` exists to verify such a pair exactly and
  is exercised by the unit tests, not by this script.
- The rank-2 → rank-1 collapse question (`SFA-CORE2-RANK-01`) rests on the
  external `CORE2-EQV-EXT-01`, which is `UNREVIEWED` in this repository.
- Prior-art search done 2026-07-25 (`M-SFA-PRIOR-001`, now `DONE`):
  `SFA-EGGAN-01` has **no new mathematical content**. The index bookkeeping
  for automata labelled by expressions is Sakarovitch, arXiv:1502.03573 §3.6,
  eqs (3.24)–(3.26) with Property 3.12 and Prop. 3.13 (Lombardy–Sakarovitch
  2003) and Thm. 3.11 (Eggan 1963), and the bound is in fact an equality over
  elimination orders. The *generalized*-star-height reading, which this
  manifest previously credited to the repository, is PST 1992 Thm. 4.6
  (p.229f). And `r_SF` is Hashiguchi's relative star height (1988, Def. 2.6)
  over star-free bases: `r_SF(L) = min over finite 𝒞 ⊆ SF of h_r(L, 𝒞)`.
  What this run establishes is therefore the *measurements* and the
  machine-checked packaging, not a theorem.
- Consequence not yet exploited: `h_r(·, 𝒞)` is decidable for each fixed
  finite base (Hashiguchi 1988; complexity in Kirsten 2011), so item 2 above
  could be upgraded from "no rank-1 automaton found" to a decided value over
  the specific base used here. Registered as `M-SFA-DECIDE-001`; still not a
  gsh lower bound, since the minimum over all of `SF` stays infinite.
- Program audit and independent human re-derivation pending
  (obligation `N-SFA-AUDIT-001`).
