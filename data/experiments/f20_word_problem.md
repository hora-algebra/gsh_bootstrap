# Run manifest: F_20 two-generator word problem, gsh = 1

Claims: `F20-STD-01` (`COMPUTED`), `WATOM-45-01` (`COMPUTED`).
Obligation: partial progress on `N-F20-001` (the full 20-letter alphabet, i.e.
`HeightOneForGroup F_20`, is **not** settled by this run).

Derivation: `RESULTS.md` §5.11.  Base commit: `6bc9e13` (merge of PR #27).

## Commands

```bash
python3 scripts/research/f20_word_problem.py
python3 scripts/research/f20_word_problem.py --certificate data/certificates/height1_f20_word_problem.json
python3 scripts/ci/check_certificate.py data/certificates/height1_f20_word_problem.json
```

Python standard library only.  The regex AST, recursive matcher, exact DFA
compiler, minimizer, equivalence checker and certificate translator are imported
from `scripts/research/weis_l2_full_gsh1.py` rather than reimplemented.

## Environment

- Python 3.14.6, macOS (darwin 25.5.0), single process, no network.
- Wall clock: 4.1 s without the certificate, 5.4 s with it.
- Largest intermediate object: the compiled DFA of the atom assembly.

## Hashes

| Artifact | sha256 |
|---|---|
| `scripts/research/f20_word_problem.py` | `06b9bf73eb9aad9a54e6fd859ad519cc42aad07b0fbce536a70373ef4fa52274` |
| `data/certificates/height1_f20_word_problem.json` | `876ef23aa7eface7ac59cc9d33aff0ac8def36eb87225162d1dba4c43fd1f704` |
| stdout of the plain run | `cb40168b1c779e5feb4341e36a1d88921d8463b72651d6b393e49deac7f3c4e6` |

Deterministic: no randomness, no sampling, no dictionary-order dependence.

## What the run checks

1. `<phi(a), phi(b)>` has order 20 with `order(phi(a)) = 5`,
   `order(phi(b)) = 4`; the closed coordinate formula
   `alpha = 2^{|w|_b}`, `beta = sum_a 2^{(b's after)}` agrees with direct
   composition on all 8191 words of length <= 12.
2. The arithmetic characterization
   `L = { |w|_b = 0 mod 4 and N_0 + 3N_1 + 4N_2 + 2N_3 = 0 mod 5 }`
   agrees with `phi(w) = identity` on all 32767 words of length <= 14
   (exhaustive).
3. `height(E) = 1`; all 20 W-atoms and the transparent assembly have height 1.
3b. **Each** of the 20 W-atoms equals `{ w : N_r = h mod 5 }`, checked by the
   compiled DFA on all 8191 words of length <= 12 and by the independent
   recursive matcher on all 511 words of length <= 8.  This is what validates
   the *construction* rather than only the final language.
4. The compact expression compiles and minimizes to exactly 20 states.
5. It is language-equal to the 20-state `F_20` word-problem DFA, proved by
   complete product reachability (no sampling).
5b. The transparent W-atom assembly independently minimizes to 20 states and is
   equivalent to the same target, so the compact form is only a size
   optimization for the certificate.
6. The recursive matcher, the compiled DFA, and direct evaluation in the group
   agree on all 511 words of length <= 8.
7. The emitted certificate is verified by the separate implementation
   `tools/regex_cert.py` via `scripts/ci/check_certificate.py`:
   `PASS: equivalent; height=1 <= 1; minimal states expression=20, target=20`.
   `./scripts/check.sh --static` picks it up on every run.

## Verdict

Upper bound: gsh <= 1, by a complete finite proof.
Lower bound: the minimal DFA is the 20-state Cayley automaton of `F_20`, so the
syntactic monoid is the group `F_20`, which is not aperiodic; by Schützenberger
1965 the language is not star-free, i.e. gsh >= 1.  Hence **gsh = 1 exactly**.

## Known gaps

- This is one morphism (`a -> x+1`, `b -> 2x`) and one accepting set
  (`{identity}`).  It does **not** prove `HeightOneForGroup F_20`; by
  `FULL-ALPH-RED-01` that is equivalent to the identity fibre over the full
  20-element alphabet, which is a separate and harder problem (the analogue of
  `A4-FULL-01` for `A_4`).  `F_20` therefore remains listed as open in
  `FRONTIER-ORD20-01`.
- Program audit and independent human re-derivation are pending.
- The construction was drafted by a delegated agent (Sakana Fugu via
  `codex exec`) from a caller-written plan; checks 3, 3b and 5b were added by
  the reviewing agent because the delegated version validated only the
  assembled language, not the individual atoms.
