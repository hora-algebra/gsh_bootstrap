# Run manifest: C_7⋊C_3 full 21-letter alphabet — positive result

Claim: `C7C3-FULL-01` (`COMPUTED`, positive).
Obligation: advances `N-C7C3-001`; `HeightOneForGroup (C_7⋊C_3)` stays OPEN
(no height-one regular expression has been compiled).

Derivation: `notes/c7c3_full_alphabet.md`, `RESULTS.md` §5.13.
Base commit: `19d33ff` (on `feature/c7c3-full-alphabet`).

## Command

```bash
python3 scripts/c7c3_full_alphabet.py --exhaustive-length 4 --sweep 40000
```

Python standard library only.  Runtime 53.2 s.  Python 3.14.6, macOS
(darwin 25.5.0), single process, no network.  The default invocation
(`--exhaustive-length 3 --sweep 20000`, 23.3 s) checks the same sections on a
smaller word set and is the quick regression form.

## Hashes

| Artifact | sha256 |
|---|---|
| `scripts/c7c3_full_alphabet.py` | `241c0f9436d733f136c063f8b2e80e6652bffa151e7359bd208ca608764eb368` |
| stdout of the run | `dfcca27d84920ba698ebbce9e9edee926d61bbc25656dc8f53e3c15ed4c39a44` |

## What the run establishes

1. **The group is right.** 21 elements, closure/associativity/identity/inverses
   checked exhaustively, non-abelian, and the presentation
   `<x, y | x^7 = y^3 = 1, y x y^-1 = x^2>` verified with `<x,y>` equal to the
   whole group.  21 letters, 7 non-movers (`eps = 0`), 14 movers.  The
   coordinate formula `alpha = 2^{sum eps}`, `beta = sum_i beta_i 2^{E_i}` holds
   on all 9724 words of length <= 3 and on 20000 fixed-seed words of length 4..8.
2. **Aperiodicity table (exact, by full transition-monoid enumeration).** All
   **288 / 288** candidate cut patterns of the `RESULTS.md` §5.5 scheme
   (1 base, 7 single, 280 pair) are aperiodic.  8 distinct DFA types, minimal
   states 5–6, monoid orders 23–61.
3. **Positive control on the judge.** The 14 excluded same-letter pure-power
   patterns (`g -> g`) are all **NOT** aperiodic (period 3, witness
   `g(e=1,b=0)`).  So the 288 OK rows are not the output of a judge that always
   answers yes.  This mirrors the A_4 behaviour recorded in `RESULTS.md` §5.5.
4. **Feature identities.** 404032 exact/sweep comparisons between the
   incrementally computed features and a direct `CutPattern.run` replay agree.
5. **GF(7) system.** Rank 6/6 for both mover classes; the beta functional is
   solved as `6·F1 + 4·F2 + 1·B0 + 3·B1` (`eps=1`) and
   `5·F0 + 4·F2 + 3·B0 + 2·B1` (`eps=2`), each independently re-checked on 5000
   random `(x,n)` vectors (0 mismatches) rather than trusted from the
   elimination that produced it.
6. **End-to-end reconstruction.** The certified features predict membership in
   the identity fibre correctly on all **204205** words of length <= 4 and on
   40000 fixed-seed words of length 5..400.
7. **Negative controls.**
   - Membership base rate 9725/204205 = 4.76 % exhaustive, 4.70 % sweep
     (theoretical 1/21 = 4.76 %), so item 6 is not a near-constant predicate
     being matched by a constant predictor.
   - All **84** single-coefficient perturbations of the solved combinations
     break the reconstruction; 0 survive.  Item 6 is sensitive to the
     coefficients.
   - Phase, endpoints and letter counts mod 7 alone do not separate the fibre
     (an explicit length-4 witness pair), so the pair/single cuts are load-bearing.

## Verdict

The `A_4` multi-mover mechanism transposes to the **full alphabet** of
`C_7⋊C_3` without modification, and the identity fibre is reconstructible from
certified features on every word tested.  This is the first full-alphabet
positive result for a group in the `FRONTIER-ORD20-01` exception list.

It also **retests the diagnosis of `F20-FULL-OBS-01`** on an independent group:
the same code path returns 0/291 for `F_20` (composite phase group `Z/4`),
56/146 for the 15-letter `F_20` sub-alphabet, and 288/288 here (prime phase
group `Z/3`).  Three different answers from one judge.

## Known gaps and cautions

- **Not a proof.** No height-one regular expression was constructed or compiled,
  and no language equivalence was proved — unlike `F20-STD-01` and
  `WEIS-L2-GSH-01`, where a product-automaton equivalence check was run.
  Agreement on finitely many words is not language equality.  `N-C7C3-001`
  stays OPEN.
- Exhaustive coverage stops at length 4; length 5 is 4.08 M words.
- The certified-feature suite uses letter counts mod 7, which are height-one but
  **not** star-free; that is by design (the scheme applies one level of star to a
  star-free token language) and is the same convention as `A4-FULL-01`.
- Implementation was written directly, not delegated
  (`~/.claude/rules/codex-delegation.md`: design-bearing work stays in-house).
  The port from `scripts/f20_full_alphabet.py` generalizes the three places
  where the width `2·PHASES` was hard-coded to 8, and replaces the F_20-specific
  `localize_obstruction` with the section-6 controls.
