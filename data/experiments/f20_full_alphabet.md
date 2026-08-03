# Run manifest: F_20 full 20-letter alphabet — negative result

Claim: `F20-FULL-OBS-01` (`COMPUTED`, negative).
Obligation: refines `N-F20-001`; `HeightOneForGroup F_20` stays OPEN.

Derivation: `notes/f20_full_alphabet_obstruction.md`, `RESULTS.md` §5.12.
Base commit: `0cf5cd9` (on `feature/f20-word-problem`).

## Command

```bash
python3 scripts/research/f20_full_alphabet.py
```

Python standard library only.  Runtime 0.1 s.  Python 3.14.6, macOS
(darwin 25.5.0), single process, no network.

## Hashes

| Artifact | sha256 |
|---|---|
| `scripts/research/f20_full_alphabet.py` | `aaf740679964d338a092fbb72147b4cea99b08d132b96aacd8f4c9a5a982e4f0` |
| stdout of the run | `eaa2c3060765cb5b1aee49352ecf1ac507ce57cb200906d45c1204f31be26c35` |

## What the run establishes

1. **Setup.** 20 letters, 5 non-movers (`eps = 0`), 15 movers; the coordinate
   formula `alpha = 2^{sum eps}`, `beta = sum_i beta_i 2^{E_i}` is verified
   exhaustively for length <= 3 (8421 words) and on 20000 fixed-seed words of
   lengths 4..8.
2. **Aperiodicity table (exact, by full transition-monoid enumeration).** All
   291 candidate cut patterns of the `RESULTS.md` §5.5 scheme (1 base, 20
   single, 270 pair) **fail**: certified = 0/291.  Every failure has period 2
   with witness `g(eps=2, beta=0)`.
3. **Localization, and a positive control on the judge.** Restricting the
   alphabet by `eps`-class: `{0,1}`, `{0,2}`, `{0,3}` and the 15-letter
   `{0,1,3}` all **CERTIFY**; `{0,1,2}`, `{0,2,3}` and the full `{0,1,2,3}`
   fail.  So the judge is not trivially answering "not aperiodic", and the
   obstruction lies exactly in the five `eps = 2` letters — and only when they
   coexist with odd-`eps` letters.
4. **Cause.** The phase group `Z/4` is composite: an `eps = 2` letter has phase
   orbit `{0,2}`, a proper subgroup, so from an odd phase it bounces
   `1 <-> 3` forever without meeting the cut phase 0.  In `A_4` the phase group
   is `Z/3`, where every non-zero `eps` generates the whole group, so this
   failure mode cannot arise; the `A4-FULL-01` mechanism silently relied on the
   phase group having prime order.
5. **The linear algebra is not the bottleneck.** Formally assuming the
   uncertified staged features, the GF(5) systems have rank 8/8 (`eps=1`), 7/8
   with a beta-neutral null direction (`eps=2`), 8/8 (`eps=3`) — beta would be
   determined.  With only soundly certified features the rank is 20/80, 21/80
   after adding the beta row.

## Verdict

The planned transposition of the `A_4` multi-mover mechanism to `F_20` **does
not close**, and the reason is identified and localized.  This is a negative
result, recorded as such.

## Known gaps and cautions

- This is **not** a lower bound: it does not show the full-alphabet language has
  height > 1 (research rule 1).  It shows one known mechanism does not apply.
- The `F20-STD-01` two-generator result is unaffected (only one letter moves the
  phase there).
- The script's "minimal obstruction witness" (two length-4 words, `mu = (1,3)`
  vs `(1,0)`) is **weak evidence and must not be over-reported**: the two words
  have the *same letter multiset*, so it only shows that count-level features do
  not determine beta, which was expected.  The substance is items 2-4.
- Implementation was delegated to Sakana Fugu (`codex exec --profile fugu-ultra`)
  from a caller-written plan.  The reviewing agent independently recomputed the
  witness pair, added the localization/positive-control experiment (item 3), and
  supplied the structural explanation (item 4), which the delegated run did not
  identify beyond naming the witness letter.
