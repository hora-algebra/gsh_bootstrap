# Run manifest: F_20 finite-code block decomposition — the delay theorem

Claims: `F20-BLOCK-OBS-01` (negative), `FULL-ALPH-RED-02` (reduction, by-product),
`F20-BASECODE-01` (negative, closes the residual route).
Obligation: refutes route (iii) of `N-F20-001`; `HeightOneForGroup F_20` stays OPEN.

Derivation: `notes/f20_block_decomposition.md`, `RESULTS.md` §5.14.
Base commit: `08fcd30` (merge of PR #30 into `main`).

## Command

```bash
python3 scripts/f20_block_decomposition.py
```

Python standard library only. Runtime 22 s. Python 3.14.6, macOS
(darwin 25.5.0 / macOS-26.5.2-arm64), single process, no network.
Imports `scripts/f20_full_alphabet.py` for the group, the coordinate formula, the
token DFA, the transition-monoid enumerator and the pattern table; ground truth for
every group element is that module's direct evaluator `evaluate`, never the
coordinate formula, so no formula is trusted here.

## Hashes

| Artifact | sha256 |
|---|---|
| `scripts/f20_block_decomposition.py` | `823aba3833b3bad129134bed4720c612ad480a2f5cf5607b2cb0bced8c3767a8` |
| stdout of the run | `e6a4259538ca87019b4fbe0baec6fc00c4c762e1f362546b573066328e5f46e9` |

(Recompute with `shasum -a 256 scripts/f20_block_decomposition.py` and
`python3 scripts/f20_block_decomposition.py | shasum -a 256`.)

## What the run establishes

1. **The block reduction is a change of alphabet and nothing more.** For the codes
   `Sigma^2` and `Sigma^3`, the token-level product and the §5.12 coordinate formula
   agree with the letter level on all 336,842 words of length at most 4. The token
   level of a block decomposition is again a word problem for `F_20` over an alphabet
   of group elements.
2. **The delay theorem, in both forms.** For every one of the 20 elements `z`, all
   nonempty prefixes of `z e^n` have image `z` (`n <= 21`); and for every `z != e`,
   the word `z e^n z^{-1}` lies in the fibre `T` while all of its proper nonempty
   prefixes have image `z`. So a finite code missing `z` cannot parse `Sigma*`, and
   cannot parse `T` either.
3. **Exhaustive form of the same statement.** All 20 maximal proper token images are
   unrealizable on the full alphabet and the full image is realizable, so
   `mu(X) = F_20` for every finite bounded-delay code. Reduced from "all proper
   images" by a verified monotonicity check (190 inclusion pairs).
4. **The realizability criterion, cross-checked two ways.** A graph criterion on the
   image walk and direct enumeration of the code-free set agree on all 63 tested
   (alphabet, image) pairs, with zero disagreements; every realizable case is
   witnessed by an explicitly constructed frontier code whose prefix-code property,
   bounded delay and token image are all verified. The enumeration cutoff `|G| + 1`
   is a proof, not a sample: a code-free word that long repeats an image.
5. **Nothing certifies at the token level.** With `mu(X) = F_20` the base cut has a
   period-2 element (`g(e=2,b=0)`) and 0 of the 291 candidate patterns certify — the
   `F20-FULL-OBS-01` obstruction verbatim, one level up. Token multiplicity does not
   repair it: on the genuine 400-token alphabet `Sigma^2` (1,606 DFA states) a single
   `eps = 2` token still has period 2.
6. **The phase-neutral variant, which is what route (iii) actually wanted, does not
   exist.** `u h^n` keeps every prefix phase in `{1,3}`, so no phase-neutral word is a
   prefix; `h e^n` keeps every prefix phase at 2. The one canonical phase-neutral code
   is the first-return code `R`, and it fails twice over: it is infinite (13 return
   words of distinct lengths 3..15 exhibited) and it is not star-free (its DFA *is*
   the §5.5 base cut, period 2).
7. **Identity-letter erasure is legitimate but does not help** (`FULL-ALPH-RED-02`).
   `mu(w) = mu(pi(w))` on all 8,421 words of length at most 3; the concatenation step
   `pi^{-1}(L1 L2) = pi^{-1}(L1) pi^{-1}(L2)` holds on 9,837 instances; the star step
   `pi^{-1}(A*) = (B u {e})*` holds on all 3,280 words for 4 test codes. On the
   resulting 19-letter alphabet, however, no token image of size 18 is realizable
   (190 cases) while all 20 of size 19 are, so `|mu(X)| >= 19` and the base cut still
   has period 2.
8. **Positive control.** On the 2-generator alphabet of `F20-STD-01` finite
   bounded-delay codes with a *proper* token image do exist: minimum image size 2
   (the trivial code), and 4 when length-1 tokens are forbidden, realized by
   `X = Sigma^2` with tokens of length exactly 2. The full alphabet admits no image of
   size at most 3. The judge is therefore not answering "unrealizable" by default, and
   the theorem is specific to the alphabet that contains the identity element.

9. **The residual route is decided, and was never viable** (`F20-BASECODE-01`).
   `T` is biunitary on all words of length at most 4 (8,422 fibre words), hence a free
   submonoid, so its base code is unique; that base is the first-return code, checked as
   `T` minus the products of two nonempty fibre words (7,240 words agree exactly). So
   "is there a star-free *code* `C` with `C* = T`?" is a single decision problem, and the
   answer is no: the minimal DFA of `R_T` has 22 states and the single letter
   `a = (x -> x+1)` has period 5 in its syntactic monoid. First established by full
   transition-monoid enumeration (20,971,502 elements on 20 letters, 294,881 on 2
   letters, max period 5 in both, ~5 min); the script carries an `O(states)` witness
   version of the same verdict. **Calibration**: the 2-generator alphabet, where
   `gsh(T) = 1` is proved by `F20-STD-01`, also returns "not star-free" — the condition
   is sufficient-only and fails where height one holds, so this route could never have
   been the mechanism.

## Verdict

For the full-alphabet instance every finite bounded-delay code has `mu(X) = G`, so
finite-code block decomposition reproduces the same instance one level up and
certifies nothing. Route (iii) of `N-F20-001` is BLOCKED. The statement of item 2 is
a three-line proof valid for every finite group, not a search over codes.

## Known gaps and cautions

- This is **not** a lower bound: nothing here shows any of these languages has
  generalized star height greater than 1 (research rule 1). It bounds one mechanism.
- `F20-STD-01` (two generators, §5.11) is unaffected — see item 8.
- **Not excluded**: non-greedy, two-sided or context-dependent factorizations; finite
  unions of case-split expressions with a different code per case; stripping the four
  non-identity `eps = 0` letters (erasure handles the identity letter only, since
  deleting any other letter changes the image). None is yet in the shape of a
  mechanism. The gap first registered here — star-free *infinite* codes — was closed
  the same day by item 9; for `C` not required to be a code (`R_T ⊆ C ⊆ T`) the
  question is formally undecided, with two data points only (`C = R_T`, and `C = T`
  whose syntactic monoid is the group `F_20`), but the calibration in item 9 removes
  the motive for pursuing it.
- **Correction recorded**: when this run was first written, star-free infinite codes were
  called "the most promising residue". That assessment was wrong, and item 9 is the
  refutation. The methodological lesson is registered in `PROOF_OBLIGATIONS.md`: test a
  proposed mechanism on the 2-generator alphabet, where height one is already proved,
  before spending effort on the full alphabet.
- `FULL-ALPH-RED-02` (item 7) is a hand proof with machine-checked steps 2 and 4. It
  brushes against the recorded caution that non-alphabetic inverse morphisms do not
  preserve height (PST 1992 item 7); the reason erasure is an exception is identified
  (step 2 is what fails for length-increasing morphisms), but the lemma is registered
  for independent audit rather than treated as settled folklore.
- Written and verified without delegation, per the reviewing agent's own measurement
  that delegating design-bearing work cost more than doing it directly.
