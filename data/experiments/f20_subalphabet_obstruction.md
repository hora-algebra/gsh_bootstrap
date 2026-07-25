# Run manifest: F_20 sub-alphabets — the 5.5 mechanism does not separate mu

Claim: `F20-SUB10-OBS-01` (negative).
Obligation: refutes route (ii) of `N-F20-001`; `HeightOneForGroup F_20` stays OPEN.

Derivation: `notes/f20_subalphabet_obstruction.md`, `RESULTS.md` §5.13.
Base commit: `19d33ff` (on `feature/f20-word-problem`).

## Command

```bash
python3 scripts/f20_subalphabet_obstruction.py
```

Python standard library only. Runtime 12.4 s. Python 3.14.6, macOS
(darwin 25.5.0 / macOS-26.5.2-arm64), single process, no network.
Imports `scripts/f20_full_alphabet.py` for the group, the coordinate formula, the
token DFA and the transition-monoid enumerator; ground truth for the group element
is that module's direct evaluator `evaluate`, not the coordinate formula, so no
formula is trusted here.

## Hashes

| Artifact | sha256 |
|---|---|
| `scripts/f20_subalphabet_obstruction.py` | `12213d2d4fb58e68effa88886319f1dd57275696b55eed21feaa8a52d1d908f0` |
| stdout of the run | `c2809a3b163da116e32088a1e0c62c41eba15491de8f53fd43b1d047c7816448` |

## What the run establishes

1. **Complete certified pattern table** (exact, by full transition-monoid enumeration,
   *including* same-letter pairs, which `f20_full_alphabet.candidate_patterns()` omits).
   On `eps in {0,1}` (10 letters): base and single-nonmover certify, and **every** pair
   pattern fails (period 2, or 4 for same-letter pairs). On `eps in {0,1,3}` (15 letters):
   base, single-nonmover and the 50 pairs with `(eps_h, eps_g)` in `{(1,3),(3,1)}` certify.
2. **Exhaustive mu-collision search** over the certified feature family closed under
   reversal: collisions exist on both sub-alphabets, and the shortest is at length 4
   (verified by searching each length in turn — 1,765 words for 10 letters, 5,045 for 15).
3. **The canonical witness with each clause of the hand proof machine-checked**:
   `w0 = k u0 u1 k`, `w1 = k u1 u0 k` with `k = g(eps=0,beta=0)`, `u0 = g(eps=1,beta=0)`,
   `u1 = g(eps=1,beta=1)`. Identical eps sequence, phase trajectory, arrivals per phase,
   nonmover counts per phase, letter multiset, first and last letter, total phase, and
   identical full feature vectors in both directions — while `mu(w0) = (4,1)` differs from
   `mu(w1) = (4,2)`.
4. **Route (ii) of `N-F20-001` is refuted**: the same witness uses no `eps = 3` letter, so
   the pair patterns the 15-letter alphabet does certify never fire on it; the feature
   vectors still agree there.
5. **Generosity check**: granting every `Sum-eps = 0` suffix pattern up to length 3 whose
   aperiodicity is *not* certified (5 extra on 10 letters, 555 on 15) does not remove the
   collision. The mechanism is handed more than it has earned and still fails.
6. **Positive control**: on the 2-generator alphabet of `F20-STD-01` the same feature
   family *does* separate `mu` (8,191 words of length ≤ 12, zero collisions) — because the
   single-nonmover cut yields `N_q` directly there. So the judge is not vacuous and the
   negative results above are not an artifact of an over-restricted feature set.

## Verdict

The pattern-conditioned-cut mechanism of `RESULTS.md` §5.5 cannot decide the `F_20`
full-alphabet word problem, and the reason appears already on a 10-letter generating
sub-alphabet, independently of the `eps = 2` letters identified in `F20-FULL-OBS-01`.
Recorded as a negative result.

## Known gaps and cautions

- This is **not** a lower bound: nothing here shows any of these languages has
  generalized star height greater than 1 (research rule 1). It bounds one mechanism.
- `F20-STD-01` (two generators, §5.11) is unaffected — see item 6.
- `F20-FULL-OBS-01` is **not corrected** by this run; its `eps = 2` localization concerns
  the aperiodicity of the base cut and remains valid. Only its recommendation of route
  (ii) as promising is refuted.
- A general law "Sum-eps ≡ 0 (mod 4) iff certifiable" was considered and **refuted** by a
  synthetic experiment over phase groups `Z/3` (13 of 16 pairs certify) and `Z/5` (31 of
  36), where patterns with `Sum-eps ≠ 0` certify freely. The agreement seen on the
  15-letter table is a fact about the eps-multiset `{0,1,3}`, not a law. That synthetic
  probe is exploratory and is not part of this script; the script depends only on the
  exact table of item 1.
- Written and verified without delegation, per the reviewing agent's own measurement that
  delegating design-bearing work cost more than doing it directly (`~/.claude/rules/`).
