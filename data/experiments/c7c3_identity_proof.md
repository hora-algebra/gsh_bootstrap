# Run manifest: C_7⋊C_3 reconstruction identity — proved for all words

Claim: `C7C3-IDENT-01` (`PROVED`, positive).
Supersedes the sampling half of `C7C3-FULL-01` (`EMPIRICAL`).
Obligation: supplies the arithmetic half of the now-closed `N-C7C3-001`.
The separate token verdict and human composition are recorded in
`data/verdicts/c7c3_height_one.json` and `notes/c7c3_height_one.md`.

Derivation: `RESULTS.md` §5.16.1.
Base commit: `b3ef73c` (on `feature/c7c3-identity-proof`).

## Command

```bash
python3 scripts/research/c7c3_identity_proof.py --exhaustive-length 4 --sweep 4000
```

Python standard library only.  Runtime 2.5 s.  Python 3.14.6, macOS
(darwin 25.5.0), single process, no network.  The default invocation
(`--exhaustive-length 3 --sweep 4000`, 0.7 s) runs the same proofs on a smaller
cross-check set and is the quick regression form.  Sections 1–5 and control (a)
do not depend on either flag: they are exhaustive over state spaces, not words.

## Hashes

| Artifact | sha256 |
|---|---|
| `scripts/research/c7c3_identity_proof.py` | `595afc4ace6a723fc818ec97eb5b3c10ca235ebcb17bd70147bf180c9c3b2fa7` |
| stdout of the run | `24e502903d0c9e125a713b1a9cfb2b39cb3b1ef751bc1ec0346ad7d7b42f3f23` |

## What the run establishes

1. **A smaller certified family.**  The pattern `("anti", g)` — skip the cut at
   an arrival at phase q iff the letter is `g` and the previous letter is not
   `g` — is aperiodic for all **14 / 14** movers, and the three nonmover bit-set
   patterns `("set", S_k)` are aperiodic as well.  The family of conditioned
   cuts drops from 741 to **57 atoms**, because one `anti` pattern replaces the
   20 pair patterns the old scheme summed, and three bit sets replace six
   single-letter patterns (`sum_g beta_g N_g = sum_k 2^k N_{S_k}`).
2. **Both control families fail.**  `("single", g)` for a mover is not
   aperiodic (period 3, witness `g(e=1,b=0)`), and neither is `("antiset", S)`
   for a set of movers of one epsilon class (period 3, witness
   `g(e=1,b=1) g(e=1,b=3)` — two distinct same-class movers alternating skip
   forever).  The judge answers no when it should; this is why the family had
   to be enlarged in exactly this shape.
3. **Closed-form coefficients.**  `cF_p + cB_p = 2^p` and
   `cF_{p+eps} = cF_p - 2^p` are forced, a one-parameter family; the particular
   solutions that `scripts/research/c7c3_full_alphabet.py` reached by Gaussian
   elimination (`6F1+4F2+B0+3B1` and `5F0+4F2+3B0+2B1`) are recovered as the
   members with `cF_0 = 0` and `cF_0 = 5`.
4. **The run identity (\*).**  The second relation telescopes, so for a maximal
   run of a mover `g` of length L starting at prefix phase p,
   `cF_p + cB_{p+(L-1)eps} = sum_{j<L} 2^{p+j eps}` — the run's true
   contribution to `beta`.  Checked for all start phases and all lengths 1..18;
   the telescoping argument covers every length.
5. **`beta_prefix(u) = delta_total(u)` for EVERY word**, by complete BFS over
   the 64 reachable `(phase, previous letter, accumulator)` states.  Not a
   sample: every reachable state is an end-of-word state, and the accumulator
   is zero in all of them.
6. **Each atom is the count it is used as**, for all **45** statements
   `base_cut[q] - conditioned_cut[q] = the intended count`, each by complete
   BFS carrying *both* cut machines' private `previous` values — so the proof
   establishes, rather than assumes, that a cut's reset of `previous` is
   harmless.  The backward atoms are these same statements applied to the
   reversed word.
7. **The fibre characterization for EVERY word**: `nu(u) = e` iff
   `phase(u) = 0` and `delta_total(u) = 0`, by complete BFS over the 442
   reachable `(group element, previous letter, accumulator)` states.  (`nu` is
   the right-to-left product, i.e. `mu` of the reversal; reversal preserves
   generalized star-height.)  That 442 = 1 + 21·21 is itself a consistency
   signal: the search discovered that the accumulator is a *function* of the
   group element, which is what the identity asserts.
8. **End-to-end cross-check** against the actual `Cut.run` values on all
   **204205** words of length ≤ 4 (68069 of total phase 0, 9725 in the fibre)
   and 4000 fixed-seed sweep words of length 5..200.
9. **Negative controls.**  All 72 single-coefficient perturbations of `cF`/`cB`
   break the section-3 proof (0 survive); dropping the repeat correction breaks
   the reconstruction on 156 words of length ≤ 3; all 57 single-term
   perturbations of the assembled combination break it already at length ≤ 2;
   membership base rate 9725/204205 = 4.76 % (theoretical 1/21 = 4.76 %), so a
   constant-False predictor would score 95.2 % and item 8 would be
   uninformative without it.

## Verdict

The arithmetic half of the `C_7⋊C_3` argument is now a **theorem about all
words** rather than an observation up to length 4.  `C7C3-FULL-01` verified the
reconstruction on 204205 + 40000 words; this run proves it on Σ\*.

## Scope and cautions

- **This run alone is not the height-one proof.**  It proves that the identity
  fibre is a Boolean combination of residue languages of 57 cut counts.  The
  first/post-cut token aperiodicity and exact mod-seven factorization are the
  separate `C7C3-H1-FINITE-CORE-01` (`COMPUTED`); Schützenberger's theorem and
  the closure/reversal/full-alphabet composition are written in
  `notes/c7c3_height_one.md`.  Those inputs together close `N-C7C3-001`.
- The exhaustive word check stops at length 4; sections 1–7(a) do not depend
  on it.
- `scripts/research/c7c3_full_alphabet.py` is imported but not modified, so the hashes
  recorded in `data/experiments/c7c3_full_alphabet.md` remain valid.  Its
  `CutPattern` does not know the new pattern kinds, so the cut semantics is
  re-implemented here; section 1 checks the two agree on all 288 old patterns,
  all 3 entries, 663 words.
