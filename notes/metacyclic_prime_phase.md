# The prime-phase metacyclic family, and what running it does not give

Ledger rows: `C13C3-FULL-01`, `C11C5-FULL-01`, `C19C3-FULL-01` (all
`EMPIRICAL`), and the evidence they add to `FAMILY-A-PRED-01` (`CONJECTURAL`).
Program: `scripts/research/metacyclic_full_alphabet.py`. Manifest:
`data/experiments/metacyclic_prime_phase.md`. Obligation: `N-FAMILY-A-001`.

## 1. Why these groups, and why together

`FAMILY-PHASE-01` sorted the 24 remaining problems of `COVER-LE59-01` by phase
group. Family A — a split extension of an abelian group by a cyclic group of
**prime** order — contains seven groups, and four of them are the metacyclic

    F_{p,q} = C_p : C_q,   q prime,  q | p - 1,

with `C_q` acting as the order-`q` subgroup `<r>` of `(Z/p)^*`:

| group | order | p | q | r | `<r>` |
|---|---|---|---|---|---|
| `C_7 : C_3` | 21 | 7 | 3 | 2 | 1, 2, 4 |
| `C_13 : C_3` | 39 | 13 | 3 | 3 | 1, 3, 9 |
| `C_11 : C_5` | 55 | 11 | 5 | 3 | 1, 3, 4, 5, 9 |
| `C_19 : C_3` | 57 | 19 | 3 | 7 | 1, 7, 11 |

`scripts/research/c7c3_full_alphabet.py` ran the multi-mover mechanism of
`RESULTS.md` §5.5 on the first of these, hard-coded to `MODULUS = 7`,
`PHASES = 3`, `POWERS_OF_TWO = (1, 2, 4)`. Those three constants are exactly
`p`, `q` and `<r>`, so the mechanism generalizes by substitution and by nothing
else. No new mathematics is introduced here; that is the point, and it is what
makes the result interpretable.

## 2. The two controls, which are the reason to believe the runs

**Positive control — the generalization must reproduce the original.** Run at
`(7, 3)` the new program must agree with `c7c3_full_alphabet.py` line for line.
It does: every result line of the original output is reproduced exactly, and the
only differences are two new header lines, one new cross-check line, the
concluding sentence, and the runtime. A generalization that had drifted would
show up here first, on the one instance whose answer is already recorded.

**Negative control — the generalization must still fail on `F_20`.**
`F20-FULL-OBS-01` establishes, `COMPUTED`, that this mechanism fails on
`F_20 = C_5 : C_4`: all 291 candidates break aperiodicity, and the obstruction
is that the phase group `Z/4` is composite, so the `eps = 2` letters have phase
orbit `{0, 2}` and never meet the cut phase. `F_20` is in range of the same
parameterization at `(p, q) = (5, 4)`, where `q` is not prime.

Running it there yields `exact total=291; certified=0; failed=291`, exit status
1, and `witness=g(e=2,b=0)` with `period=2` on all 14 signatures — the recorded
localization, reproduced.  (The letter is written `g(e=2,b=0)` because that is
what the program prints; `eps` and `beta` are the names this note uses for the
same two coordinates.) **A pass here would have been a bug and not a breakthrough**, and
saying so before the run is what makes the run informative. The prime-phase
successes and the composite-phase failure now come out of one program rather
than two, so the phase-group distinction is a property of the mechanism rather
than of two independent implementations.

The mechanism's own internal controls are preserved and all fire: same-letter
pure-power patterns must FAIL and do, for every group including the successes;
every solved coefficient is mutated and every mutation breaks the
reconstruction, with no survivors; the membership base rate is reported so that
a near-constant predicate cannot pass by triviality; and a pair of words that
letter counts alone cannot separate is exhibited.

## 3. What the runs establish, and what they do not

For each of the three new groups the program decides, **exhaustively and with
no length bound**, that every candidate pattern-conditioned cut is aperiodic —
each candidate's transition monoid is enumerated completely — and that the
`GF(p)` system has full rank, so the `beta` functional is determined by the
certified features.

The reconstruction of the identity fibre used to be checked on words up to
length 3 plus a sample, and that sample was what capped every row. Section 7
replaces it with a decision: the product of the certified-feature machine with
the group element is traversed by BFS, and membership is checked to agree at
**every reachable state** — 442 for `C_7 : C_3`, 1522 for `C_13 : C_3`, 3026
for `C_11 : C_5`, 3250 for `C_19 : C_3`. Every word lands in some reachable
state, so agreement there is agreement on every word, with no length bound.
This is the recipe `PROOF_OBLIGATIONS.md` records under `L-A4-001`, in the
style of `prove_function` in `scripts/research/weis_l2_family.py`.

Its brittleness control fires: each solved coefficient is mutated and the BFS
re-decided from scratch, 84 / 168 / 440 / 252 mutations respectively, none
surviving. A BFS that accepted the claim and a false variant of it would have
tested nothing.

**The rows are still `EMPIRICAL`, and the reason is now one specific
comparison.** Section 7 decides a *machine* that computes the certified
features. That this machine is the same function as section 5's own
`prefix_beta_from_certified_features` is checked by section 7(c) — on words up
to a bounded length plus a sample. So the chain from the text of section 5 to
the fibre still has one sampled link, and by the ceiling rule the row is capped
there.

This matters and it is worth stating plainly rather than rounding off. A
complete traversal of an object whose identification with the claim is only
sampled is the shape of `THOMAS-D2-02`: the traversal was complete and the
object was the wrong one. Section 7 is not that — the machine provably computes
*something* that determines the fibre, and 7(c) is a real comparison rather than
an assumption — but until 7(c) is decided, the row cannot claim that section 5's
function is the decided one. `N-METACYC-TRANS-001` records what closing it
takes and why it is not free.

What is **not** done, and is the whole distance to a theorem:

- no height-one regular expression is constructed or compiled, as it was for
  the two-generator cases `A4-STD-01` and `F20-STD-01`;
- no language equivalence is decided;
- the transcription step 7(c) is sampled;
- therefore `HeightOneForGroup` is **not** established for any of the three,
  and none of them leaves the unresolved list of `COVER-LE59-01`.

The distance from here to a proof is the distance `A_4` had to travel: an
automaton whose states carry the observables independently, a complete
traversal of its reachable states, and an independent reimplementation. That
was one group's worth of work.

## 4. What this does to the prediction

`FAMILY-A-PRED-01` said the mechanism closes Family A. Before these runs it
rested on two instances, both sampled. It now rests on five, still all sampled,
with none failing — and with the composite-phase prediction confirmed in the
same program on the one group where the failure is already `COMPUTED`.

That is a better position and it is not a different kind of position. Five
`EMPIRICAL` rows are five leads. The two Family A groups not covered by this
parameterization have non-cyclic kernels: `(C_2)^3 : C_7`, where `C_7` acts as
multiplication on the additive group of `GF(8)` and the linear algebra stays
over a field, and `(C_4 x C_4) : C_3`, where the kernel is a `Z/4`-module and
the `GF(p)` solve of this program has no direct analogue.
