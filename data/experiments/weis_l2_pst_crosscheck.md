# Run manifest: anchoring L2's ground truth to PST 1992 §8

Claim: `WEIS-L2-PST-SRC-01` (the expression this repository compiles denotes the
language Pin–Straubing–Thérien 1992 §8 proposed).

- date: 2026-07-28
- base commit: 2f0a22b
- environment: Python 3 stdlib only, macOS (darwin 25.5.0), CPython 3
- resource bound: < 3 s, product automaton of 36 reachable pairs, plus a
  131,071-word cross-evaluation of the two encodings

## Why this run exists

Every earlier evaluation path for L2 — `compile_dfa`, the recursive matcher,
Python `re` — starts from the **same printed string**. Three agreeing paths over
one input do not check the input. A transcription error in that string would
have produced a fully consistent, fully wrong result, and the row would have
been about a language nobody proposed.

## Primary source

    https://www.irif.fr/~jep/PDF/StarHeight.pdf   (preprint, 31 pp., p.29)

retrieved 2026-07-28 with `curl -sL -A "Mozilla/5.0 …"`. `WebFetch` and the HAL
and ScienceDirect copies return 403 / an anti-bot page, which is why several
ledger rows carried a "full text unobtained" caution; this run closes it.

Verbatim, §8 "Further results":

> Unfortunately, it is even not known whether there exist languages of
> star-height greater than or equal to 2! A possible candidate is
> L = (ab\*a ∪ ba\*b(ab\*a)\*ba\*b)\*.
> Notice that if A is the automaton represented on Figure 6, then
> L = {u ∈ A\* | 0·u = 0 and |p(u)|₍₀,b₎ ≡ 0 mod 2}.

## The reconstruction, and its status

Figure 6 is a drawing; PDF text extraction yields only the loose labels
`b a 2 a 0 1 b a b`, which do not determine the arrows. The transition table is
therefore **reconstructed**, not read, from the two constraints that fix it —
the state set is {0, 1, 2}, and PST's condition must denote the printed
language:

    a : 0 ↔ 1, 2 fixed        b : 0 ↔ 2, 1 fixed        transition monoid S₃

Under it `a b* a` runs 0→1→1*→0 using the arrow (0,b) zero times and `b a* b`
runs 0→2→2*→0 using it once, so every generator of the printed star returns to 0
with an even (0,b) count — which is what PST assert.

The reconstruction is what the controls constrain. It is an inference, and it is
labelled as one wherever it appears.

## Commands

    python3 scripts/research/weis_l2_pst_crosscheck.py
    # also run by ./scripts/check.sh (fast tier of run_research.py)

## Result

    pst-figure-6 (exhaustive, 36 states, 5/5 controls fired)
    WEIS-L2-PST-SRC-01: ceiling COMPUTED

- the two descriptions are proved language-equal by **complete product
  reachability**, all 36 reachable pairs, no word bound, no sampling;
- the printed side is rebuilt through `re` residuals rather than the
  repository's own compiler, so this check shares no machinery with
  `weis_l2_full_gsh1.py`;
- independently, the two encodings agree on all 131,071 words of length ≤ 16;
- PST's (state, arrow-parity) pair has exactly 6 states — the same automaton
  `weis_l2_full_gsh1.py` derives from the printed regex, reached from the
  opposite end.

## Controls

| perturbation of Figure 6 | first disagreeing word |
|---|---|
| the b-arrow out of 0 is a loop, not 0 ↔ 2 | `bb` |
| b is the 3-cycle (0 2 1), not the transposition (0 2) | `ab` |
| b loops at 2 instead of returning to 0 | `bbbb` |
| a loops at 1 instead of returning to 0 | `aa` |
| the (0,b) arrow-parity clause is deleted | `bb` |

5/5 fired.

**Recorded because it was tried and did **not** fire**: swapping the roles of
`a` and `b`. That map is the state relabelling 1 ↔ 2 and denotes the same
language, so it tests nothing. It was removed from the control set rather than
kept as a passing check — a control that cannot fail is the defect this
repository keeps finding in its own gates, and the same rule applies when the
gate is one run.

## Scope

This run says **which language** is under discussion. It says nothing about its
height; that is `WEIS-L2-GSH-01`, and its trust boundary is in
`notes/weis_l2_review_packet.md` §5.
