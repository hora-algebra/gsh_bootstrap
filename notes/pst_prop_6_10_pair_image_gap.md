# PST Proposition 6.10: pair-image gap

## Scope

Pin--Straubing--Thérien 1992 Proposition 6.10 is still a `CITED` theorem, and
Theorem 7.6 is still a `CITED` input to the mathematical small-group ladder.
This note isolates one equality in the printed proof that cannot be used
verbatim in Lean.  It does not refute either theorem's conclusion.

## Printed equality and counterexample

On p. 22, put `X = {aa, ab, ba, bb}` and let the morphism `φ` satisfy
`φ(a) = ab` and `φ(b) = ba`.  The proof prints

```text
Sφ = {u ∈ X* | |u|ab - |u|ba ≡ s (mod 2n)}.
```

For `s = 0`, take `u = aa`.  The word `aa` lies in `X*`, and its two signed
pair counts are both zero.  It therefore lies in the set on the right.  But a
length-two word in the morphic image `Sφ ⊆ {ab, ba}*` is either `ab` or `ba`,
so `aa ∉ Sφ`.  Thus the displayed equality is false as written.

The primary source is
<https://www.irif.fr/~jep/PDF/StarHeight.pdf>, Proposition 6.10, pp. 21--22.

## Formalized part and remaining repair

`GSH/Height/PairCode.lean` proves the preceding word-level arithmetic without
using the disputed equality:

- `GSH.PairCode.arrowCount_allFlip_zero_even`;
- `GSH.PairCode.count_false_eq_pairCounts`.

The immediate missing statement is `L-C2-PAIR-BAL-001`: on even Boolean words,
every modular residue of the fixed-pair balance `#ab - #ba` has generalized
star height at most one.  It is only one input to the flipping-edge case.
The full `S₃` consumer additionally needs the self-loop edge case, a corrected
argument admitting the neutral blocks `aa` and `bb`, transport from the
original six-letter alphabet, and source/final-state handling; these are
separated as `L-C2-ARROW-ID-001`, `L-C2-ARROW-FLIP-001`, and
`L-C2-ARROW-RES-001`.  Simply formalizing the printed morphic image is invalid.

Status classification:

- Proposition 6.10 conclusion: `CITED`;
- Theorem 7.6 conclusion (`PST-GRP-03`): `CITED`;
- printed image equality above: `REFUTED` as written;
- pair-count arithmetic in Lean: `PROVED`;
- corrected pair-balance height theorem: `OPEN`.
