# Run manifest: the fibration view of F_20 — base Z/4, fibre Z/5

Claims: `F20-FIB-01` (structure, PROVED), `F20-COH-SEP-01` (negative, COMPUTED),
`F20-MONO-FRONT-01` (COMPUTED), `F20-TRANSD-RED-01` (reduction, PROVED),
`TRANSD-ABEL-01` (CONJECTURAL), `TRANSD-LADDER-01` (COMPUTED),
`PST-WREATH-78-01` and `EIL-WPP-01` (CITED, from the prior-art search).
Obligation: `N-F20-001` stays OPEN; opens route (vi); `N-FIB-PRIOR-001` run and
marked `PARTIAL`; `N-TRANSD-ABEL-001` registered.

Derivation: `notes/f20_fibration_geometry.md`, `RESULTS.md` §5.15.
Base commit: `3004aff` (merge of PR #32 into `main`).

## Command

```bash
python3 scripts/f20_fibration_geometry.py
```

Python standard library only. Runtime 25 s. Python 3.14.6, macOS
(darwin 25.5.0 / macOS-26.5.2-arm64), single process, no network.
Imports `scripts/f20_full_alphabet.py` for the group and its direct evaluator, and
`scripts/small_group_pst_coverage.py` for the group constructors, the isomorphism
test and `pst_necessary_criterion`. Ground truth for every group element is
`f20_full_alphabet.evaluate`, never the coordinate formula.

## Hashes

| Artifact | sha256 |
|---|---|
| `scripts/f20_fibration_geometry.py` | `a337418565ac310b290dac4cb55ff5ec345a3895f6576893fde6ccf06adc2d27` |
| stdout of the run | `d7113299598b6f459d6105bc626a0b1f60adef8da35e156e87a652df27289ac6` |

(Recompute with `shasum -a 256 scripts/f20_fibration_geometry.py` and
`python3 scripts/f20_fibration_geometry.py | shasum -a 256`.)

## What the run establishes

1. **`β` is a 1-cocycle, and the free monoid carries no obstruction.**
   `β(uv) = α(v)β(u) + β(v)` on all 177,241 pairs of words of length ≤ 2 over the
   full 20-letter alphabet, and on 4,000 random pairs of length ≤ 11 each. Moreover
   every one of 200 random assignments of fibre values to the 20 letters extends to a
   cocycle, i.e. `Z¹(Σ*, Z/5) = (Z/5)^Σ`. The coordinate formula of §5.12 is not a
   derived gadget: it is the unique solution of the cocycle condition. The difficulty
   is the *definability* of `β`, never its existence.

2. **The extension cohomology vanishes identically across the order-20 family.**
   `H^n(C_4, Z/5)` computed from the bar resolution by exact F_5 linear algebra (not
   from the periodic-resolution formula), for the module where the generator acts by
   `r`: for every `r ∈ {1, 4, 2}` and every `n ∈ {1,2,3,4}`, `H^n = 0`; `H^0` is
   1-dimensional for `r = 1` and 0 otherwise. So `H² = 0` (all three split) and
   `H¹ = 0` (splitting unique up to conjugacy) for `C_20`, `Dic_5` and `F_20` alike.

3. **The frontier inside that family is the monodromy order alone.** The three
   members are pairwise non-isomorphic (machine-verified), `r = 1` is `C_20` and
   `r = 4` is `Dic_5` (machine-verified against `dicyclic(5)`), and
   `pst_necessary_criterion` returns a witness for `r = 1, 4` and `None` for `r = 2`.
   Monodromy orders 1, 2, 4 ↔ settled, settled, OPEN. Combined with item 2: no functor
   of the extension's classifying data can separate the settled cases from the open
   one.

4. **The hard irreducible representation is induced, and its dimension is the
   monodromy order.** `⟨Ind χ, Ind χ⟩` computed exactly in `Z[ζ_5]` from the coset
   formula is 4, 2, 1 for `r = 1, 4, 2`; by Clifford theory `Ind` is that many
   *distinct* irreps of dimension `4 / ⟨Ind, Ind⟩` = 1, 2, 4 = the monodromy order.
   For `F_20`, orthogonality specialises on all 20 elements to
   `5·1_{g=e} = 1_{ε(g)=0} + χ_ρ(g)`: the four linear characters give the base
   language (count mod 4) and a single 4-dimensional induced character carries all of
   the remaining difficulty. An explicit 4×4 model of `ρ` is verified to be a
   homomorphism on all 400 products, to have the coset character as its trace, and to
   be **monomial**, with the permutation part a function of `ε(g)` alone —
   `ρ(g) = P(ε(g))·D(g)`, the fibration in matrix form.

5. **The wreath embedding.** `F_20 ↪ C_5 ≀ C_4 = (Z/5)^4 ⋊ C_4` (order 2500) via
   `(α, β) ↦ ((2^i β)_i, ε)`, verified a homomorphism on all 400 products and
   injective on all 20 elements; the ambient product is associative on 20,000 random
   triples.

6. **The transducer decomposition** `μ⁻¹(e) = {ε ≡ 0 mod 4} ∩ σ⁻¹(K)` where `σ` is
   right-sequential with state set `Z/4` (the monodromy group itself; verified to be
   the claimed sequential machine on 2,000 random words) and `K ⊆ (Z/4 × Σ)*` is
   recognized by `C_5`. Checked on all 168,421 words of length ≤ 4 over the full
   alphabet and all 8,191 words of length ≤ 12 over the two generators. Three negative
   controls (constant weights, two weights transposed, one weight zeroed) are wrong on
   173 / 160 / 109 words of length ≤ 10, so the identity is a property of the weights
   `2^p` and not of the shape of the statement. A cyclic shift of the weights is
   deliberately *not* used as a control — it scales the sum by a unit of F_5 and
   decides the same predicate — and that fact is itself verified.

7. **Calibration passed.** Specialised to `{a, b}`, `σ⁻¹(K)` *is* the published
   arithmetic characterization of `F20-STD-01`; it agrees with the group on all 32,767
   words of length ≤ 14, the same instance verified there. Route (ii) and route (iii)
   both failed this test; this mechanism does not. The published coefficients
   `(1,3,4,2) = 2^{-p}` are identified as the **prefix**-phase convention (the suffix
   reading is wrong on 544 of 8,191 words), and the two trivialisations are shown to
   differ by exactly the holonomy `2^{ε(w)}` of the whole loop, on all 8,421 words of
   length ≤ 3 over the full alphabet.

8. **What homology sees, and its limit.** With the LHS collapse (short proof in the
   note; the input `H^{2k}(C_5, Z) = Z/5` with `C_4` acting by `r^k` is CITED), the
   5-torsion survives exactly in degrees `2k` with `ord(r) | k`, so the 5-primary
   cohomological period is 2, 4, 8 for `r = 1, 4, 2` — always `2 × ord(r)`. Homology
   *does* separate the three groups, but reports nothing beyond the monodromy order.

9. **`σ⁻¹` does not preserve star-freeness.** `A·Γ*` uses no star at all, hence is
   star-free over `Γ`; its `σ`-preimage has a 5-state minimal DFA whose transition
   monoid contains an element of period 4, so by Schützenberger 1965 it is not
   star-free — on the 2-generator and on the full alphabet alike. The closure property
   the reduction needs therefore cannot come from any star-free closure theorem, and
   the gap to `PST-CL-01` (inverse *alphabetic* morphisms = the one-state case) is
   exactly "one state" versus "monodromy many states".

10. **The hypothesis on the state monoid is the whole content** (`TRANSD-LADDER-01`).
    For every regular `L`, marking each letter with the DFA state in front of it makes
    `L = σ⁻¹(Γ*·S)` with the target **star-free**. Verified for `mu⁻¹(e)` on all 8,191
    words of length ≤ 12 over two generators and all 168,421 of length ≤ 4 over the full
    alphabet. Since `mu⁻¹(e)` is not star-free (syntactic monoid the group `F_20`),
    "σ⁻¹ preserves gsh 0 with no hypothesis" is outright **false**, and "σ⁻¹ preserves
    gsh ≤ 1 with no hypothesis" is **equivalent to the entire generalized star-height
    conjecture**. The known rungs are aperiodic (`PST-WREATH-78-01`) and elementary
    abelian 2 (`PST-GRP-03`); the first open rung is a cyclic state monoid of order 4,
    which is `N-F20-001` itself.

11. **The abelian rung would settle every finite solvable group.** The
    Krasner–Kaloujnine embedding `g ↦ (q ↦ t_q g t_{q·π(g)}⁻¹, π(g))` into `G' ≀ (G/G')`
    is verified an injective homomorphism at **every** stage of the derived series, with
    every quotient checked abelian, for all six groups outside the PST class: `A_4`
    12→4→1, `F_20` 20→5→1, `C_7⋊C_3` 21→7→1, `SL(2,3)` 24→8→2→1, `S_4` 24→12→4→1,
    `C_2×A_4` 24→4→1. Quotients are reported by **order only** — an abelian group of
    order 4 may be `C_4` or `C_2×C_2` and the computation does not decide which.

## Prior-art search (`N-FIB-PRIOR-001`, run 2026-07-25, PARTIAL)

Found, and it changes the framing rather than the result:

- **`PST-WREATH-78-01`.** PST 1992 **Theorem 7.8** reads, quoted verbatim from
  Bourne–Ruškuc arXiv:1603.06236: "Since all languages that belong to the pseudovariety
  generated by wreath products of abelian groups by aperiodic monoids have star-height
  at most one [9, Theorem 7.8]". In the transducer language of item 6 this is exactly
  the **aperiodic-state case** of `TRANSD-ABEL-01`. It supersedes the wording of
  `PST-WREATH-06-01` (taken from the abstract, which did not say which factor must be
  aperiodic) and explains `PST-WREATH-COMM-01` structurally.
- **`EIL-WPP-01`.** The decomposition of item 6 is Eilenberg's wreath-product machinery
  (Proposition IX.1.1, modified for generalized sequential functions), as cited in the
  same paper. **No novelty is claimed** for the construction; the repo's derivation is
  elementary only so that nothing depends on an unobtained citation.
- **The abelian-state case was not located** — neither proved nor refuted in the
  surveyed sources.

Not obtained: the PST 1992 **full text**. HAL returns an Anubis anti-bot page,
ScienceDirect 403, `irif.fr` 403, and `web.archive.org` is unreachable from this
environment. The theorem number and wording therefore rest on a secondary source, and
"not found" must not be read as "not known". Remaining sub-task recorded on
`N-FIB-PRIOR-001`: obtain PST 1992 §7 through an institutional library, and check Pin,
*Varieties of Formal Languages*, on wreath products.

## Verdict

The fibration reading is exact, not analogical. It supplies **no new invariant** —
extension cohomology is identically zero across a family whose members differ in gsh
status, and full homology only re-encodes the monodromy order as a period — but it
supplies a **reduction**: the identity fibre is the `σ`-preimage of a commutative-group
language intersected with a base language, both of gsh ≤ 1. `HeightOneForGroup F_20`
follows if `σ⁻¹` preserves gsh ≤ 1. This is the first `N-F20-001` mechanism to pass the
2-generator calibration. The prior-art search then locates it exactly: the aperiodic-state
case is PST 1992 Theorem 7.8, the elementary-abelian-2 case is `PST-GRP-03`, and `F_20` is
the first open rung — a cyclic state monoid of order 4.

## Known gaps and cautions

- **Not a lower bound** (research rule 1). Nothing here shows any language has gsh > 1.
- **The single-`K` form of the reduction is close to a restatement**, and therefore
  falls under the AGENTS.md stop condition "the missing lemma is equivalent in
  strength to the original target". It must not be attacked directly. The value lies
  in the general form `TRANSD-ABEL-01`, which is strictly stronger, uniform, and — if
  the reading in the note §6 is right — has `PST-GRP-03` as its elementary-abelian-2
  case. That reading of PST 1992's reach is **UNREVIEWED**; the primary source full
  text is still unobtained (same cause as the caution on `PST-WREATH-06-01`).
- **Prior art searched, PARTIAL** (see the section above). The construction is standard
  (`EIL-WPP-01`) and the aperiodic case is a theorem (`PST-WREATH-78-01`); the abelian
  case was not located. The primary source is still unobtained, so the citation chain
  runs through a secondary source.
- **The abelian conjecture is not a small step.** By item 11 it settles every finite
  solvable group, and by item 10 dropping the hypothesis altogether restates the whole
  open problem. Both facts argue for attacking the minimal open rung (state monoid
  `C_4`) and not the general statement.
- `PST-GRP-01` (commutative ⇒ gsh ≤ 1) is CITED, not proved here, and the reduction
  depends on it. `Dic_5` being settled rests on `DICM-EMB-01` (PROVED) plus
  `PST-GRP-03` (CITED).
- `COH-01` stays **REFUTED**. Item 2 strengthens it from "no such theorem was found"
  to "extension cohomology provably cannot separate a settled case from the open one",
  but it does not touch the possibility of some other cohomological construction.
- Written and verified without delegation, per the measurement recorded on PR #29 that
  delegating design-bearing work costs more than doing it directly.
