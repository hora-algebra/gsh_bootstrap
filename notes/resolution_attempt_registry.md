# Registry of the 2026-07-22 resolution-attempt draft and its failed inferences

**Provenance.** `~/Downloads/gsh_resolution_attempt.tex` (548 lines, dated
2026-07-22, **not under version control**) is a Japanese working note titled
「一般化星高問題：完全解決の試み，厳密な完全帰着，および残る一点」. Its own
`status` environments state the outcome plainly: the reductions are proved,
the final separation proposition is **not**, and publishing it as a full
resolution 「は数学的に偽の報告になる」. This note registers what the draft
contains so the repository does not lose or re-derive it; nothing here
upgrades any ledger status. Ledger rows: `RESATT-DOC-01`,
`LB-INVALID-ARGS-01`.

## 1. What the draft proves (its own classification, all UNREVIEWED here)

| Label | Statement (compressed) | Proof status in the draft |
|---|---|---|
| `thm:H1SF` | `H₁(A) = SF(C_*(A))` where `C_*(A) = QBool({K* : K star-free})` and `SF(−)` closes under union, complement, concatenation | full, ~5 lines, both inclusions; uses PST quotient-closure as imported input |
| `thm:PZ` | orbit characterization of `C`-separability | **imported from Place–Zeitoun 2025, not reproved; cited with no theorem number** |
| `thm:group-separator` | for `α : A* ↠ G`, TFAE: `gsh(α⁻¹(1)) ≤ 1`; the `C_*`-orbit of `α` at `1` is trivial; every `α⁻¹(g)`, `g ≠ 1`, is `C_*`-separable from `α⁻¹(1)` | full modulo `thm:PZ`; new step: the orbit is a finite submonoid of a finite group, hence a subgroup, hence aperiodic iff trivial |
| `thm:padding` | every DFA language is `φ⁻¹(P*S)` for finite `P, S` and a uniform (non-alphabetic) morphism `φ(a) = a c^N`, so `P*S` has restricted star height ≤ 1 | **full, both directions, written out** — the only written-out padding proof anywhere in this project's footprint; attributed to PST 1992 as "the concrete form of their final result", no theorem number |
| `thm:projection` | every regular `L` is the bijective letter-to-letter image of a star-free language of accepting runs | full; no citation, prior art unsearched |

Two corollaries sharpen the problem into single quantified statements: the
conjecture holds iff `φ⁻¹(P*S) ∈ H₁(A)` for every padding datum, iff every
letter-to-letter image of a star-free language has height ≤ 1. The draft
notes that PST's closure theorem covers inverse *alphabetic* morphisms only,
and extending it to the padding morphism 「は問題全体そのものと同値な強さを
持つ」 — an equivalence-strength trap in the sense of the stop conditions of
`AGENTS.md`.

**Overlap warnings, checked against this repository:**

- `thm:H1SF` is essentially ledger row `TOPOS-BASE-01` (`UNREVIEWED`, sourced
  to a deleted file). The draft supplies a proof text that the ledger row
  lacks, but auditing it must reconcile with `SFA-STAR-ONLY-01` (`PROVED`),
  whose characterization uses concatenation rather than quotients — the
  ledger already flags "quotients versus concatenation" as the gap to check.
- `thm:PZ` is `TOPOS-ORB-01`, and `PROOF_OBLIGATIONS.md` already complains
  that it is cited with no theorem number; the draft has the same defect,
  while `docs/exposition-ja/A5_simple_group_starheight_note_ja.tex` cites
  Place–Zeitoun 2025 Theorem 5.11 precisely. Any audit should use the latter.
- Attribution hazard: `PST-GRP-01` records that the commutative case is due
  to **Henneman**, credited by PST themselves. The draft attributes to "PST"
  three times with no theorem numbers; audits must not inherit that.

## 2. The six invalid inferences (「なぜここから先を証明として書けないか」)

Registered per the `AGENTS.md` rule that failed approaches are preserved with
their exact obstruction. Each row is an *apparent* inference and its breaking
point; rows 3–4 are invalid **upper-bound** arguments, the rest invalid
lower-bound arguments.

| # | Apparent inference | Breaking point |
|---|---|---|
| 1 | one-point anchor fails for all actions, so height > 1 | anchor expressions are a strict subfamily of height-1 expressions; the `C_*` separators are not exhausted |
| 2 | commutative counting methods fail, so height > 1 | `C_*` contains `K*` with non-commutative syntactic monoids |
| 3 | Pin 1978 puts every finite monoid inside some `P*`, so height ≤ 1 | division does not preserve letter marking; an inverse image under a general word morphism remains at the end |
| 4 | PST makes every regular language an inverse image of a height-1 language, so height ≤ 1 | the morphism is not alphabetic, so no known closure theorem applies |
| 5 | `A_5` has nontrivial cohomology, so a lower bound follows | no map from languages to classes, and no vanishing/preservation under the generating operations of `C_*` |
| 6 | finite search finds no expression, so height > 1 | no complete upper bound on the size of a height-1 expression |

The draft's closing caveat: assuming any of these as an unproved lemma
would produce a formally complete proof whose missing lemma is equivalent to
the problem — 「解決ではなく問題の改名である」.

A second, distinct list records five naive invariants that this repository's
own computations had *already* refuted as lower bounds by 2026-07-22:
non-solvable syntactic monoid; syntactic monoid containing a simple group;
the generated group being `A_5` (the `(123),(145)` identity language has
height 1, `A5-GEN145-01`); visible mod-4 scattered-subword counting
(`LAAB-04-01`); visible two-level dependent counters (the Weis stage-2 count
flattens through a finite prefix code). Any cohomological candidate must
therefore attach to something finer than these.

## 3. The draft's Lean order (for whenever this route is resumed)

Its ten-step formalization order is: (1) expressions/semantics/height;
(2) Boolean and concatenation closure of `H₁`; (3) quotient closure;
(4) `C_*(A)` as a prevariety intersection; (5) `thm:H1SF`; (6) separation,
pairs, orbits; (7) Place–Zeitoun as an explicit imported interface;
(8) syntactic monoid of group fibres + `thm:group-separator`; (9) the 59
`A_5` fibre pairs as finite data; (10) kernel-checked certificates for either
outcome. Steps (1)–(2) already exist in this repository; step (3) partially
(`leftQuotient`, reversal); the rest do not.

## 4. Preservation

The source file is a single unversioned copy in `~/Downloads`. Whether to
commit the .tex itself (or move it to a versioned location) is the owner's
call — it is a draft with known citation defects, and this registry already
carries its load-bearing content.
