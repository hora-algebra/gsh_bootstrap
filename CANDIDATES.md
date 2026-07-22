# Counterexample candidates (generalized star height ≥ 2)

Status date: 2026-07-22.  This list refines RESULTS.md §6 ("構成の適用限界").
Every entry is a *candidate*: no language is known to have generalized star
height ≥ 2, and no lower-bound technique exists (RESULTS.md §2).  Failure of
the synthesis search (`tools/height_search.py`) up to any size bound is a
search result only, never a lower bound (README rule 1).

Machine-readable targets: each candidate with a `target` name below has a
minimal-DFA builder in `tools/targets.py`; run

    python3 -m tools.height_search --list
    python3 -m tools.height_search --target <name> --max-size <n>

## Why these candidates

The height-1 constructions verified in RESULTS.md §5 all factor through:
an abelian normal subgroup `A` with cyclic quotient `Z/m`, plus a division of
labour among generators (one letter generates the quotient, the others land
in `A`), plus tokenization by a star-free prefix code.  Each candidate below
breaks at least one of these three legs.

## Tier 1 — structural obstruction to every known positive method

History (2026-07-22): this tier originally listed `a5` with φ(a) = (12345),
φ(b) = (123) on the rationale "simple and non-solvable, so the
cumulative-count decomposition fails for every generating set".  That
rationale is dead: RESULTS.md §5.6 resolved (123),(145) as height 1 by a
point-stabilizer filtration with star-free first-return codes, and §5.7
generalized it to a machine-checkable **anchor criterion** under which
(12345),(123) and (123),(345) — indeed every generating set consisting only
of 3-/5-cycles — are height 1.  The `a5` target is kept as a calibration
target only.  What survives §5.7:

1. **A5 word problem, (2,3,5)-type generators** — `target: a5_235`
   (60 states), φ(a) = (12)(34), φ(b) = (135).  The anchor criterion fails
   at *every* anchor: the double transposition has two 2-cycles, and one
   anchor can break only one of them, so the internal walk machine stays
   non-aperiodic.  Status: COMPUTED (anchor-criterion failure,
   `scripts/a5_frontier.py`), SPECULATIVE (that no other height-1 assembly
   exists).  Perrin's caveat still applies: no lower-bound tool exists.

2. **A5 word problem, full 60-element alphabet** — no DFA target here yet
   (60 states over a 60-letter alphabet; the universal case dominating
   every generating morphism).
   §5.7 machine-verifies that all current routes fail: every anchor's
   internal monoid contains A4 (non-aperiodic), the regular action has no
   fixed points (first-return codes not star-free), and the 5-point action
   is primitive (no quotient topology).  Status of the obstructions:
   COMPUTED; the candidacy itself remains SPECULATIVE.

## Tier 2 — solvable, but the generator division of labour fails

2. **S4 word problem** — `target: s4` (24 states), φ(a) = (1234), φ(b) = (12).
   Solvable, but the derived tower `S4 ▷ A4 ▷ V4` has non-cyclic quotient
   steps (`S4/V4 ≅ S3`), so the "one letter drives a cyclic quotient"
   normal form does not exist.  Status: COMPUTED (group facts), SPECULATIVE
   (that this defeats all height-1 assemblies).

3. **A4 word problem with two 3-cycles** — `target: a4_two_3cycles`
   (12 states), φ(a) = (123), φ(b) = (124).  Same group as
   `a4_std` (height ≤ 1 COMPUTED, RESULTS.md §5), but no generator lands in V4, so the verified construction does
   not transfer.  Tests whether word-problem star height can depend on the
   generating morphism.  Status: SPECULATIVE.

## Tier 3 — counting languages just outside the covered zone

4. **L(aab, 0, 8)** — `target: L_aab_0_8`.  `binom(w, aab) ≡ 0 mod 8`.
   The n = 4 case (COMPUTED, RESULTS.md §6) used one carry-bit decomposition;
   n = 8 needs two nested carries.  Status: CONJECTURAL that the carry
   decomposition iterates; unresolved either way.

5. **L(aabb, 0, 2)** — `target: L_aabb_0_2`, and **L(abab, 0, 2)** —
   `target: L_abab_0_2`.  `|u| = 4` leaves the Pin–Straubing–Thérien zone
   (`|u| ≤ 2` any n; `|u| ≤ 3`, n squarefree) and the repo's `|u| = 3`
   extension.  The single-residue reduction of RESULTS.md §3 has no analogue
   checked for `|u| = 4`.  Status: SPECULATIVE.

## Tier 4 — definition audit pending

6. **Weis L2** (order-48 group; segment counting of the unbounded pattern
   `ba*b`).  Update 2026-07-22: the stage-2 reading of this description —
   every Boolean combination of staged `ba*b` pair counts `N_{p,q} mod 2/4`
   with phases mod 2, and odd-run segment counts mod 4 — is **resolved:
   generalized star height <= 1** (RESULTS.md §5.9,
   `scripts/weis_l2_family.py`, `notes/weis_l2_stage2_height1.md`).  The
   old obstruction ("tokenization breaks phase tracking", RESULTS.md §6.3)
   is bypassed by flat token counting over the FINITE run code {b, aa, ab}.
   Still open: (i) the stage-3 reading (phases mod 3) — single-run-covering
   prefix codes are integrality-locked to the (2·T1+T2) mod 3 combination,
   only T1 mod 2 is recovered, and cascade codes were machine-checked
   insufficient (PROOF_OBLIGATIONS.md N-L2-M3-001); (ii) the definition
   audit against Weis (2011) — the thesis is unreachable from the current
   session environment, and the cited order-48 group was NOT reproduced by
   any scanned family instance (max-subgroup orders seen: 2..384, no 48;
   PROOF_OBLIGATIONS.md M-WEIS-001).  A 2009 UMass theory-seminar abstract
   states Weis proved all four of his candidate languages to be of
   generalized star height one, so L2 is likely not a live counterexample
   candidate at all.  Status: stage-2 family COMPUTED (height <= 1);
   identification with Weis's L2 UNREVIEWED; stage >= 3 OPEN.

## Practical note on the synthesis search

`tools/height_search.py` enumerates all generalized regular expressions of
star height ≤ 1 over {a, b} in order of AST size, deduplicated by language
(canonical minimal DFA).  The number of distinct languages grows quickly with
size; group word problems above (12–60 DFA states) are far beyond exhaustive
range.  The search is useful for (i) calibration on solved targets,
(ii) finding *minimal* height-≤1 expressions for small fragments (atoms of a
hand-built construction), and (iii) making "no small expression exists"
statements exact.  A negative run must always be reported with its size
bound and pruning status.
