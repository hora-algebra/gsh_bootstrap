# Star-free-labelled automata: an automaton-side reading of height one

Date: 2026-07-25.  Status of the main construction: `PROVED` (§2, elementary
and machine-checked on every use).  Status of the reformulations: `PROVED`
(§3) and `UNREVIEWED` (§4, because it rests on the external
`CORE2-EQV-EXT-01`).  Status of the measurement: `COMPUTED` (§5).

Nothing in this note is a star-height *lower* bound.  §2 gives an upper-bound
machine only; §2.4 explains precisely why the converse half of Eggan's
theorem does not relativize, and every "not found" statement below is a
search result (README research rule 1).

## 0. Why this note exists

Every positive result in this repository — `A4-FULL-01`, `A5-GEN145-01`,
`THOMAS-D2-02`, `WEIS-L2-GSH-01` — has the same shape:

> tokenize the input by a **star-free** code, run a **finite** action on the
> tokens, and separate the fibres by a **Boolean** combination.

That shape is an automaton, not an expression.  This note writes it down as
one, so that "find a height-1 expression" becomes "find an automaton of a
certain kind", and so that the search can use graph-theoretic tools
(strongly connected components, vertex deletion, rank induction) that the
expression language does not offer.

## 1. Definitions

Fix a finite alphabet `Σ`.  Write `SF` for the star-free languages over `Σ`,
i.e. the languages of generalized regular expressions of syntactic star
height 0.  Star-freeness of a *label* is therefore a syntactic, decidable
side condition, not a semantic obligation — this is what makes the objects
below certifiable.

> **Definition 1.1 (SF-automaton).**  An SF-automaton is a finite directed
> multigraph `𝒜 = (V, E, I, F)` with `I, F ⊆ V`, together with a labelling
> `λ : E → SF`.  A word `w` is accepted iff `w ∈ λ(e₁)···λ(e_k)` for some
> path `e₁…e_k` from a vertex of `I` to a vertex of `F` (the empty path is
> allowed, contributing `ε`).  `L(𝒜)` is the accepted language.

> **Definition 1.2 (loop complexity).**  The *cycle rank* `r(G)` of a
> digraph `G`, following Lombardy–Sakarovitch, *The universal automaton*,
> Def. 7.4:
> `r(G) = 0` if `G` has no edge; `r(G) = max_i r(C_i)` over the strongly
> connected components if there is more than one; and
> `r(G) = 1 + min_{v ∈ V} r(G − v)` if `G` is strongly connected and has an
> edge.  Write `r(𝒜)` for the cycle rank of the underlying digraph.

> **Definition 1.3.**  `r_SF(L) = min { r(𝒜) : 𝒜 an SF-automaton, L(𝒜) = L }`.

Implementation: `tools/sf_automaton.py` (`SFAutomaton`, `cycle_rank`).

## 2. The upper-bound machine

> **Theorem 2.1.**  For every SF-automaton `𝒜` and all `p, q ∈ V`, the path
> language `L(p,q)` is denoted by a generalized regular expression of
> syntactic star height at most `r(𝒜)`.  Consequently
>
>     gsh(L) ≤ r_SF(L)   for every regular L.

*Proof.*  Induction on `|V|`, along the three cases of Definition 1.2.
Write `λ(x,y)` for the union of the labels of the edges `x → y`, and `∅`
when there is none.

**(a) No edges.**  `L(p,q) = {ε}` if `p = q` and `∅` otherwise; height 0.

**(b) More than one strongly connected component.**  Let `C₁, …, C_m` be the
components and fix a topological order of the condensation, which is acyclic.
Each `C_i` is a proper subset of `V`, so by induction the within-component
path languages `L_{C_i}(x,y)` have expressions of height `≤ r(C_i) ≤ r(𝒜)`.
Fix a goal `q` and define, by reverse topological order,

    f_q(x) = [ L_{C(x)}(x,q) if C(x) = C(q) ]
             ∪ ⋃ { L_{C(x)}(x,u) · λ(u,w) · f_q(w) : u ∈ C(x), w ∉ C(x), (u,w) ∈ E }.

The recursion is well founded because `C(w)` is strictly later in the
topological order, and it is exact because a path that leaves a component
never re-enters it: splitting at the first crossing edge is a bijection.
No star is introduced, so `height(f_q) ≤ max_i r(C_i) = r(𝒜)`.

**(c) Strongly connected with an edge.**  Choose `v` realizing
`r(𝒜 − v) = r(𝒜) − 1`, and let `H = 𝒜 − v`.  By induction the path
languages `L_H(x,y)` have height `≤ r(𝒜) − 1`.  Put

    C    = λ(v,v) ∪ ⋃_{x,y ∈ H} λ(v,x) · L_H(x,y) · λ(y,v)      (first returns to v)
    B(p) = ε if p = v, else ⋃_{x ∈ H} L_H(p,x) · λ(x,v)
    D(q) = ε if q = v, else ⋃_{y ∈ H} λ(v,y) · L_H(y,q)

Then

    L(p,q) = [ L_H(p,q) if p ≠ v and q ≠ v ] ∪ B(p) · C* · D(q).

A path from `p` to `q` either avoids `v` altogether — the first summand,
which is empty when `p` or `q` is `v` — or visits it, and splitting at the
first and last visit to `v` gives the second summand; conversely every such
concatenation is a path.  `B`, `C`, `D` are built from the `L_H` and from
edge labels using only `∪` and `·`, so each has height `≤ r(𝒜) − 1`; hence
`C*` has height `≤ r(𝒜)` and so does the whole expression.

Finally `L(𝒜) = ⋃_{p ∈ I, q ∈ F} L(p,q)` is a finite union. ∎

### 2.1a The bound is tight, and the mechanism is published

Sakarovitch, *Automata and rational expressions* (arXiv:1502.03573, the long
version of Chapter 2 of the AutoMathA Handbook) §3.6, already carries out
this bookkeeping.  His Definition 3.1 of loop complexity is the cycle rank
used here (his "balls" are the nontrivial strongly connected components).
Crucially, in the proof of his Proposition 3.13 he considers

> "automata whose transitions are labelled not by letters only but by
> rational expressions in general"

and defines the *index* of such a **generalised automaton** by equations
(3.24)–(3.26), starting from the index of a single transition,
`i(e) = h[|e|]` — the star height of its label.  Then

* Property 3.12: `lc(A) = min { I_ω(A) : ω an order on the states }`;
* Proposition 3.13 (Lombardy–Sakarovitch, *On the star height of rational
  languages*, 2003): `I_ω(A) = h[B_ω(A)]` for every order `ω`, where
  `B_ω(A)` is the expression that state elimination computes in the order
  `ω`;
* Theorem 3.11 (Eggan 1963) follows.

For an SF-automaton every label has index 0, so (3.24)–(3.26) collapse to the
classical loop complexity of the underlying digraph, and the two displayed
statements give **equality**:

    min over elimination orders of the star height of the emitted expression
      =  loop complexity of the automaton.

So Theorem 2.1 is not merely an inequality that some order happens to
satisfy — the minimum is attained, and the elimination order derived from the
cycle-rank recursion attains it.  The proof in §2 above is retained because it
is self-contained and is what the implementation follows, but the priority is
Eggan's and Lombardy–Sakarovitch's; see §7.

### 2.2 Machine-checked form

`SFAutomaton.to_expression()` implements exactly this recursion and
**re-verifies the conclusion on every call**: it compares the syntactic star
height of the emitted expression with `loop_complexity()` and raises
`SFAutomatonError` if the bound is exceeded.  A regression in the elimination
order therefore fails loudly rather than silently producing a weaker
certificate.  `tests/test_sf_automaton.py::RankBoundTests` runs the check
over every automaton in the module.

### 2.3 Calibration of the extremes

`r_SF(L) = 0` iff `L` is star-free: an acyclic SF-automaton has finitely many
paths, so `L` is a finite union of concatenations of star-free languages and
hence star-free; conversely a star-free `L` is the label of a single edge
between two vertices.  With `GSH-BASE-01` this matches `gsh(L) = 0`.
So Theorem 2.1 is exact at height 0, and the first genuinely new content is

    r_SF(L) ≤ 1   ⟹   gsh(L) ≤ 1.

### 2.4 Why the converse does not relativize

Eggan's theorem (Lombardy–Sakarovitch Thm. 7.5, used in this repository by
`WEIS-L2-RSH-01`) states that the *restricted* star height equals the minimal
loop complexity over letter-labelled automata.  Its non-trivial direction
turns an expression of star height `h` into an automaton of loop complexity
`≤ h`, by structural induction on `∪`, `·`, `*`.  A generalized expression
also has `¬`, and complementation has no automaton construction that controls
loop complexity — the only route is determinization, which destroys the graph
structure.  So `r_SF` is an upper bound for `gsh` and there is no reason to
expect equality.

This is not an abstract worry: `WEIS-L2-GSH-01` gives `gsh(L2) = 1`, while §5
measures `r_SF(L2) ≤ 2` and finds no rank-1 SF-automaton for `L2`.  The gap is
exactly the Boolean layer.

> **Definition 2.5.**  `𝒮₁ = { L : r_SF(L) ≤ 1 }`, the languages of rank-1
> SF-automata.  Equivalently, `𝒮₁` is the closure of `SF ∪ { E* : E ∈ SF }`
> under `∪` and `·` only.

## 3. The whole problem is one more star

`GH₁` denotes the languages of generalized star height at most 1.  Directly
from the definition of star height — which propagates as a maximum through
`∪`, `∩`, `¬` and `·`, and adds one only at `*` — we get:

> **Proposition 3.1.**  `GH₁` is the smallest class containing `SF` and
> `{ E* : E ∈ SF }` and closed under `∪`, `∩`, `¬` and `·`.  In particular
> `GH₁` is a Boolean algebra closed under concatenation, and it contains
> `𝒮₁`.  (It is also closed under left and right quotients, by the Brzozowski
> derivative lemma of `notes/conway_group_identities_and_full_alphabet.md`
> §3.5, `FULL-ALPH-RED-01`.)

> **Proposition 3.2.**  `GLOBAL-ONE` holds iff `GH₁` is closed under `*`.

*Proof.*  `(⇐)` `GH₁` contains `∅` and every singleton `{a}`, and is closed
under `∪` and `·` by Proposition 3.1; if it is also closed under `*` it
contains every regular language by Kleene's theorem.  `(⇒)` If every regular
language lies in `GH₁` then `GH₁` is the class of all regular languages,
which is closed under `*`. ∎

Elementary, but it isolates the obstruction: `GH₁` already has every Boolean
operation, concatenation and quotients.  **The star is the only missing
closure property**, and on the automaton side "apply one more star" is
"add ε-edges from the final vertices back to the initial ones", which raises
the cycle rank by at most one.

## 4. CORE2, read as rank reduction

`CORE2-EQV-EXT-01` (external, `UNREVIEWED`; `RESULTS.md` §6.1) reports

    every regular language is in GH₁  ⟺  ∀ A,B,C,D ∈ SF, (A ∪ B D* C)* ∈ GH₁.

The right-hand side is an SF-automaton verbatim:

    state 1: self-loop A          1 --B--> 2          I = F = {1}
    state 2: self-loop D          2 --C--> 1

whose path language from 1 to 1 is `(A ∪ B D* C)*`.  All four labels are
star-free.  Deleting vertex 1 leaves the self-loop `D`, so no single deletion
makes the graph acyclic and the cycle rank is exactly **2**.

> **Reformulation 4.1** (modulo `CORE2-EQV-EXT-01`, hence `UNREVIEWED`).
> `GLOBAL-ONE` is equivalent to: every SF-automaton of loop complexity 2 —
> indeed every SF-automaton of the single two-state shape above — has
> generalized star height at most 1.

Combining with Theorem 2.1, for every `r ≥ 2` the statement "every rank-`r`
SF-automaton has `gsh ≤ 1`" is equivalent to `GLOBAL-ONE`: it implies the
rank-2 case, and it follows from `GLOBAL-ONE` trivially.  So the rank
hierarchy collapses to a single question,

    rank 1  ⟹  gsh ≤ 1        (Theorem 2.1, unconditional)
    rank 2  ⟹  gsh ≤ 1        (⟺ GLOBAL-ONE)

and the target of the programme is a **rank-reduction transformation**:
given a rank-2 SF-automaton, produce a Boolean combination of rank-1
SF-automata with the same language.

## 5. What has been measured

`scripts/sf_automaton_calibration.py` (exact, no sampling, no length
cutoffs; run manifest `data/experiments/sf_automaton_calibration.md`):

1. **Ground truth.**  The printed Weis 2011 p.115 expression for `L2` is
   recompiled and asserted equal to the six-state walk automaton of
   `a = (0 1)(3 4)`, `b = (0 2 3 5)`.
2. **`L2`, letter-labelled.**  The minimal DFA of `L2`, viewed as an
   SF-automaton, has loop complexity **2**, and state elimination returns a
   star-height-2 expression that is exactly `L2`.  So `r_SF(L2) ≤ 2`.
3. **The four-diagonal graph.**  Absorbing the two `a`-self-loops (at `D₀`
   and `D₁`) into the incoming edges, using the star-free `a* = ¬(⊤b⊤)`,
   gives a four-vertex SF-automaton of loop complexity **1**.  Its
   first-return and escape languages, computed by elimination, coincide
   exactly — checked by DFA equivalence, not by inspection — with the ones
   printed in `notes/weis_l2_full_height_one.md` §3, for **both** anchors:

       R_{D₂} = (a | b a* b a* b)(a | b)
       R_{D₃} = (a | b)a | (a | b) b a* b a* b

4. **The atoms.**  All eight anchor-walk atoms `W_d(x)`, `d ∈ {D₂, D₃}`,
   `x ∈ {D₀,…,D₃}`, have loop complexity 1, eliminate to star height ≤ 1, and
   are proved language-equal to the exact diagonal walk automata.  Both
   letter-parity atoms are rank-1 SF-automaton languages as well
   (`even_a` eliminates to `b*(a b* a b*)*`).
5. **Consequence.**  `WEIS-L2-GSH-01` writes `L2` as a union of eight fibres,
   each an intersection of two parity atoms and two anchor-walk atoms.  Every
   one of those atoms is now certified to be a rank-1 SF-automaton language,
   so

       L2 ∈ BoolComb(𝒮₁),     r_SF(L2) ≤ 2,

   and no rank-1 SF-automaton for `L2` is known.  The labels range over all
   star-free languages, so this is a **search result and never a lower
   bound**.

Two certificates are emitted and re-verified by `tools/regex_cert.py`
(`CERT-01`, an independent implementation) on every run of
`./scripts/check.sh`:
`data/certificates/height1_weis_l2_anchor_atom.json` (the atom `K_{D₂}`) and
`data/certificates/height1_z3_sf_automaton.json`.

**Reading of the measurement.**  The anchor criterion of `RESULTS.md` §5.7 is
exactly a sufficient condition for a walk language to have `r_SF ≤ 1`, and the
Boolean layer of `WEIS-L2-GSH-01` is exactly the step from `𝒮₁` to
`BoolComb(𝒮₁)`.  The framework therefore reproduces the repository's hardest
positive result rather than competing with it — and it says where the
difficulty sits: not in finding stars, but in needing intersections.

## 6. The transformation catalogue

The moves that the repository's proofs actually perform, stated at the
automaton level.  Only the first is implemented so far.

1. **Self-loop absorption** (`SFAutomaton.absorb_self_loop`).  If a vertex
   carries a self-loop labelled `E` and `E*` is *again star-free*, fold `E*`
   into the incoming edges and delete the self-loop.  Labels stay star-free,
   an edge leaves the graph, the rank can only drop.  This is what makes the
   `a`-loops of the `L2` diagonal graph disappear.
2. **Quotient of the action.**  Replace the state set by a quotient on which
   the first-return languages become star-free.  This is the six-point →
   four-diagonal move of `WEIS-L2-GSH-01`.
3. **Final-state flip.**  Complement, free — *but only when the automaton is
   deterministic in its label alphabet*, i.e. when the labels form a code
   whose parsing is unique.  For a general SF-automaton, flipping final
   vertices does not complement the language.  This is the tension the whole
   framework sits on: determinism makes negation free, nondeterminism keeps
   the rank low, and `rsh(L2) = 2 > 1 = gsh(L2)` is that gap measured.
4. **Product.**  Intersection; the obligation is a common star-free
   refinement of the two label codes.
5. **State elimination.**  Rank reduction (Theorem 2.1).

Read in this language, the `A_5` obstructions of `RESULTS.md` §5.7 are
failures of exactly the first two moves: "the regular action has no fixed
points, so first-return codes are not star-free" is the failure of (1), and
"the five-point action is primitive, so there is no quotient topology" is the
failure of (2).

## 7. Priority, and what is not claimed

**Prior-art search performed 2026-07-25** (obligation `M-SFA-PRIOR-001`).
Result: Theorem 2.1 is **not new**, and the note's earlier "presumed
folklore" reading was correct.

*What is published.*  The label-agnostic index bookkeeping is exactly
Sakarovitch's treatment of *generalised automata* in
[Automata and rational expressions](https://arxiv.org/abs/1502.03573) §3.6
(long version of AutoMathA Handbook Ch. 2): the index of a transition is the
star height of its label, equations (3.24)–(3.26) lift the loop complexity to
that setting, Property 3.12 and Proposition 3.13 (the latter credited to
S. Lombardy and J. Sakarovitch, *On the star height of rational languages*,
in *Words, Languages and Combinatorics III*, World Scientific, 2003) give
`min_ω h[B_ω(A)] = lc(A)`, and Theorem 3.11 is Eggan 1963.  The proof's base
case turns on `h[E + F·G*·H] = max(h[E], h[F], h[H], 1 + h[G])`, an identity
that never mentions the labels.

*What that source does not do.*  Its `h[·]` is the star height of **rational**
expressions throughout — complement is not part of the framework (the word
appears once in the whole survey, in an unrelated aside).  So a star-free
label such as `a*` has index 1 there and index 0 here.  Reading the same
identity with `h` = *generalized* star height is legitimate precisely because
complement does not occur in `E + F·G*·H`, so the induction transfers
verbatim; but that reading is not stated in the source.  **The contribution of
this note is therefore the instantiation and the bookkeeping, not the
theorem**: it converts "exhibit a height-1 expression" into "exhibit an
SF-automaton of rank 1", a finite object with a decidable side condition and
a machine-checkable certificate.

*What was searched and not found.*  No automaton-side treatment of
*generalized* star height was found in: Sakarovitch's survey (above);
H. Gruber, [Digraph Complexity Measures and Applications in Formal Language
Theory](https://arxiv.org/abs/1111.5357) (cycle rank throughout, restricted
star height only, NP-completeness and the bideterministic case); T. Bourne's
[NBSAN slides on the generalized star-height problem](https://personalpages.manchester.ac.uk/staff/Mark.Kambites/events/nbsan/nbsan20_bourne.pdf)
(automata used only to certify star-freeness via aperiodicity; the listed
techniques are Schützenberger, Henneman, and PST — nothing loop-theoretic);
and *Star Height via Games* (arXiv:1708.03603, restricted only).

*Residual, not closed.*  Two items could not be checked from open sources and
stay in `M-SFA-PRIOR-001`:

1. **Hashiguchi's *relative star height*** (Inf. Comput. 78(2):124–169, 1988;
   and *Relative star height, star height and finite automata with distance
   functions*, 1988), together with Kirsten's *Distance Desert Automata and
   Star Height Substitutions* (Habilitation, Leipzig).  This is star height
   measured over a base of given languages — structurally the same move as
   `r_SF`.  The exact definition (in particular whether the base may be an
   infinite class such as `SF`) was **not retrieved**; both are paywalled.

   *Lead, `SPECULATIVE`, from a search-engine snippet and not from the paper.*
   The definition may read: for a **finite** class `C = {R_1, …, R_m}` of
   regular languages over `Σ` and the substitution `δ` sending each letter of
   `Δ` to some `R_i`, the relative star height of `R` w.r.t. `C` is the least
   star height of a language over `Δ` that `δ` maps onto `R`.  If the class is
   required to be finite, then `r_SF` — whose base `SF` is infinite — is the
   infimum of that quantity over all finite `C ⊆ SF`, hence related but not an
   instance.  If the class may be infinite, `r_SF` *is* an instance and the
   name should change.  **Do not act on this paragraph until the definition is
   read in the source.**
2. **Pin–Straubing–Thérien 1992** itself could not be fetched (the HAL copy is
   behind a bot filter), so it has not been checked for an automaton-side
   formulation. `M-PST-001` covers the paper for other reasons.

*Fetch list for the residual* (recorded 2026-07-25 so the obligation stays
actionable; none of these were reachable from this machine):

| # | Source | Link | What to extract |
|---|---|---|---|
| 1 | Hashiguchi 1988, *Algorithms for determining relative star height and star height*, Inf. Comput. **78**(2):124–169 | [doi:10.1016/0890-5401(88)90033-8](https://doi.org/10.1016/0890-5401%2888%2990033-8) | the definition of relative star height, verbatim with its page number; whether the base class must be finite; whether complement appears anywhere |
| 2 | Hashiguchi 1988, *Relative star height, star height and finite automata with distance functions* (LNCS, LITP Spring School) | [doi:10.1007/BFb0013113](https://doi.org/10.1007/BFb0013113) | same definition in survey form — usually shorter and enough to decide the question |
| 3 | Kirsten 2011, *Some Variants of the Star Height Problem*, MFCS 2011 | [doi:10.1007/978-3-642-22993-0_4](https://doi.org/10.1007/978-3-642-22993-0_4) | the variant taxonomy: is "star height over a base of star-free languages" one of the listed variants? |
| 4 | Kirsten, *Distance Desert Automata and Star Height Substitutions*, Habilitation, Univ. Leipzig 2006 | no open copy found; try the Leipzig library / Qucosa | what a *star height substitution* is, and whether the substituted base may be infinite |
| 5 | Pin–Straubing–Thérien 1992, *Some results on the generalized star-height problem*, Inf. Comput. **101**(2):219–250 | [HAL PDF](https://hal.science/hal-00019978v1/file/StarHeight.pdf) · [record](https://hal.science/hal-00019978) · [doi:10.1016/0890-5401(92)90063-L](https://doi.org/10.1016/0890-5401%2892%2990063-L) | any automaton-side formulation; and the origin of `L2` (`M-PST-001`) |

Open-access and already usable without a library: Kirsten 2005, *Distance
desert automata and the star height problem*, RAIRO-ITA **39**(3):455–509,
[doi:10.1051/ita:2005027](https://doi.org/10.1051/ita:2005027), free PDF at
[numdam](https://www.numdam.org/articles/10.1051/ita:2005027.pdf) — restricted
star height only, but it is the standard modern restatement of Hashiguchi's
machinery and may carry the relative definition in usable form.

Not claimed anywhere above: that `r_SF = gsh`; that `r_SF` is computable
(minimizing over all star-free labellings is an infinite search); that
`L2 ∉ 𝒮₁`; that any language has generalized star height ≥ 2.
