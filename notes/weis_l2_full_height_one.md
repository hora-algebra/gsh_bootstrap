# Full L2 has generalized star-height 1 (and restricted star-height 2)

Date: 2026-07-25. Status of the main claim: `COMPUTED` (complete finite
proof by machine; program audit and independent human re-derivation are
still open). Claims: `WEIS-L2-GSH-01`, `WEIS-L2-RSH-01`, `UNIV-SUBGRP-01`.

## 0. The language and what was open

    L2 = L( ( a b* a  |  b a* b (a b* a)* b a* b )* )   over {a, b}

printed exactly this way in Weis 2011 (UMass thesis) p.115 and *proposed
by Pin–Straubing–Thérien 1992* ("proposed in [30]"); see
`notes/weis_2011_primary_audit.md` for the audit of the attribution.

Previously recorded in this repository:

- `WEIS-L2-AUDIT-01` (`CITED`): minimal DFA has 6 states, syntactic monoid
  is a non-nilpotent group of order 48, isomorphic to `C₂ × S₄`.
- `WEIS-L2-OPEN-01` (`CITED`): Weis leaves the generalized star-height of
  **full** L2 open; only a restricted subset (≥ 4 a's between b's) was
  shown to have height 1.
- `WEIS-L2-NOTFN-01` (`COMPUTED`): membership in full L2 is **not** a
  function of this repository's certified stage-2 feature family, so
  `WEIS-L2-M2-01` does not decide it.

This note closes the question: **gsh(L2) = 1**. The method is the
"anchor" criterion of RESULTS.md §5.7, applied not to the 6-point action
but to a *quotient* action on 4 points.

## 1. Ground truth, fixed once

Compiling the printed expression (exact subset construction + Moore
minimization, `scripts/research/weis_l2_full_gsh1.py` step 0) gives the 6-state
minimal DFA, and it is exactly the walk automaton of

    ψ₆(a) = (0 1)(3 4),    ψ₆(b) = (0 2 3 5),    start = accept = 0,

on the six vertices of an octahedron (vertices paired antipodally by the
central involution z). So L2 = φ⁻¹(Stab(0)) for φ: {a,b}* → G ≤ S₆ with
G = ⟨ψ₆(a), ψ₆(b)⟩ of order 48, and Stab(0) of order 8, index 6.

Nothing below depends on the earlier sessions' hand-entered automaton:
the script derives the automaton from the printed regex and asserts the
agreement.

## 2. Why the naive anchor attempt fails, and the fix

The anchor criterion (RESULTS.md §5.7) asks for a point whose
*first-return* language is star-free; then the star of that language is
the only star needed. On the six vertices this fails: vertices 0 and 3
are moved by **both** letters, so the off-anchor part still contains
b-cycles and the first-return language is not star-free.

The fix is to change the action. Let z be the unique central
fixed-point-free involution of G (the antipodal map; the script finds it
by search and asserts uniqueness). The 8 faces of the octahedron (3-subsets
containing no antipodal pair) fall into 4 z-orbits — the 4 **diagonals**
of the dual cube. On them G acts through

    ψ(a) = (D₂ D₃)        — a transposition,
    ψ(b) = (D₀ D₃ D₂ D₁)  — a 4-cycle

(machine-verified cycle types). The two diagonals moved by **both**
letters are exactly `{D₂, D₃}` — and they are the support of ψ(a). These
are the anchors.

## 3. The height-1 atoms

Fix an anchor d ∈ {D₂, D₃}. Delete d from the 4-point walk graph: the
only remaining cycles are a-self-loops, because ψ(a) is a transposition
supported on the anchor pair and ψ(b) is a single 4-cycle. Since

    a* = ¬(⊤ b ⊤)          (star-free: "no b occurs")

each escape language S_d(x) (paths d → x avoiding d) is **star-free**, and
so is the first-return language R_d. Concretely, with the labelling the
script produces (D₂: a-self-loops at D₀ and D₁; D₃: likewise):

    R_{D₂} = (a | b a* b a* b)(a | b)
    R_{D₃} = (a | b) a  |  (a | b) b a* b a* b

    S_{D₂} = { D₃ ↦ a | b a* b a* b,   D₁ ↦ b a*,   D₀ ↦ b a* b a* }
    S_{D₃} = { D₂ ↦ a | b,   D₁ ↦ (a | b) b a*,   D₀ ↦ (a | b) b a* b a* }

The script asserts `height(R_{D₂}) = height(R_{D₃}) = 0`. Then

    K_d = (R_d)*                          — star-height 1
    W_d(x) = K_d · S_d(x)  (x ≠ d),  W_d(d) = K_d

and W_d(x) = { w : the d-walk of w ends at x }, by the unique
factorization at the last visit to d. Star-height 1.

## 4. Separating the fibers

ψ alone cannot separate G: Stab_ψ(D₂) ∩ Stab_ψ(D₃) still contains a
transposition of the other two diagonals. Add the two letter parities.
The script checks, over all 48 elements:

- the map w ↦ (|w|_a mod 2, |w|_b mod 2) is well defined on G
  (i.e. it factors through G, checked edge by edge on the Cayley graph —
  equivalently z ∉ G′), and
- (parities, ψ) is **injective** on G.

Both parity languages are height 1 (`(N l N l)* (N l)^r N` with N
star-free). Hence every fiber φ⁻¹(g) is an intersection of four
height-1 languages, and

    L2 = ⋃_{g ∈ Stab(0)} φ⁻¹(g)     (8 fibers)

has generalized star-height ≤ 1.

## 5. Certification

`scripts/research/weis_l2_full_gsh1.py` (Python 3 stdlib, seconds):

1. compiles the printed regex, asserts the 6-state walk automaton;
2. rebuilds G, z, the diagonals, ψ; asserts |G| = 48, cycle types,
   anchor pair, parity well-definedness, injectivity;
3. asserts `height(expression) = 1` syntactically;
4. compiles the expression exactly to a minimal DFA (6 states);
5. cross-checks the compiler against an independent recursive interval
   matcher (all words of length ≤ 7) **and** against Python's `re` engine
   applied to the printed regex (all 8191 words of length ≤ 12);
6. proves language equality with the ground-truth DFA by product
   reachability — a complete finite proof, no sampling;
7. with `--certificate data/certificates/height1_weis_l2_full.json`,
   emits a repository-standard certificate (`gsh-regex-certificate-v1`)
   which `tools/regex_cert.py` — an implementation independent of this
   script, soundness claim `CERT-01` — re-verifies, and which
   `./scripts/check.sh` picks up automatically. Verdict:
   `PASS: equivalent; height=1 <= 1; minimal states expression=6,
   target=6`. So the bound is re-checked on every run of the standard
   checks, by a fourth evaluation path.

Lower bound: the syntactic monoid is a nontrivial group, so L2 is not
star-free (Schützenberger 1965); hence **gsh(L2) = 1 exactly**.

## 6. Restricted star-height: rsh(L2) = 2

`scripts/research/weis_l2_restricted_height.py`. Cited inputs, verified verbatim
in Lombardy–Sakarovitch, *The Universal Automaton* (2008): Def. 2.4
(universal automaton = maximal factorizations), Def. 7.4 (loop
complexity), Thm. 7.5 (Eggan 1963: star height = minimal loop complexity
of an accepting automaton), Thm. 7.10 (Lombardy–Sakarovitch 2003: the
universal automaton of a regular *group* language contains a
subautomaton of minimal loop complexity recognizing it).

**Lemma (`UNIV-SUBGRP-01`).** Let φ: Σ* → G be onto with G finite, H ≤ G
a subgroup, L = φ⁻¹(H). Then the maximal factorizations of L with both
components nonempty are exactly the pairs (Hg⁻¹, gH), g ∈ G; they
correspond bijectively to the left cosets gH; and the universal
automaton restricted to them is deterministic and isomorphic to the coset
automaton, i.e. to the minimal DFA of L.

*Proof.* Factorizations are saturated by the syntactic congruence (if
u ≡ u′ then uY ⊆ L ⟺ u′Y ⊆ L), so we may work with subsets A, B ⊆ G and
the condition AB ⊆ H. Let B ≠ ∅ and pick b₀ ∈ B. From Ab₀ ⊆ H we get
A ⊆ Hb₀⁻¹, so maximality forces A = Hb₀⁻¹; then
B = {b : Hb₀⁻¹b ⊆ H} = {b : b₀⁻¹b ∈ H} = b₀H. Conversely each (Hg⁻¹, gH)
satisfies Hg⁻¹gH = H ⊆ H and is maximal by the same computation, and
Hg⁻¹ = Hg′⁻¹ ⟺ g′ ∈ gH ⟺ gH = g′H. For transitions, Def. 2.4 gives
(Hg⁻¹, gH) --x--> (Hg′⁻¹, g′H) ⟺ Hg⁻¹ φ(x) g′H ⊆ H ⟺ g⁻¹φ(x)g′ ∈ H
⟺ g′H = φ(x)⁻¹gH: exactly one target, and the left language of the
target is Hg⁻¹φ(x). Initial ⟺ 1 ∈ Hg⁻¹ ⟺ gH = H, final ⟺ 1 ∈ gH ⟺
gH = H. Relabelling states by their left languages is the coset
automaton, which for a group language is the minimal DFA. ∎

The two degenerate factorizations (Σ*, ∅), (∅, Σ*) are not accessible /
not co-accessible, and loop complexity is monotone under subgraph
inclusion, so the minimum in Thm. 7.10 is attained on subautomata of the
trim part — the 6-state minimal DFA.

(Consistency check with the literature: TUA remarks after Cor. 7.12 that
for W_q = {w : |w|_a ≡ |w|_b mod 2^q} the universal automaton *is*
isomorphic to the minimal automaton. That is the H = {1} case of the
lemma.)

Exhausting all 2¹² labelled-edge subsets: a subautomaton accepts L2 iff
every state reachable inside it has both letters defined (if a reachable
s lacks c, take u reaching s and v driving the full DFA from δ(s,c) back
to 0 — possible since the coset automaton is strongly connected — then
ucv ∈ L2 has no run). Exactly **one** subset qualifies, the full
automaton, of loop complexity **2**. Hence rsh(L2) = 2.

Consequence: the printed expression has restricted star-height 3, so it
is not even optimal for the restricted measure; and L2 is an explicit
**literature-standard** language with gsh = 1 < rsh = 2.

## 7. What this does and does not settle

- It removes L2 from the list of candidate counterexamples to the
  height-one collapse: the PST-1992 candidate, left open by Weis 2011,
  has generalized star-height 1.
- It does **not** prove `HeightOneForGroup (C₂ × S₄)`: the proof is about
  the specific morphism φ (2 letters) and the specific accepting set
  Stab(0). The full-alphabet statement for S₄ / C₂ × S₄ stays open, as
  does `A5`.
- The next target with the same technique is Weis's L3 (syntactic monoid
  S₅, still open): look for an action of the syntactic group in which the
  letters move exactly the anchor pair. Registered as an obligation.

## 8. Threats to validity

- All bounds are program-checked. The three evaluation paths (exact DFA
  compiler, recursive matcher, Python `re` on the printed regex) agree,
  and the toolchain independently reproduces A4-STD-01 with a *complete*
  proof (`scripts/research/a4_std_dfa_equivalence.py`), but a program audit by a
  second party is not done.
- rsh(L2) = 2 depends on two cited theorems (Eggan; Lombardy–Sakarovitch)
  plus the lemma above. Only the lemma is proved here.
- Novelty is **not** claimed against the whole literature. The searches
  performed (Weis 2011 full text, Pin's star-height surveys, arXiv
  neighbourhood) found no published determination of gsh(L2), but a
  targeted L2-specific prior-art search is required before any external
  write-up.
