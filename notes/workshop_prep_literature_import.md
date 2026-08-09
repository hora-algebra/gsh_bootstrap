# Literature and method imports from the unversioned workshop-prep repository

**Provenance.** A second local repository, `~/Codes/Generalized Star Height
Problem/` (branch `feature/workshop-prep`, 4 commits, 33 files, **no remote**),
was drafted 2026-07-22 for ZMC workshop preparation. Its provenance headers
read "drafted 2026-07-22 by Claude, human review: (pending)", so everything
below enters this repository as `UNREVIEWED` regardless of how the source repo
labelled it. This note reconstructs the content that exists nowhere in
gsh_bootstrap; it does not import the source repo's blueprint, prompts, or
Lean skeleton. Ledger rows: `LIT-LDID-DICHO-01`, `LIT-CHOHUYNH-01`,
`LIT-BARRINGTON-01`, `LIT-NC1-BARRIER-01`, `LIT-NEGSEARCH-01`.

## 1. The ld-identity dichotomy (Pin 1978 + PST 1992)

The one statement in the source repo that names a precise target for the
*separation* direction:

> If the class of languages of generalized star height ≤ 1 is closed under
> arbitrary inverse morphisms (i.e. forms a variety of languages), then every
> regular language has generalized star height ≤ 1.

Mechanism: Pin 1978 shows every finite monoid divides the syntactic monoid of
some `F*` with `F` finite. Dually, by Pin's 2017 survey (p. 6, *Open problems
about regular languages, 35 years later*), exhibiting a **single nontrivial
ld-identity** satisfied by all languages of height ≤ 1 would prove that a
language of height ≥ 2 exists — and no such identity is known. ("ld" = closed
under inverse length-decreasing morphisms; the identity is a profinite
identity in the ld sense.)

Two consequences for this repository:

- The height-1 class **is** closed under Boolean operations, concatenation,
  quotients, and inverse *alphabetic* / length-decreasing morphisms (PST 1992;
  partially formalized here as `GSH.hasHeightAtMost_comap` and
  `HasHeightAtMost.inverseLetterMap`). The dichotomy says the missing closure
  — arbitrary inverse morphisms — is not a technical gap but the whole
  problem: proving it proves total collapse.
- Any candidate lower-bound invariant must, in particular, be an ld-identity
  or refine one. This sharpens `N-LOWER-001`.

## 2. Complexity anchors

- **Decidability floor.** Height 0 (star-free) is decidable and
  PSPACE-complete: Cho–Huynh 1991, *Finite-automaton aperiodicity is
  PSPACE-complete*, Theoret. Comput. Sci. 88 (1991) 99–116; Stern 1985 is
  prior. No standalone result on decidability of "height ≤ 1" was found
  (search dated 2026-07-22).
- **Circuit-complexity connection.** Barrington 1989, *Bounded-width
  polynomial-size branching programs recognize exactly those languages in
  NC¹*, J. Comput. System Sci. 38 (1989) 150–164: width-5 branching programs
  capture NC¹, with the non-solvability of `A_5` carrying the proof, so the
  `A_5` word problem is NC¹-complete. Word problems of solvable groups are
  believed (not cited as proved in the source repo) to sit in ACC⁰-type
  classes, and ACC⁰ vs NC¹ is open. **Speculative barrier program**: if a map
  from expression height to circuit resources showed that a proof of
  `gsh(W(A_5)) ≥ 2` implies an ACC⁰ ≠ NC¹-type separation, that would be an
  independent result explaining the sixty-year gap. No such map is
  constructed anywhere.

## 3. Dated negative literature searches (all 2026-07-22)

Recorded because a negative search is refutable evidence with a date, and
repeating one wastes a session. None of these establishes absence; each is
"not found by this search on this date".

| Search | Outcome |
|---|---|
| arXiv full-text, "generalized/generalised star-height" | only Bourne–Ruškuc 2016; no direct progress |
| Semantic Scholar, citations of PST 1992 since 2018 | zero |
| arXiv, cohomology × regular languages / syntactic monoids | zero hits |
| public Lean code (GitHub-wide): star-free, syntactic monoid, aperiodic, Schützenberger, Krohn–Rhodes | zero hits |
| primary source naming `A_5` as Pin's candidate | none exists — never write "Pin proposed A_5" |
| standalone decidability result for "gsh ≤ 1" | not found |
| any lower-bound technique beyond 0 vs ≥ 1 | not found (consistent with `N-LOWER-001`) |

The Lean-gap search predates this repository's own Schützenberger
formalization (`LEAN-SCHUTZ-01`, 2026-07-28), which as far as these searches
show remains the only public Lean treatment of the hard direction.

## 4. arXiv items absent from this repository

Profinite/duality line, flagged in the source repo as the active adjacent
field: `arXiv:1609.07736` (van Gool–Steinberg), `arXiv:2203.03286`
(Gehrke–van Gool, book), `arXiv:2402.13086` (Moreau), `arXiv:2506.14134`
(Sin'ya–Yuyama, measure-theoretic independence of star-free and group
languages), `arXiv:2406.18477` (Margolis–Rhodes–Schilling, decidability of
Krohn–Rhodes complexity). Related and already in `docs/CommonBiblio20240922.bib`
but never cited in prose here: `arXiv:1512.04389` (Uramoto) and
`arXiv:2411.06358` (Hora, *Topoi of automata I* — relevant to the `BLOCKED`
topos route of `PROGRESS.md`).

## 5. The sanity battery (imported method, not a claim)

Before investing in a candidate separation invariant `I`, evaluate it on:
(a) star-free languages; (b) word problems of `Z/nZ` (commutative ⇒ height
≤ 1, Henneman); (c) word problems of nilpotent class-2 groups and all groups
of order < 12 (PST); (d) `L(u,k,n)` with `|u| ≤ 2` (PST) and the
Bourne–Ruškuc factor-counting languages; (e) `Σ*`. If `I` fails to be trivial
on any of these, discard or refine, and log the dead invariant with its cause
of death (∪ / ¬ / concatenation / star-of-star-free / battery case). The test
set (b)–(d) is exactly this repository's known-upper-bound inventory, so the
battery can be run against the committed artifacts. The companion discipline:
a lower-bound proof must show `I` trivial on **every** height-≤ 1 language by
induction on expression syntax — the concatenation and star cases are where
candidate invariants die, per the source repo's failure taxonomy.
