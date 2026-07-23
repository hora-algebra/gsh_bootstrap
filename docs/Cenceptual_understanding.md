# Conceptual understanding: generalized star height, hyperconnected quotients, and isotropy

> **Status.** This note separates established facts, precise reformulations, and conjectural bridges. It does **not** claim a solution of the generalized star-height problem.
>
> **Filename.** The spelling `Cenceptual_understanding.md` is retained intentionally to match the requested repository path.

## 0. Executive summary

Fix a finite alphabet $A$. Define

\[
\mathcal B_A
:=
\operatorname{QBool}
\{K^*\mid K\subseteq A^*\text{ is star-free}\},
\]

where `QBool` denotes closure under Boolean operations and left/right quotients. The languages of generalized star height at most one are

\[
\operatorname{GSH}_1(A)=\operatorname{SF}(\mathcal B_A),
\]

where $\operatorname{SF}(-)$ is the star-free closure used in the Place--Zeitoun framework.

For a surjective recognizing morphism $\alpha:A^*\twoheadrightarrow M$ and an idempotent $e\in M$, Place--Zeitoun attach the local monoid

\[
\operatorname{Orb}^{\mathcal B_A}_e(\alpha)
=
\{ete\mid (e,t)\text{ is a }\mathcal B_A\text{-pair}\}
\subseteq eMe.
\]

The generalized star-height problem is therefore equivalent to the assertion that all these local monoids are aperiodic.

The categorical interpretation is:

1. $eMe$ is the endomorphism monoid of the object $e$ in the Karoubi envelope $\operatorname{Kar}(M)$.
2. A finite monoid is aperiodic iff the maximal subgroupoid of its Karoubi envelope is discrete.
3. Thus $\operatorname{Orb}^{\mathcal B_A}_e(\alpha)$ measures the **residual isotropy at the idempotent/essential point $e$ after observation by $\mathcal B_A$**.
4. Hora's language-class/syntactic-topos construction assigns to $\mathcal B_A$ a smallest hyperconnected quotient recognizing it.
5. The Kobin/Navir direction suggests constructing an isotropy-generated subtopos and then taking its smallest containing hyperconnected quotient.

This leads to the central conjectural comparison:

\[
\boxed{
\operatorname{Hull}_{\mathrm{hc}}(\mathcal I_A)
\simeq
\mathcal Q_{\mathcal B_A},
}
\]

where $\mathcal I_A$ is an appropriately defined isotropy subtopos and $\mathcal Q_{\mathcal B_A}$ is the hyperconnected quotient corresponding to $\mathcal B_A$.

The phrase “isotropy subtopos” is not yet canonical enough for the boxed statement to be a theorem. The main task is to make $\mathcal I_A$ precise and prove that its hyperconnected hull recognizes exactly $\mathcal B_A$.

---

## 1. The language-theoretic layer

### 1.1 The base local variety $\mathcal B_A$

Let $\operatorname{SF}_0(A)$ be the class of star-free languages over $A$. Set

\[
\mathcal G_A
=
\{K^*\mid K\in\operatorname{SF}_0(A)\}.
\]

Then define

\[
\mathcal B_A
=
\operatorname{QBool}(\mathcal G_A).
\]

The purpose of $\mathcal B_A$ is to isolate the languages produced by **one primitive use of iteration**, before allowing arbitrary star-free composition around them.

There are three distinct levels that should not be conflated:

| notation | meaning |
|---|---|
| $\operatorname{SF}_0(A)$ | ordinary star-free languages |
| $\mathcal B_A$ | quotient/Boolean closure of $K^*$ with $K$ star-free |
| $\operatorname{GSH}_1(A)$ | all generalized-height-$\leq1$ languages |

The exact relation is

\[
\operatorname{GSH}_1(A)=\operatorname{SF}(\mathcal B_A).
\]

Thus the hyperconnected quotient attached directly to $\mathcal B_A$ should be regarded as the **base observer for one-star phenomena**, not automatically as the whole height-one class.

### 1.2 Separation and $\mathcal B_A$-pairs

For a surjective morphism $\alpha:A^*\twoheadrightarrow M$, a pair $(s,t)\in M^2$ is a $\mathcal B_A$-pair when there is no language $D\in\mathcal B_A$ satisfying

\[
\alpha^{-1}(s)\subseteq D,
\qquad
D\cap\alpha^{-1}(t)=\varnothing.
\]

Equivalently, $s$ and $t$ remain indistinguishable by the observations supplied by $\mathcal B_A$.

For an idempotent $e\in M$, define

\[
\operatorname{Orb}^{\mathcal B_A}_e(\alpha)
=
\{ete\mid (e,t)\text{ is a }\mathcal B_A\text{-pair}\}.
\]

Place--Zeitoun's theorem gives the operative criterion

\[
L\in\operatorname{SF}(\mathcal B_A)
\iff
\operatorname{Orb}^{\mathcal B_A}_e(\alpha_L)
\text{ is aperiodic for every idempotent }e.
\]

Hence the generalized star-height conjecture becomes

\[
\forall A,\ \forall L\in\operatorname{Reg}(A),\ \forall e\in E(M_L),
\quad
\operatorname{Orb}^{\mathcal B_A}_e(\alpha_L)
\text{ is aperiodic}.
\]

---

## 2. Karoubi envelopes and total isotropy

### 2.1 The local monoid $eMe$

Regard a monoid $M$ as a one-object category. Its Karoubi envelope $\operatorname{Kar}(M)$ has

\[
\operatorname{Ob}(\operatorname{Kar}(M))=E(M)
\]

and, with one standard convention,

\[
\operatorname{Hom}_{\operatorname{Kar}(M)}(e,f)=fMe.
\]

In particular,

\[
\operatorname{End}_{\operatorname{Kar}(M)}(e)=eMe.
\]

Therefore the Place--Zeitoun orbit is not merely analogous to a Karoubi-local object: it is literally a submonoid of the endomorphism monoid at $e$.

### 2.2 Why the full Karoubi groupoid is needed

For a finite monoid $N$, let

\[
\operatorname{IsoKar}(N)
\subseteq
\operatorname{Kar}(N)
\]

be the maximal subgroupoid: it has all idempotent objects and only the invertible Karoubi arrows.

Then

\[
N\text{ is aperiodic}
\iff
\operatorname{IsoKar}(N)
\text{ is discrete}.
\]

It is not enough to inspect only the units of $N$ at its global identity. A nontrivial maximal subgroup may occur at another idempotent. Consequently, the correct categorical form of the orbit condition is

\[
\operatorname{IsoKar}
\bigl(\operatorname{Orb}^{\mathcal B_A}_e(\alpha)\bigr)
\text{ is discrete for every }e.
\]

This is the “total isotropy” formulation of the generalized star-height problem.

### 2.3 Essential points

For a finite monoid action topos, an idempotent $e$ determines a retract of the regular action and hence a projective object. Under the usual variance convention, evaluation at that retract has the form

\[
X\longmapsto Xe.
\]

This is the point at which the local endomorphism monoid $eMe$ becomes the endomorphism algebra of an essential-point-like probe. Accordingly,

\[
\operatorname{Orb}^{\mathcal B_A}_e(\alpha)
\]

should be read as the endomorphisms that remain locally visible at $e$ after passing through the $\mathcal B_A$ observer.

A precise theorem must fix left/right action conventions and identify the exact category of points or projectives being used.

---

## 3. Hyperconnected quotients and language classes

### 3.1 Ambient topoi

Two ambient categories should be kept separate.

1. $A\text{-}\mathbf{Set}$: all $A^*$-actions.
2. $A\text{-}\mathbf{Set}_{\mathrm{of}}$: orbit-finite $A^*$-actions, corresponding to regular languages.

The generalized star-height problem is a problem about regular languages, so the natural local-variety comparison should ultimately take place over the orbit-finite/regular topos.

### 3.2 The quotient corresponding to $\mathcal B_A$

Hora's syntactic-topos construction assigns to a quotient-stable language class $C$ the smallest hyperconnected quotient recognizing all languages in $C$. Write

\[
q_C:
A\text{-}\mathbf{Set}
\twoheadrightarrow
\mathcal Q_C.
\]

For the present problem,

\[
q_{\mathcal B_A}:
A\text{-}\mathbf{Set}_{\mathrm{of}}
\twoheadrightarrow
\mathcal Q_{\mathcal B_A}
\]

is the intended object, assuming the local-variety/hyperconnected-quotient correspondence is available in the required orbit-finite setting.

Equivalently, $\mathcal Q_{\mathcal B_A}$ is generated, as a hyperconnected quotient, by the syntactic objects of the languages $K^*$ with $K$ star-free:

\[
\mathcal Q_{\mathcal B_A}
=
\bigvee_{K\in\operatorname{SF}_0(A)}
\mathcal T(K^*),
\]

where $\mathcal T(-)$ denotes the syntactic topos/quotient and the join is taken in the lattice of hyperconnected quotients.

The equation above is a target formulation; its exact status depends on the precise version of the language-class correspondence being used.

### 3.3 The local-state-classifier formulation

Let $\Xi$ be the local state classifier of the ambient topos. Hyperconnected quotients correspond to internal filters in $\Xi$.

If $F_{\mathcal B_A}$ denotes the filter associated with $\mathcal Q_{\mathcal B_A}$, then conceptually

\[
F_{\mathcal B_A}
=
\left\langle
\xi_{\mathcal L}(K^*)
\mid
K\text{ star-free}
\right\rangle.
\]

This gives a concrete comparison problem: construct an isotropy-generated internal filter $F_{\mathrm{iso}}$ and ask whether

\[
F_{\mathrm{iso}}=F_{\mathcal B_A}.
\]

This filter equality is likely the cleanest formal version of the proposed Navir--Hora bridge.

---

## 4. The Kobin/Navir direction

### 4.1 Proposed construction

The user-supplied Kobin/Navir idea is interpreted as follows.

1. Construct a subtopos
   \[
   i_A:\mathcal I_A\hookrightarrow A\text{-}\mathbf{Set}_{\mathrm{of}}
   \]
   generated by the relevant isotropy data.
2. Regard hyperconnected quotients as full subcategories of the ambient topos via their inverse-image functors.
3. Form the smallest hyperconnected quotient whose essential image contains $\mathcal I_A$:
   \[
   \operatorname{Hull}_{\mathrm{hc}}(\mathcal I_A)
   :=
   \bigwedge
   \left\{
   \mathcal Q\in\operatorname{HQ}(A\text{-}\mathbf{Set}_{\mathrm{of}})
   \mid
   \mathcal I_A\subseteq\mathcal Q
   \right\}.
   \]
4. Compare this hull with $\mathcal Q_{\mathcal B_A}$.

The completeness of the lattice of hyperconnected quotients supplies the existence of the hull once “$\mathcal I_A\subseteq\mathcal Q$” has been made type-correct.

### 4.2 Central conjecture

The proposed comparison is

\[
\boxed{
\operatorname{Hull}_{\mathrm{hc}}(\mathcal I_A)
\simeq
\mathcal Q_{\mathcal B_A}.
}
\]

Equivalent forms to investigate are:

#### Language-class form

\[
\mathcal L
\bigl(\operatorname{Hull}_{\mathrm{hc}}(\mathcal I_A)\bigr)
=
\mathcal B_A.
\]

#### Generator form

\[
\operatorname{Hull}_{\mathrm{hc}}(\mathcal I_A)
=
\bigvee_{K\text{ star-free}}\mathcal T(K^*).
\]

#### Filter form

\[
F_{\mathrm{iso}}
=
\left\langle
\xi_{\mathcal L}(K^*)
\mid K\text{ star-free}
\right\rangle.
\]

The filter form is preferred for a first proof attempt because it reduces the comparison to generators and closure operations in the local state classifier.

### 4.3 What exactly should $\mathcal I_A$ be?

The phrase “the subtopos consisting of all isotropy” is not yet a definition. At least four candidates must be distinguished.

1. **Isotropy-support subtopos:** generated by objects on which the localic isotropy group acts nontrivially.
2. **Essential-point isotropy subtopos:** generated by the projective/essential-point probes associated with idempotents and their automorphism groups.
3. **Karoubi-isotropy subtopos:** generated by the maximal subgroupoids of Karoubi envelopes of finite transition monoids.
4. **Relative isotropy subtopos:** generated only by isotropy surviving the $\mathcal B_A$-observation relation.

The fourth candidate is closest to the Place--Zeitoun criterion, but using it to define $\mathcal I_A$ risks circularity. A useful construction should be definable before knowing $\mathcal B_A$ and then be proved to generate the same quotient.

### 4.4 Subtopos versus isotropy quotient

There is an important variance issue.

- A **subtopos** is presented by a geometric inclusion.
- A **hyperconnected quotient** is presented by a hyperconnected geometric morphism and can be regarded as a full subcategory closed under subquotients.
- The standard **isotropy quotient** of a topos kills or divides out an isotropy action; it is not automatically the same object as a subtopos generated by isotropy-bearing objects.

Therefore the Navir construction must be checked for its exact universal property. “Containing isotropy” and “quotienting by isotropy” point in opposite categorical directions.

---

## 5. Why the conjectural identification is plausible

### 5.1 One star creates a return/loop layer

If $K$ is star-free, its syntactic monoid is aperiodic. Passing to $K^*$ introduces arbitrary repetition of $K$-blocks. Algebraically, the new phenomenon is concentrated in return monoids and local monoids at idempotents.

This makes $K^*$ a natural generator for isotropy that arises from **one layer of repetition over an aperiodic base**.

### 5.2 Quotients and Boolean operations match the quotient formalism

The closure operations used to form $\mathcal B_A$ are precisely the operations naturally visible in the language-class/hyperconnected-quotient correspondence:

- Boolean operations combine predicates on the same recognizing object;
- left/right quotients correspond to the word action and state change;
- generated hyperconnected quotients combine recognizers by lattice operations.

Thus the definition of $\mathcal B_A$ is structurally compatible with taking the hyperconnected hull of a family of isotropy generators.

### 5.3 Place--Zeitoun orbits are relative isotropy

The orbit

\[
\operatorname{Orb}^{\mathcal B_A}_e(\alpha)
\]

retains precisely those local endomorphisms that cannot be separated from $e$ by $\mathcal B_A$. Its maximal Karoubi subgroupoid is therefore a candidate for the isotropy remaining after reflection to $\mathcal Q_{\mathcal B_A}$.

The generalized star-height problem then asks whether this relative isotropy is always trivial for finite syntactic objects.

---

## 6. Why the identification is not automatic

### 6.1 $eMe$ contains more than isotropy

The local monoid $eMe$ contains noninvertible endomorphisms as well as groups. The Place--Zeitoun orbit is first a monoid; isotropy appears only after taking maximal subgroups at all its idempotents.

A construction using only automorphism groups may forget noninvertible data needed to determine which isotropy survives.

### 6.2 Star is not a standard topos operation

The operation

\[
K\longmapsto K^*
\]

is not itself one of the elementary closure operations supplied by a Grothendieck topos. A proof must explain why the proposed isotropy generators are exactly the syntactic data created by this operation.

### 6.3 All isotropy may be too large

The total isotropy of the regular-language topos includes arbitrary finite group behavior. By contrast, $\mathcal B_A$ is generated by stars of **star-free** languages. It may encode a particular class of return-group phenomena rather than every possible group action.

Thus one possible outcome is a strict inclusion

\[
\mathcal Q_{\mathcal B_A}
\subsetneq
\operatorname{Hull}_{\mathrm{hc}}(\mathcal I_A).
\]

### 6.4 $\mathcal B_A$ is not the height-one class

Even if the isotropy hull equals $\mathcal Q_{\mathcal B_A}$, the generalized-height-one class is

\[
\operatorname{SF}(\mathcal B_A),
\]

not $\mathcal B_A$ itself. The second stage is a **relative anisotropy theorem** identifying star-free closure with the disappearance of residual isotropy.

### 6.5 The orbit-finite correspondence needs a theorem

The exact correspondence between local varieties of regular languages and hyperconnected quotients of the orbit-finite automata topos is part of the intended Topoi-of-automata framework, but the version required here must be stated and checked explicitly before it is used as a black box.

---

## 7. Precise theorem package to target

### Theorem A: fixed-alphabet local Eilenberg/topos correspondence

Construct an order isomorphism

\[
\operatorname{LocalVar}(A)
\cong
\operatorname{HQ}
\bigl(A\text{-}\mathbf{Set}_{\mathrm{of}}\bigr)
\]

with explicit compatibility between recognition, generated language classes, and the local-state-classifier filter.

### Theorem B: isotropy generator theorem

Define $\mathcal I_A$ without reference to $\mathcal B_A$ and prove

\[
\operatorname{Hull}_{\mathrm{hc}}(\mathcal I_A)
=
\bigvee_{K\text{ star-free}}\mathcal T(K^*).
\]

This is the central Navir--Hora comparison.

### Theorem C: orbit/isotropy comparison

For every finite recognizing morphism $\alpha:A^*\twoheadrightarrow M$ and idempotent $e\in M$, identify

\[
\operatorname{IsoKar}
\bigl(\operatorname{Orb}^{\mathcal B_A}_e(\alpha)\bigr)
\]

with the relative isotropy groupoid of the $e$-probe after applying the hyperconnected reflection to $\mathcal Q_{\mathcal B_A}$.

### Theorem D: relative anisotropy theorem

For a regular language $L$,

\[
L\in\operatorname{SF}(\mathcal B_A)
\iff
\text{all relative isotropy groupoids of }L
\text{ over }\mathcal Q_{\mathcal B_A}
\text{ are discrete}.
\]

This should recover the Place--Zeitoun orbit theorem in topos-theoretic language.

### Corollary target: generalized star height

The generalized star-height conjecture becomes

\[
\forall A,\ \forall L\in\operatorname{Reg}(A),
\quad
L\text{ is relatively anisotropic over }
\operatorname{Hull}_{\mathrm{hc}}(\mathcal I_A).
\]

A counterexample is a finite syntactic object with nontrivial residual isotropy.

---

## 8. Profinite and semi-Galois reformulation

Let

\[
\widehat{A^*}_{\mathcal B_A}
\]

be the free profinite/pro-$\mathcal B_A$ monoid associated with the fixed-alphabet local variety $\mathcal B_A$.

For $\alpha:A^*\twoheadrightarrow M$, $\mathcal B_A$-separability of two fibres is equivalent to disjointness of their closures in this completion. Thus

\[
(s,t)\text{ is a }\mathcal B_A\text{-pair}
\iff
\overline{\alpha^{-1}(s)}
\cap
\overline{\alpha^{-1}(t)}
\neq\varnothing.
\]

The proposed isotropy object should therefore also admit a profinite description. A likely target is the maximal progroupoid inside the Karoubi envelope of $\widehat{A^*}_{\mathcal B_A}$, or a semi-Galois category of finite continuous actions generated by its isotropy.

The expected comparison diagram is

\[
\begin{array}{ccc}
\text{local variety }\mathcal B_A
&\longleftrightarrow&
\widehat{A^*}_{\mathcal B_A}
\\[2mm]
\updownarrow&&\updownarrow
\\[2mm]
\text{hyperconnected quotient }\mathcal Q_{\mathcal B_A}
&\longleftrightarrow&
\text{continuous-action/semi-Galois category}
\\[2mm]
\updownarrow&&\updownarrow
\\[2mm]
\text{relative isotropy at essential points}
&\longleftrightarrow&
\text{pro-Karoubi isotropy groupoid}.
\end{array}
\]

This is where the Uramoto semi-Galois perspective and the Kobin/Navir construction should meet.

---

## 9. The $A_5$ laboratory

For a surjection

\[
\alpha:A^*\twoheadrightarrow A_5,
\]

there is only one idempotent in the target group, namely $1$. Hence

\[
\operatorname{Orb}^{\mathcal B_A}_1(\alpha)
\leq A_5
\]

is a subgroup.

For the identity fibre $L_1=\alpha^{-1}(1)$,

\[
\operatorname{gsh}(L_1)\leq1
\iff
\operatorname{Orb}^{\mathcal B_A}_1(\alpha)=\{1\}.
\]

Topos-theoretically, this says that the $A_5$ isotropy at the relevant essential point is completely killed by $\mathcal B_A$-separation.

The known easy generating systems give explicit separators and therefore trivial residual isotropy. The hard $(2,3,5)$ marking is the natural test case for whether nontrivial isotropy survives the proposed reflection.

This stresses that the invariant must depend on the marked morphism

\[
A^*\twoheadrightarrow A_5,
\]

not merely on the abstract group $A_5$.

---

## 10. Immediate checks in Kobin and Topoi of automata II

Before promoting the central conjecture, extract the following data from the exact Navir/Kobin source.

1. What is the ambient topos?
2. Is the construction a subtopos, a quotient topos, or an isotropy quotient?
3. Which isotropy is used: point isotropy, localic isotropy, inertia, or automorphisms in a groupoid completion?
4. What is the universal property of the resulting object?
5. Does “smallest hyperconnected quotient containing it” exist internally in the stated ambient category?
6. How is the corresponding local-state-classifier filter generated?
7. Is the construction stable under passage to orbit-finite objects?
8. Does it retain the alphabet marking $A^*\to M$?

The exact Kobin locator for the Navir construction should be inserted here once identified. Two nearby Kobin notes already relevant to the surrounding programme are:

- `ideas/2026-07-08_prodiscrete-galois-monoids-language-classes.md`;
- `ideas/2026-07-14_topoi-of-automata-iii-geometry-of-sigma-sets.md`.

---

## 11. Computational and formal tests

### Finite-monoid test

For a small $A$-generated finite monoid $M$:

1. enumerate idempotents $e$;
2. construct $\operatorname{Kar}(M)$;
3. enumerate maximal subgroups of every $eMe$;
4. approximate $\mathcal B_A$ by bounded star-free generators $K$;
5. compute the corresponding approximate orbit monoids;
6. compare their maximal subgroupoids with the isotropy generators predicted by $\mathcal I_A$.

### Local-state-classifier test

For finite quotients, compare two generated filters:

\[
F_{\mathrm{star}}
=
\left\langle\xi_{\mathcal L}(K^*)\mid K\text{ star-free}\right\rangle
\]

and

\[
F_{\mathrm{iso}}
=
\left\langle\text{Navir isotropy generators}\right\rangle.
\]

Equality on all finite test objects would not prove the theorem, but disagreement would quickly refute the proposed identification.

### Lean interfaces

The formalization should keep the following objects separate:

- `KaroubiEnvelope M`;
- `LocalMonoid e = eMe`;
- `MaximalSubgroupoid (KaroubiEnvelope M)`;
- `CPair C α s t`;
- `Orbit C α e`;
- `Aperiodic (Orbit C α e)`;
- the language-class/hyperconnected-quotient Galois connection;
- the isotropy-generated filter and its hyperconnected hull.

---

## 12. Claim-status ledger

| claim | status |
|---|---|
| $\operatorname{GSH}_1(A)=\operatorname{SF}(\mathcal B_A)$ | established by syntax/closure argument, subject to exact adopted definitions |
| $\operatorname{Orb}^{\mathcal B_A}_e(\alpha)\subseteq eMe$ | definition-level fact |
| $eMe=\operatorname{End}_{\operatorname{Kar}(M)}(e)$ | standard fact, convention-sensitive |
| finite $N$ aperiodic iff $\operatorname{IsoKar}(N)$ is discrete | standard finite-semigroup reformulation |
| orbit aperiodicity is “relative isotropy vanishing” | precise programme; categorical identification still to prove |
| $\mathcal Q_{\mathcal B_A}$ is the join of the $\mathcal T(K^*)$ | expected from the syntactic-topos Galois connection; exact hypotheses to check |
| the Navir isotropy subtopos $\mathcal I_A$ is canonically defined | unresolved until the exact Kobin construction is extracted |
| $\operatorname{Hull}_{\mathrm{hc}}(\mathcal I_A)\simeq\mathcal Q_{\mathcal B_A}$ | central conjecture |
| this conjecture solves generalized star height | no; it supplies the base quotient, after which a relative-anisotropy theorem is still required |
| every regular language is relatively anisotropic over this hull | equivalent target for the affirmative generalized star-height conjecture |

---

## 13. Recommended next mathematical move

The next task should not be another global attempt at generalized star height. It should be the following comparison lemma.

> **Comparison problem.** Define the Navir isotropy-generated internal filter $F_{\mathrm{iso}}$ in the local state classifier of $A\text{-}\mathbf{Set}_{\mathrm{of}}$. Prove or disprove
> \[
> F_{\mathrm{iso}}
> =
> \left\langle
> \xi_{\mathcal L}(K^*)
> \mid K\subseteq A^*\text{ star-free}
> \right\rangle.
> \]

This has three advantages.

1. It is a sharply stated equality in a complete lattice.
2. Each inclusion can be attacked independently.
3. It directly exposes whether “one star over an aperiodic language” is the same phenomenon as “isotropy generated inside the automata topos.”

Only after this comparison is settled should the project attempt the stronger relative-anisotropy theorem needed for the full generalized star-height problem.

---

## References and source pointers

- R. Hora, *Topoi of automata II: Hyperconnected geometric morphisms, syntactic monoids, and language classes*, in preparation.
- R. Hora, *Internal Parameterization of Hyperconnected Quotients*.
- T. Uramoto, *Semi-Galois Categories I: The Classical Eilenberg Variety Theory*.
- T. Place and M. Zeitoun, work on star-free closure and $\mathcal C$-orbits.
- J.-E. Pin, *Mathematical Foundations of Automata Theory*.
- S. Henry, *The Localic Isotropy Group of a Topos*.
- Kobin notes listed in Section 10.
