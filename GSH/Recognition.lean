import GSH.Challenges.GeneralizedStarHeight
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Congruence.Hom

/-!
# Recognition: automata, monoids, syntactic congruence, aperiodicity

This file collects the recognition-theoretic interface layer in one place
(consolidated 2026-07-23 from `GSH/Automata/DFA.lean`,
`GSH/Monoid/Recognition.lean`, `GSH/Monoid/Syntactic.lean`,
`GSH/StarFree/Aperiodic.lean`, and `GSH/GroupLanguages/Basic.lean`,
definitions unchanged):

1. deterministic finite automata and their languages;
2. recognition of a language by a monoid morphism with an accepting set;
3. the syntactic congruence (proved to be a two-sided congruence), its
   quotient monoid, and the canonical quotient morphism;
4. aperiodicity;
5. the height-one recognition properties `HeightOneForMonoid` /
   `HeightOneForGroup` used by the finite-group ladder.

This file is `sorry`-free.  The two placeholders it used to carry were
removed on 2026-07-25 so that the finite-group ladder downstream had no
unproved declaration in its import closure.  The quotient-monoid obligation
L-SYN-002 was subsequently discharged by packaging the proved contextual
relation as mathlib's `Con`; the Schützenberger interface L-SF-001 remains
open and is recorded in `PROOF_OBLIGATIONS.md`.

That sentence was false until 2026-07-25: this file imports
`GSH.Challenges.GeneralizedStarHeight`, which was where the repository's one
deliberate `sorry` lived, so the *dependency* closure was clean while the
*import* closure was not.  The `sorry` now sits alone in `GSH/Conjecture.lean`,
which nothing here imports, and `GSHTest/Axioms.lean` checks the dependency
claim by sweeping every theorem in the `GSH` namespace rather than a list of
names someone maintained by hand.

`HeightOneForGroup G` says: for **every** finite alphabet `α`, **every**
monoid morphism `φ : α* →* G`, and **every** accepting subset `S ⊆ G`, the
recognized language `φ⁻¹(S)` has generalized star height at most one.
"Recognized by `G`" means membership in such a preimage — *not* that the
syntactic monoid equals `G`.
-/

set_option autoImplicit false

namespace GSH

universe u v

/-! ### 1.  Deterministic finite automata

The core definition does not assume finiteness; finiteness is added by
typeclass hypotheses in algorithms and theorems that need it. -/

structure DFA (α : Type u) (σ : Type v) where
  step : σ → α → σ
  start : σ
  accept : Set σ

namespace DFA

variable {α : Type u} {σ : Type v}

/-- Run an automaton from an arbitrary state. -/
def run (M : DFA α σ) : σ → Word α → σ
  | q, [] => q
  | q, a :: w => run M (M.step q a) w

@[simp] theorem run_nil (M : DFA α σ) (q : σ) : M.run q [] = q := rfl

@[simp] theorem run_cons (M : DFA α σ) (q : σ) (a : α) (w : Word α) :
    M.run q (a :: w) = M.run (M.step q a) w := rfl

/-- Running a concatenation factors through the state reached by the prefix. -/
theorem run_append (M : DFA α σ) (q : σ) (u v : Word α) :
    M.run q (u ++ v) = M.run (M.run q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
      simpa using ih (q := M.step q a)

/-- The language accepted from the designated start state. -/
def language (M : DFA α σ) : Language α :=
  {w | M.run M.start w ∈ M.accept}

@[simp] theorem mem_language_iff (M : DFA α σ) (w : Word α) :
    w ∈ M.language ↔ M.run M.start w ∈ M.accept := by
  rfl

end DFA

/-! ### 2.  Recognition by monoids

Recognition data is a morphism from the free monoid of words and an
accepting subset.  The morphism need not be surjective. -/

structure Recognition (α : Type u) (M : Type v) [Monoid M] where
  -- API repair 2026-07-22: `List α →* M` does not elaborate because plain
  -- `List α` carries no `MulOneClass` instance in mathlib; the free monoid on
  -- `α` is `FreeMonoid α`, a definitional synonym for `List α`
  -- (`FreeMonoid.ofList` is the identity equivalence).
  morphism : FreeMonoid α →* M
  accepting : Set M

namespace Recognition

variable {α : Type u} {M : Type v} [Monoid M]

/-- The inverse image of the accepting subset. -/
def language (R : Recognition α M) : Language α :=
  {w | R.morphism (FreeMonoid.ofList w) ∈ R.accepting}

@[simp] theorem mem_language_iff (R : Recognition α M) (w : Word α) :
    w ∈ R.language ↔ R.morphism (FreeMonoid.ofList w) ∈ R.accepting := by
  rfl

end Recognition

/-- Existential recognition by a specified monoid. -/
def RecognizedBy (M : Type v) [Monoid M] {α : Type u} (L : Language α) : Prop :=
  ∃ R : Recognition α M, R.language = L

/-! ### 3.  Syntactic congruence

The contextual relation is first proved to be a two-sided congruence and is
then packaged as mathlib's `Con`.  The quotient monoid and its canonical
surjective morphism are consequently supplied by proved library
constructions rather than by a hand-written quotient instance. -/

/-- Two words are syntactically equivalent when every two-sided context gives
the same membership answer. -/
def SyntacticEq {α : Type u} (L : Language α) (u v : Word α) : Prop :=
  ∀ x y : Word α, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L

namespace SyntacticEq

variable {α : Type u} {L : Language α} {u v w : Word α}

@[refl] theorem refl (u : Word α) : SyntacticEq L u u := by
  intro x y
  rfl

@[symm] theorem symm (h : SyntacticEq L u v) : SyntacticEq L v u := by
  intro x y
  exact (h x y).symm

@[trans] theorem trans (h₁ : SyntacticEq L u v) (h₂ : SyntacticEq L v w) :
    SyntacticEq L u w := by
  intro x y
  exact (h₁ x y).trans (h₂ x y)

/-- Compatibility with appending the same prefix. -/
theorem append_left (p : Word α) (h : SyntacticEq L u v) :
    SyntacticEq L (p ++ u) (p ++ v) := by
  intro x y
  simpa [List.append_assoc] using h (x ++ p) y

/-- Compatibility with appending the same suffix. -/
theorem append_right (q : Word α) (h : SyntacticEq L u v) :
    SyntacticEq L (u ++ q) (v ++ q) := by
  intro x y
  simpa [List.append_assoc] using h x (q ++ y)

/-- Two-sided compatibility for word multiplication. -/
theorem append_congr {u' v' : Word α}
    (hu : SyntacticEq L u u') (hv : SyntacticEq L v v') :
    SyntacticEq L (u ++ v) (u' ++ v') := by
  exact (append_right v hu).trans (append_left u' hv)

end SyntacticEq

/-- Syntactic equivalence packaged as a multiplicative congruence on the free
monoid of words. -/
def syntacticCon {α : Type u} (L : Language α) : Con (FreeMonoid α) where
  r u v := SyntacticEq L (FreeMonoid.toList u) (FreeMonoid.toList v)
  iseqv := ⟨SyntacticEq.refl, SyntacticEq.symm, SyntacticEq.trans⟩
  mul' := by
    intro w x y z hw hy
    simpa only [FreeMonoid.toList_mul] using
      SyntacticEq.append_congr hw hy

/-- The setoid underlying the syntactic quotient. -/
def syntacticSetoid {α : Type u} (L : Language α) : Setoid (FreeMonoid α) :=
  (syntacticCon L).toSetoid

/-- The syntactic quotient monoid.  Its multiplication is induced by word
concatenation through the proved two-sided congruence `syntacticCon L`. -/
abbrev SyntacticQuotient {α : Type u} (L : Language α) :=
  (syntacticCon L).Quotient

/-- The canonical surjective monoid morphism from words to their syntactic
congruence classes. -/
def syntacticMorphism {α : Type u} (L : Language α) :
    FreeMonoid α →* SyntacticQuotient L :=
  Con.mk' (syntacticCon L)

/-- Every syntactic congruence class has a representative word. -/
theorem syntacticMorphism_surjective {α : Type u} (L : Language α) :
    Function.Surjective (syntacticMorphism L) :=
  Con.mk'_surjective

/-- The kernel equality of the syntactic morphism is exactly contextual
syntactic equivalence. -/
theorem syntacticMorphism_eq_iff {α : Type u} (L : Language α) (u v : Word α) :
    syntacticMorphism L (FreeMonoid.ofList u) =
        syntacticMorphism L (FreeMonoid.ofList v) ↔
      SyntacticEq L u v := by
  change (syntacticCon L).mk' u = (syntacticCon L).mk' v ↔ SyntacticEq L u v
  rw [← Con.ker_apply, Con.mk'_ker]
  rfl

/-! ### 4.  Aperiodicity

`IsAperiodicMonoid` is used to state Schützenberger's theorem.  The statement
itself (obligation `L-SF-001`) is **not** present as a Lean declaration:
although the syntactic quotient monoid is now available, an unproved
Schützenberger `theorem` would not be a formalization.  It returns only with
a proof or an explicitly cited trusted boundary. -/

/-- A monoid is aperiodic when every element has an eventually idempotent power. -/
def IsAperiodicMonoid (M : Type v) [Monoid M] : Prop :=
  ∀ x : M, ∃ n : Nat, x ^ (n + 1) = x ^ n

/-! ### 5.  Height-one statements for recognizing monoids and groups -/

/-- Every language recognized by `M` has a height-one certificate. -/
def HeightOneForMonoid (M : Type v) [Monoid M] : Prop :=
  ∀ (α : Type u) [Fintype α] [DecidableEq α],
    ∀ R : Recognition α M, HasHeightAtMost R.language 1

/-- Group-specialized name for the same recognition property. -/
-- API repair 2026-07-22: the alphabet universe `u` quantified inside
-- `HeightOneForMonoid` must be bound explicitly here, otherwise it is left as
-- a universe metavariable.
def HeightOneForGroup (G : Type v) [Group G] : Prop :=
  HeightOneForMonoid.{u, v} G

end GSH
