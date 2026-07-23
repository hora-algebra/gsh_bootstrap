import GSH.Challenges.GeneralizedStarHeight
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Recognition: automata, monoids, syntactic congruence, aperiodicity

This file collects the recognition-theoretic interface layer in one place
(consolidated 2026-07-23 from `GSH/Automata/DFA.lean`,
`GSH/Monoid/Recognition.lean`, `GSH/Monoid/Syntactic.lean`,
`GSH/StarFree/Aperiodic.lean`, and `GSH/GroupLanguages/Basic.lean`,
definitions unchanged):

1. deterministic finite automata and their languages;
2. recognition of a language by a monoid morphism with an accepting set;
3. the syntactic congruence and the syntactic monoid
   (quotient-monoid instance: registered `sorry`, obligation L-SYN-002);
4. aperiodicity and the Schützenberger interface
   (registered `sorry`, obligation L-SF-001);
5. the height-one recognition properties `HeightOneForMonoid` /
   `HeightOneForGroup` used by the finite-group ladder.

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

The quotient-monoid instance is deliberately isolated: the contextual
relation must first be proved to be a two-sided congruence. -/

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

/-- The setoid underlying the syntactic quotient. -/
def syntacticSetoid {α : Type u} (L : Language α) : Setoid (Word α) where
  r := SyntacticEq L
  iseqv := ⟨SyntacticEq.refl, SyntacticEq.symm, SyntacticEq.trans⟩

/-- The carrier of the syntactic monoid. -/
abbrev SyntacticMonoid {α : Type u} (L : Language α) :=
  Quotient (syntacticSetoid L)

-- BLUEPRINT: L-SYN-002
/-- The quotient monoid structure induced by two-sided congruence. -/
instance syntacticMonoidInst {α : Type u} (L : Language α) :
    Monoid (SyntacticMonoid L) := by
  sorry

/-! ### 4.  Aperiodicity and the Schützenberger interface

The final equivalence is a blueprint declaration, not yet a formalization of
Schützenberger's theorem. -/

/-- A monoid is aperiodic when every element has an eventually idempotent power. -/
def IsAperiodicMonoid (M : Type v) [Monoid M] : Prop :=
  ∀ x : M, ∃ n : Nat, x ^ (n + 1) = x ^ n

/-- A syntactic-monoid formulation for one language. -/
def HasAperiodicSyntacticMonoid {α : Type u} (L : Language α) : Prop :=
  IsAperiodicMonoid (SyntacticMonoid L)

-- BLUEPRINT: L-SF-001
/-- Schützenberger's theorem, retained as an explicit formalization target. -/
theorem schutzenberger_interface {α : Type u} (L : Language α) (hreg : IsRegular L) :
    IsStarFree L ↔ HasAperiodicSyntacticMonoid L := by
  sorry

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
