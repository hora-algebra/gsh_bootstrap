import GSH.Regex.Derivative
import GSH.Regex.CountHeight

/-!
# Derivative certificates: proving `denote r = L` against an automaton

Writing an explicit star-free expression for a language and then proving
`denote r = L` by hand is the dominant cost in this repository (see
`GSH/Results/A4CutFeature.lean`).  This file removes most of that cost.

The observation is that `GRegex` has a *proved* Brzozowski derivative theory
(`GSH/Regex/Derivative.lean`): `denote (deriv a r) = {w | a :: w ∈ denote r}`.
So if a finite family of expressions `E : σ → GRegex α` is closed under
derivatives along a transition function `step : σ → α → σ`, and nullability of
`E s` matches an acceptance predicate `acc s`, then `E s` denotes exactly the
language accepted from state `s` (`denote_of_derivFamily`).

This turns

  "give an expression and prove a language equality by hand"

into

  "give one expression per automaton state and discharge finitely many
   *derivative identities*",

each of which is a small local computation.  The `denote`-level normalisation
lemmas in §3 are the simp set that discharges them; `deriv_inter`,
`deriv_univ` and `deriv_compl` hold *syntactically* (`rfl`), so only
`atomsOf` and `concat` need real work.

The certificate says nothing about star height: the height of the exhibited
expression is read off separately with `starHeight`.  Both together give
`HasHeightAtMost L n`.

This file contains no `sorry` and no `axiom`.
-/

set_option autoImplicit false

namespace GSH

universe u v

variable {α : Type u}

/-! ## 1.  Running a transition function -/

/-- Run a transition function along a word, leftmost letter first. -/
def runFrom {σ : Type v} (step : σ → α → σ) : σ → Word α → σ
  | s, [] => s
  | s, a :: w => runFrom step (step s a) w

@[simp] theorem runFrom_nil {σ : Type v} (step : σ → α → σ) (s : σ) :
    runFrom step s [] = s := rfl

@[simp] theorem runFrom_cons {σ : Type v} (step : σ → α → σ) (s : σ) (a : α)
    (w : Word α) : runFrom step s (a :: w) = runFrom step (step s a) w := rfl

theorem runFrom_append {σ : Type v} (step : σ → α → σ) :
    ∀ (s : σ) (u v : Word α),
      runFrom step s (u ++ v) = runFrom step (runFrom step s u) v
  | _, [], _ => rfl
  | s, a :: u, v => by
    simp only [List.cons_append, runFrom_cons]
    exact runFrom_append step (step s a) u v

namespace GRegex

/-! ## 2.  The certificate -/

/--
**Derivative certificate.**  A family of expressions closed under Brzozowski
derivatives along `step`, whose nullability matches `acc`, denotes the
language accepted by the automaton `(step, acc)`.
-/
theorem mem_denote_of_derivFamily [DecidableEq α] {σ : Type v}
    (E : σ → GRegex α) (step : σ → α → σ) (acc : σ → Prop)
    (hstep : ∀ (s : σ) (a : α), denote (deriv a (E s)) = denote (E (step s a)))
    (hnull : ∀ s : σ, ([] ∈ denote (E s)) ↔ acc s) :
    ∀ (w : Word α) (s : σ), w ∈ denote (E s) ↔ acc (runFrom step s w)
  | [], s => by simpa using hnull s
  | a :: w, s => by
    have h1 : (a :: w ∈ denote (E s)) ↔ w ∈ denote (deriv a (E s)) := by
      rw [denote_deriv]; exact Iff.rfl
    rw [h1, hstep s a, runFrom_cons]
    exact mem_denote_of_derivFamily E step acc hstep hnull w (step s a)

/-- Language form of `mem_denote_of_derivFamily`. -/
theorem denote_of_derivFamily [DecidableEq α] {σ : Type v}
    (E : σ → GRegex α) (step : σ → α → σ) (acc : σ → Prop)
    (hstep : ∀ (s : σ) (a : α), denote (deriv a (E s)) = denote (E (step s a)))
    (hnull : ∀ s : σ, ([] ∈ denote (E s)) ↔ acc s) (s : σ) :
    denote (E s) = {w : Word α | acc (runFrom step s w)} := by
  ext w
  exact mem_denote_of_derivFamily E step acc hstep hnull w s

/--
Packaged form: an expression of star height ≤ `n` whose derivative family
certifies an automaton gives `HasHeightAtMost` for the accepted language.
-/
theorem hasHeightAtMost_of_derivFamily [DecidableEq α] {σ : Type v} {n : Nat}
    (E : σ → GRegex α) (step : σ → α → σ) (acc : σ → Prop)
    (hstep : ∀ (s : σ) (a : α), denote (deriv a (E s)) = denote (E (step s a)))
    (hnull : ∀ s : σ, ([] ∈ denote (E s)) ↔ acc s) (s : σ)
    (hh : starHeight (E s) ≤ n) :
    HasHeightAtMost {w : Word α | acc (runFrom step s w)} n :=
  ⟨E s, denote_of_derivFamily E step acc hstep hnull s, hh⟩

/-! ## 3.  Normalisation lemmas for the derivative identities

`deriv` commutes syntactically with `compl`, `union`, `inter` and fixes
`univ`, so the identities `denote (deriv a (E s)) = denote (E (step s a))`
reduce to the `atomsOf` and `concat` cases. -/

@[simp] theorem deriv_univ [DecidableEq α] (a : α) :
    deriv a (univ : GRegex α) = univ := rfl

@[simp] theorem deriv_compl [DecidableEq α] (a : α) (r : GRegex α) :
    deriv a (compl r) = compl (deriv a r) := rfl

@[simp] theorem deriv_union [DecidableEq α] (a : α) (r s : GRegex α) :
    deriv a (union r s) = union (deriv a r) (deriv a s) := rfl

@[simp] theorem deriv_inter [DecidableEq α] (a : α) (r s : GRegex α) :
    deriv a (inter r s) = inter (deriv a r) (deriv a s) := rfl

@[simp] theorem nullable_univ : nullable (univ : GRegex α) = true := rfl

@[simp] theorem nullable_inter (r s : GRegex α) :
    nullable (inter r s) = (nullable r && nullable s) := by
  simp only [inter, nullable]
  cases nullable r <;> cases nullable s <;> rfl

/-! ### `denote`-level normalisation -/

@[simp] theorem denote_zero_eq : denote (zero : GRegex α) = ∅ := rfl

@[simp] theorem denote_epsilon_eq :
    denote (epsilon : GRegex α) = ({[]} : Language α) := rfl

@[simp] theorem denote_atom_eq (a : α) : denote (atom a) = ({[a]} : Language α) := rfl

@[simp] theorem denote_union_eq (r s : GRegex α) :
    denote (union r s) = denote r ∪ denote s := rfl

@[simp] theorem denote_concat_eq (r s : GRegex α) :
    denote (concat r s) = Language.concat (denote r) (denote s) := rfl

@[simp] theorem denote_compl_eq (r : GRegex α) :
    denote (compl r) = (denote r)ᶜ := rfl

@[simp] theorem denote_inter_eq (r s : GRegex α) :
    denote (inter r s) = denote r ∩ denote s := denote_inter r s

end GRegex

/-! ### Language-level normalisation used by the same simp set -/

@[simp] theorem concat_empty_left (L : Language α) :
    Language.concat (∅ : Language α) L = ∅ := by
  ext w; simp [Language.concat]

@[simp] theorem concat_empty_right (L : Language α) :
    Language.concat L (∅ : Language α) = ∅ := by
  ext w; simp [Language.concat]

@[simp] theorem concat_singleton_nil_left (L : Language α) :
    Language.concat ({[]} : Language α) L = L := by
  have : ({[]} : Language α) = Language.epsilon := rfl
  rw [this, epsilon_concat]

@[simp] theorem concat_singleton_nil_right (L : Language α) :
    Language.concat L ({[]} : Language α) = L := by
  have : ({[]} : Language α) = Language.epsilon := rfl
  rw [this, concat_epsilon]

namespace GRegex

/-- Derivative of an `atomsOf` alternation, denotationally. -/
theorem denote_deriv_atomsOf [DecidableEq α] (a : α) :
    ∀ S : List α,
      denote (deriv a (CountHeight.atomsOf S))
        = if a ∈ S then ({[]} : Language α) else ∅
  | [] => by simp [CountHeight.atomsOf, deriv]
  | b :: S => by
    have ih := denote_deriv_atomsOf a S
    by_cases hb : a = b
    · subst hb
      by_cases hS : a ∈ S <;> simp [CountHeight.atomsOf, deriv, ih, hS]
    · by_cases hS : a ∈ S <;>
        simp [CountHeight.atomsOf, deriv, hb, ih, hS, List.mem_cons]

/-- Derivative of `avoidSet`, denotationally: reading a forbidden letter kills
the language, any other letter leaves it unchanged. -/
theorem denote_deriv_avoidSet [DecidableEq α] (a : α) (S : List α) :
    denote (deriv a (CountHeight.avoidSet S))
      = if a ∈ S then ∅ else denote (CountHeight.avoidSet S) := by
  ext w
  rw [denote_deriv]
  by_cases h : a ∈ S
  · simp only [h, if_pos, Set.mem_setOf_eq]
    rw [CountHeight.denote_avoidSet]
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hc
    exact hc a h (by simp)
  · simp only [h, if_neg, not_false_iff, Set.mem_setOf_eq, CountHeight.denote_avoidSet]
    constructor
    · intro hc b hb hbw
      exact hc b hb (by simp [hbw])
    · intro hc b hb hbw
      simp only [List.mem_cons] at hbw
      rcases hbw with rfl | hbw
      · exact h hb
      · exact hc b hb hbw

/-! ## 4.  Worked example / regression test

`avoidSet S` is re-derived through the certificate: two states (alive, dead),
one derivative identity per state.  This is the shape every application
takes — one expression per automaton state, then `hstep` and `hnull`. -/

section Example

variable [DecidableEq α]

private def avoidState (S : List α) : Bool → GRegex α
  | true => CountHeight.avoidSet S
  | false => zero

private def avoidStep (S : List α) (b : Bool) (a : α) : Bool :=
  b && !decide (a ∈ S)

theorem denote_avoidSet_via_certificate (S : List α) :
    denote (CountHeight.avoidSet S)
      = {w : Word α | runFrom (avoidStep S) true w = true} := by
  have hstep : ∀ (b : Bool) (a : α),
      denote (deriv a (avoidState S b)) = denote (avoidState S (avoidStep S b a)) := by
    intro b a
    cases b with
    | false => simp [avoidState, avoidStep, deriv]
    | true =>
      by_cases h : a ∈ S <;>
        simp [avoidState, avoidStep, h, denote_deriv_avoidSet]
  have hnull : ∀ b : Bool, ([] ∈ denote (avoidState S b)) ↔ (b = true) := by
    intro b
    cases b with
    | false => simp [avoidState]
    | true =>
      simp only [avoidState, CountHeight.denote_avoidSet, Set.mem_setOf_eq,
        List.not_mem_nil, not_false_iff, implies_true, iff_true]
  exact denote_of_derivFamily (avoidState S) (avoidStep S) (fun b => b = true)
    hstep hnull true

end Example

end GRegex
end GSH
