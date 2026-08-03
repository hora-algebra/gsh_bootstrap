import GSH.StarFree.Schutzenberger
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finite.Prod

/-!
# Transition monoids, and Schützenberger's theorem in automaton form

`GSH/StarFree/Schutzenberger.lean` proves the hard direction of
Schützenberger's theorem in *monoid* form: a language recognized by a finite
aperiodic monoid is star-free.  Concrete languages are almost always given by
an automaton instead, so this file packages the theorem in the form actually
used downstream:

    if the deterministic automaton `(Q, δ)` is **counter-free** — every word
    satisfies `run q wⁿ⁺¹ = run q wⁿ` for one uniform `n` — then every
    language `{w | run q₀ w ∈ F}` accepted by it is star-free.

The bridge is the *transition monoid*

    TM δ = { t : Q → Q | ∃ w, t = fun q => run δ q w },

which is a finite monoid under `t₁ * t₂ = t₂ ∘ t₁` (words compose left to
right).  The counter-freeness hypothesis is literally aperiodicity of `TM δ`,
and `{w | run δ q₀ w ∈ F}` is the language recognized by the subset
`{t | t q₀ ∈ F}`.

## Design notes

* `TM δ` is a subtype of `Q → Q` cut out by an existential over words, which
  is not a decidable predicate.  `Fintype (TM δ)` is therefore obtained from
  `Finite` by `Fintype.ofFinite` and `DecidableEq` classically, inside the
  proof.  Both are only *instance arguments* of `recognized_isStarFree`; the
  statement of `hasHeightAtMost_of_run` mentions neither, so nothing
  computable is lost.
* Counter-freeness is stated with an explicit bound `n` rather than
  `∀ w, ∃ n`, because that is the form a concrete automaton proof produces
  and it avoids a choice step.

This file contains no `sorry` and no `axiom`.
-/

set_option autoImplicit false

namespace GSH
namespace TransitionMonoid

universe u

variable {A Q : Type u}

/-! ## 1.  Runs -/

/-- Run the transition function `δ` from state `q` along a word. -/
def run (δ : Q → A → Q) : Q → Word A → Q
  | q, [] => q
  | q, x :: w => run δ (δ q x) w

@[simp] theorem run_nil (δ : Q → A → Q) (q : Q) : run δ q [] = q := rfl

@[simp] theorem run_cons (δ : Q → A → Q) (q : Q) (x : A) (w : Word A) :
    run δ q (x :: w) = run δ (δ q x) w := rfl

theorem run_append (δ : Q → A → Q) : ∀ (q : Q) (u v : Word A),
    run δ q (u ++ v) = run δ (run δ q u) v
  | _, [], _ => rfl
  | q, x :: u, v => by
    simp only [List.cons_append, run_cons]
    exact run_append δ (δ q x) u v

/-- Concatenation power of a word. -/
def wpow (w : Word A) : Nat → Word A
  | 0 => []
  | k + 1 => wpow w k ++ w

@[simp] theorem wpow_zero (w : Word A) : wpow w 0 = [] := rfl

@[simp] theorem wpow_succ (w : Word A) (k : Nat) :
    wpow w (k + 1) = wpow w k ++ w := rfl

theorem wpow_nil : ∀ k : Nat, wpow ([] : Word A) k = []
  | 0 => rfl
  | k + 1 => by simp [wpow_nil k]

/-- Once one power of `w` acts like the next, all larger powers agree with it. -/
theorem run_wpow_stab (δ : Q → A → Q) (w : Word A) (n : Nat)
    (h : ∀ q : Q, run δ q (wpow w (n + 1)) = run δ q (wpow w n)) :
    ∀ (m : Nat) (q : Q), run δ q (wpow w (n + m)) = run δ q (wpow w n)
  | 0, q => rfl
  | m + 1, q => by
    have hstep : run δ q (wpow w (n + m + 1)) = run δ (run δ q (wpow w (n + m))) w := by
      rw [wpow_succ, run_append]
    rw [show n + (m + 1) = n + m + 1 from rfl, hstep, run_wpow_stab δ w n h m q,
      ← run_append, ← wpow_succ, h q]

/-! ## 2.  The transition monoid -/

/-- The transformation of the state space induced by a word. -/
def transOf (δ : Q → A → Q) (w : Word A) : Q → Q := fun q => run δ q w

theorem transOf_append (δ : Q → A → Q) (u v : Word A) :
    transOf δ (u ++ v) = fun q => transOf δ v (transOf δ u q) := by
  funext q; exact run_append δ q u v

/-- The transition monoid of `δ`: the transformations realized by words. -/
def TM (δ : Q → A → Q) : Type u := {t : Q → Q // ∃ w : Word A, t = transOf δ w}

namespace TM

variable {δ : Q → A → Q}

instance : One (TM δ) := ⟨⟨transOf δ [], ⟨[], rfl⟩⟩⟩

instance : Mul (TM δ) :=
  ⟨fun t₁ t₂ => ⟨fun q => t₂.val (t₁.val q), by
    obtain ⟨u, hu⟩ := t₁.2
    obtain ⟨v, hv⟩ := t₂.2
    exact ⟨u ++ v, by rw [transOf_append, hu, hv]⟩⟩⟩

@[simp] theorem mul_val (t₁ t₂ : TM δ) :
    (t₁ * t₂).val = fun q => t₂.val (t₁.val q) := rfl

@[simp] theorem one_val : (1 : TM δ).val = transOf δ [] := rfl

instance : Monoid (TM δ) where
  mul_assoc _ _ _ := Subtype.ext rfl
  one_mul t := Subtype.ext (by funext q; rfl)
  mul_one t := Subtype.ext (by funext q; rfl)

/-- The element of the transition monoid realized by a word. -/
def mk (δ : Q → A → Q) (w : Word A) : TM δ := ⟨transOf δ w, ⟨w, rfl⟩⟩

theorem mk_append (δ : Q → A → Q) (u v : Word A) :
    mk δ (u ++ v) = mk δ u * mk δ v :=
  Subtype.ext (transOf_append δ u v)

theorem mk_pow (δ : Q → A → Q) (w : Word A) :
    ∀ k : Nat, mk δ w ^ k = mk δ (wpow w k)
  | 0 => by rw [pow_zero]; rfl
  | k + 1 => by rw [pow_succ, mk_pow δ w k, wpow_succ, mk_append]

/-- The letter map into the transition monoid. -/
def letterTr (δ : Q → A → Q) (a : A) : TM δ := mk δ [a]

theorem eval_letterTr (δ : Q → A → Q) :
    ∀ w : Word A, Schutzenberger.eval (letterTr δ) w = mk δ w
  | [] => rfl
  | a :: w => by
    rw [Schutzenberger.eval_cons, eval_letterTr δ w, letterTr, ← mk_append]
    rfl

end TM

/-! ## 3.  Counter-free automata accept star-free languages -/

/--
**Schützenberger's theorem, automaton form.**  If every word acts on the state
space with `run q wⁿ⁺¹ = run q wⁿ` (counter-freeness with the uniform bound
`n`), then every language accepted by the automaton is star-free.
-/
theorem hasHeightAtMost_of_run [Fintype A] [DecidableEq A] [Fintype Q] [DecidableEq Q]
    (δ : Q → A → Q) (q₀ : Q) (F : Set Q) (n : Nat)
    (hap : ∀ (q : Q) (w : Word A), run δ q (wpow w (n + 1)) = run δ q (wpow w n)) :
    HasHeightAtMost {w : Word A | run δ q₀ w ∈ F} 0 := by
  classical
  haveI : Finite (Q → Q) := inferInstance
  haveI : Finite (TM δ) :=
    inferInstanceAs (Finite {t : Q → Q // ∃ w : Word A, t = transOf δ w})
  letI : Fintype (TM δ) := Fintype.ofFinite _
  have hM : IsAperiodicMonoid (TM δ) := by
    intro x
    obtain ⟨w, hw⟩ := x.2
    refine ⟨n, ?_⟩
    have hx : x = TM.mk δ w := Subtype.ext hw
    rw [hx, TM.mk_pow, TM.mk_pow]
    exact Subtype.ext (funext fun q => hap q w)
  have hset : {w : Word A | run δ q₀ w ∈ F}
      = {w : Word A | Schutzenberger.eval (TM.letterTr δ) w
            ∈ ({t : TM δ | t.val q₀ ∈ F} : Set (TM δ))} := by
    ext w
    simp only [Set.mem_setOf_eq, TM.eval_letterTr]
    rfl
  rw [hset]
  exact Schutzenberger.recognized_isStarFree hM _ _

end TransitionMonoid
end GSH
