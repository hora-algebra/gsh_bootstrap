import GSH.Results.A4LetterCut
import GSH.StarFree.TransitionMonoid

/-!
# Mover-marked cuts: the reduction of `N-A4-FULL-033b`

`GSH/Results/A4LetterCut.lean` closes the *filler* case of `N-A4-FULL-033`
because for a filler `h` the cut core is `{h}*`.  For a **mover** `g` the cut
core is the aperiodic language

    cutCore g = { w | phaseSum w ≡ 0 ∧ every landing is a `g` whose
                      predecessor is not `g` }

for which no explicit star-free expression was ever found by search
(`scripts/a4_aggregate_cstar.py`, `scripts/a4_cstar_block_code.py`).  It is
handled here (§3a, `N-A4-FULL-033c`) by exhibiting its accepting automaton,
proving that automaton **counter-free**, and invoking Schutzenberger's theorem
in automaton form (`GSH/StarFree/TransitionMonoid.lean`).

## Contents

1. `landingMarkCount`: landings carrying a mark that may look at the previous
   letter.  Basic algebra (append, mod-3 congruence, phase shift, splitting a
   landing count into marked and unmarked parts).
2. The mover marking `moverMark g prev x := (x = g ∧ prev ≠ some g)` and the
   two features `mch` (matched) and `unm` (unmatched).
3. The cut core, the token, the opener, and the `CutSystem`
   (`GSH/Regex/CutParity.lean`).
3a. The cut-core automaton and its counter-freeness (`N-A4-FULL-033c`).
4. The GF(2) recovery.  Writing `x p = N[g,p]`, `Lft p` for the occurrences of
   `g` at entry phase `p` not preceded by `g` and `Rgt p` for those not
   followed by `g`, the digram identity `nL (p+ε) = nR p` (count the `gg`
   digrams by their second resp. first letter) gives

        x p + x (p-ε) = Lft p + Rgt (p-ε)

   which is *independent of the total phase* `P`, and together with
   `∑ x p = |w|_g` determines every `x p` over `GF(2)`.

This file contains no `sorry` and no `axiom`.
-/

set_option autoImplicit false

namespace GSH
namespace A4MoverCut

open GRegex Language A4Structure A4CutFeature A4LetterCut CountHeight List

/-! ## 1.  Landings with a mark depending on the previous letter -/

/-- The letter preceding the continuation of `u`, given what preceded `u`. -/
def lastPrev : Word A4 → Option A4 → Option A4
  | [], prev => prev
  | x :: w, _ => lastPrev w (some x)

@[simp] theorem lastPrev_nil (prev : Option A4) : lastPrev [] prev = prev := rfl

@[simp] theorem lastPrev_cons (x : A4) (w : Word A4) (prev : Option A4) :
    lastPrev (x :: w) prev = lastPrev w (some x) := rfl

theorem lastPrev_append : ∀ (u v : Word A4) (prev : Option A4),
    lastPrev (u ++ v) prev = lastPrev v (lastPrev u prev)
  | [], _, _ => rfl
  | x :: u, v, prev => by
    simp only [List.cons_append, lastPrev_cons]
    exact lastPrev_append u v (some x)

/-- Number of landings on `q` (scanning from start phase `p` with `prev` the
letter just before the word) whose mark `mk` fires. -/
def landingMarkCount (mk : Option A4 → A4 → Bool) (q : Fin 3) :
    Word A4 → Nat → Option A4 → Nat
  | [], _, _ => 0
  | x :: w, p, prev =>
      (if (p + (phase x).val) % 3 = q.val ∧ mk prev x = true then 1 else 0)
        + landingMarkCount mk q w (p + (phase x).val) (some x)

theorem landingMarkCount_nil (mk : Option A4 → A4 → Bool) (q : Fin 3) (p : Nat)
    (prev : Option A4) : landingMarkCount mk q [] p prev = 0 := rfl

theorem landingMarkCount_cons (mk : Option A4 → A4 → Bool) (q : Fin 3) (x : A4)
    (w : Word A4) (p : Nat) (prev : Option A4) :
    landingMarkCount mk q (x :: w) p prev =
      (if (p + (phase x).val) % 3 = q.val ∧ mk prev x = true then 1 else 0)
        + landingMarkCount mk q w (p + (phase x).val) (some x) := rfl

theorem landingMarkCount_append (mk : Option A4 → A4 → Bool) (q : Fin 3) :
    ∀ (u v : Word A4) (p : Nat) (prev : Option A4),
      landingMarkCount mk q (u ++ v) p prev
        = landingMarkCount mk q u p prev
          + landingMarkCount mk q v (p + phaseSum u) (lastPrev u prev)
  | [], v, p, prev => by simp [landingMarkCount_nil, phaseSum]
  | x :: u, v, p, prev => by
    simp only [List.cons_append, landingMarkCount_cons, phaseSum_cons,
      lastPrev_cons]
    rw [landingMarkCount_append mk q u v (p + (phase x).val) (some x)]
    simp [Nat.add_assoc]

theorem landingMarkCount_congr (mk : Option A4 → A4 → Bool) (q : Fin 3) :
    ∀ (w : Word A4) (p p' : Nat) (prev : Option A4), p % 3 = p' % 3 →
      landingMarkCount mk q w p prev = landingMarkCount mk q w p' prev
  | [], _, _, _, _ => rfl
  | x :: w, p, p', prev, h => by
    have hstep : (p + (phase x).val) % 3 = (p' + (phase x).val) % 3 := by omega
    rw [landingMarkCount_cons, landingMarkCount_cons,
      landingMarkCount_congr mk q w (p + (phase x).val) (p' + (phase x).val)
        (some x) hstep, hstep]

theorem landingMarkCount_shift (mk : Option A4 → A4 → Bool) (q : Fin 3) :
    ∀ (w : Word A4) (p : Nat) (prev : Option A4),
      landingMarkCount mk q w (q.val + p) prev = landingMarkCount mk 0 w p prev
  | [], _, _ => rfl
  | x :: w, p, prev => by
    rw [landingMarkCount_cons, landingMarkCount_cons]
    have harg : q.val + p + (phase x).val = q.val + (p + (phase x).val) := by omega
    rw [harg, landingMarkCount_shift mk q w (p + (phase x).val) (some x)]
    congr 1
    have hqlt := q.isLt
    have hiff : ((q.val + (p + (phase x).val)) % 3 = q.val)
        ↔ ((p + (phase x).val) % 3 = (0 : Fin 3).val) := by
      simp only [Fin.val_zero]; omega
    exact if_congr (and_congr_left fun _ => hiff) rfl rfl

/-- Splitting a landing count into the marked and the unmarked part. -/
theorem landingMarkCount_add_not (mk : Option A4 → A4 → Bool) (q : Fin 3) :
    ∀ (w : Word A4) (p : Nat) (prev : Option A4),
      landingMarkCount mk q w p prev
          + landingMarkCount (fun pv y => !mk pv y) q w p prev
        = landingCount q w p
  | [], _, _ => rfl
  | x :: w, p, prev => by
    rw [landingMarkCount_cons, landingMarkCount_cons, landingCount_cons,
      ← landingMarkCount_add_not mk q w (p + (phase x).val) (some x)]
    by_cases hc : (p + (phase x).val) % 3 = q.val
    · by_cases hm : mk prev x = true <;> simp [hc, hm] <;> omega
    · simp [hc]

theorem landingMarkCount_le (mk : Option A4 → A4 → Bool) (q : Fin 3)
    (w : Word A4) (p : Nat) (prev : Option A4) :
    landingMarkCount mk q w p prev ≤ landingCount q w p := by
  have := landingMarkCount_add_not mk q w p prev
  omega

/-! ## 2.  The mover marking -/

/-- A landing is *matched* when its letter is the mover `g` and the letter
before it is not `g` (the start of the word counts as "not `g`"). -/
def moverMark (g : A4) : Option A4 → A4 → Bool :=
  fun prev x => decide (x = g ∧ prev ≠ some g)

/-- Matched landings on `q`. -/
def mch (g : A4) (q : Fin 3) (w : Word A4) (p : Nat) (prev : Option A4) : Nat :=
  landingMarkCount (moverMark g) q w p prev

/-- Unmatched landings on `q` (the cut events). -/
def unm (g : A4) (q : Fin 3) (w : Word A4) (p : Nat) (prev : Option A4) : Nat :=
  landingMarkCount (fun pv y => !moverMark g pv y) q w p prev

theorem mch_add_unm (g : A4) (q : Fin 3) (w : Word A4) (p : Nat)
    (prev : Option A4) : mch g q w p prev + unm g q w p prev = landingCount q w p :=
  landingMarkCount_add_not _ q w p prev

theorem unm_le (g : A4) (q : Fin 3) (w : Word A4) (p : Nat) (prev : Option A4) :
    unm g q w p prev ≤ landingCount q w p := landingMarkCount_le _ q w p prev

theorem unm_append (g : A4) (q : Fin 3) (u v : Word A4) (p : Nat)
    (prev : Option A4) :
    unm g q (u ++ v) p prev
      = unm g q u p prev + unm g q v (p + phaseSum u) (lastPrev u prev) :=
  landingMarkCount_append _ q u v p prev

theorem unm_congr (g : A4) (q : Fin 3) (w : Word A4) {p p' : Nat}
    (prev : Option A4) (h : p % 3 = p' % 3) :
    unm g q w p prev = unm g q w p' prev :=
  landingMarkCount_congr _ q w p p' prev h

theorem unm_shift (g : A4) (q : Fin 3) (w : Word A4) (p : Nat)
    (prev : Option A4) :
    unm g q w (q.val + p) prev = unm g 0 w p prev :=
  landingMarkCount_shift _ q w p prev

/-- At a reset boundary the running phase equals the cut phase, so the first
letter can only land if it is a filler — and a filler is never matched.  Hence
the count no longer depends on the preceding letter. -/
theorem landingMarkCount_reset_indep (g : A4) (hg : phase g ≠ 0) :
    ∀ (w : Word A4) (prev prev' : Option A4),
      unm g 0 w 0 prev = unm g 0 w 0 prev'
  | [], _, _ => rfl
  | x :: w, prev, prev' => by
    show landingMarkCount _ 0 (x :: w) 0 prev = landingMarkCount _ 0 (x :: w) 0 prev'
    rw [landingMarkCount_cons, landingMarkCount_cons]
    congr 1
    by_cases hc : (phase x).val % 3 = 0
    · -- the landing letter is a filler, hence not `g`, hence unmatched
      have hlt := (phase x).isLt
      have hx0 : phase x = 0 := Fin.ext (by omega)
      have hxg : x ≠ g := by
        intro hxe; rw [← hxe] at hg; exact hg hx0
      simp [moverMark, hxg, hx0]
    · simp [hc]

theorem landingMarkCount_of_landingCount_zero (mk : Option A4 → A4 → Bool) (q : Fin 3)
    {w : Word A4} {p : Nat} (prev : Option A4) (h : landingCount q w p = 0) :
    landingMarkCount mk q w p prev = 0 := by
  have := landingMarkCount_le mk q w p prev
  omega

/-- A word with a single landing, at its last letter, contributes to a marked
count exactly according to the mark of that letter. -/
theorem landingMarkCount_of_single_landing (mk : Option A4 → A4 → Bool) (q : Fin 3)
    {init : Word A4} {x : A4} (prev : Option A4)
    (hinit : landingCount q init 0 = 0)
    (hsum : (phaseSum init + (phase x).val) % 3 = q.val) :
    landingMarkCount mk q (init ++ [x]) 0 prev
      = if mk (lastPrev init prev) x = true then 1 else 0 := by
  rw [landingMarkCount_append,
    landingMarkCount_of_landingCount_zero mk q prev hinit, Nat.zero_add,
    landingMarkCount_cons, landingMarkCount_nil, Nat.add_zero]
  by_cases hm : mk (lastPrev init prev) x = true
  · simp [hm, hsum]
  · simp [hm]

/-! ## 3.  The cut core, the token, the opener and the cut system -/

/-- Semantic cut core: phase-neutral words all of whose landings are matched.
Well defined as a factor because the count does not depend on the letter
preceding a cut (`landingMarkCount_reset_indep`). -/
def cutCore (g : A4) : Language A4 :=
  {w | phaseSum w % 3 = 0 ∧ unm g 0 w 0 none = 0}

/-- Words ending in `y g` with `y ≠ g`. -/
def matchedSuffix (g : A4) : GRegex A4 :=
  concat univ
    (concat (atomsOf (allA4.filter (fun x => decide (x ≠ g)))) (atom g))

/-- Words whose final landing is matched, as seen from a cut (so the
one-letter word `g` counts). -/
def matchedEnd (g : A4) : GRegex A4 := union (atom g) (matchedSuffix g)

/-- First-return blocks whose final landing is **not** matched. -/
def unmBlock (g : A4) : GRegex A4 := inter frToken (compl (matchedEnd g))

theorem starHeight_matchedSuffix (g : A4) : starHeight (matchedSuffix g) = 0 := by
  change max (starHeight (univ : GRegex A4))
    (max (starHeight (atomsOf (allA4.filter (fun x => decide (x ≠ g)))))
      (starHeight (atom g))) = 0
  rw [starHeight_univ, starHeight_atomsOf, starHeight_atom]; rfl

theorem starHeight_matchedEnd (g : A4) : starHeight (matchedEnd g) = 0 := by
  change max (starHeight (atom g)) (starHeight (matchedSuffix g)) = 0
  rw [starHeight_atom, starHeight_matchedSuffix]; rfl

theorem starHeight_unmBlock (g : A4) : starHeight (unmBlock g) = 0 := by
  change max (starHeight frToken) (starHeight (matchedEnd g)) = 0
  rw [starHeight_frToken, starHeight_matchedEnd]; rfl

/-! ### 3a.  The cut core is star-free (`N-A4-FULL-033c`)

An explicit star-free expression for `cutCore g` was never found by search
(blind enumeration up to size 6, intersection of star-free supersets up to
size 4), and the block code `K` with `cutCore g = K*`
(`scripts/a4_cstar_block_code.py`) has *unbounded* synchronization delay, so
that decomposition does not produce one either.  The route taken here is
Schützenberger's theorem in automaton form
(`GSH/StarFree/TransitionMonoid.lean`, `hasHeightAtMost_of_run`): we exhibit
the accepting automaton and prove it **counter-free**.

The automaton scans the word keeping the running phase `p : Fin 3` and a bit
`b` recording whether the previous letter was `g`; it dies at a *landing*
(`p` returning to `0`) whose letter is not `g`, or whose letter is `g` but
whose predecessor is also `g`.  This is the five-state machine of
`scripts/a4_aggregate_cstar.py` before minimization.

Counter-freeness with the uniform bound `4` comes from three facts about the
transformation `t_w` induced by a nonempty word `w`, whose effect on a live
state `(p, b)` is either death or `(p + phF w, β)` with
`β = ` "the last letter of `w` is `g`" (`run_cstep_shape`):

* `run_cstep_head_none`: from the phase making the *first* letter a landing,
  a word dies when `b = true`;
* `run_cstep_last_none`: from the phase making the *last* letter a landing, a
  word whose last letter is not `g` dies;
* consequently, if `phF w ≠ 0`, then `t_w⁴` kills every state: surviving four
  passes would require surviving from `(q, β)` for **all three** phases `q`
  (because `phF w ≠ 0` generates `Fin 3`), which the two facts above forbid —
  the first if `β = true`, the second if `β = false`.

If instead `phF w = 0`, the live image `(p, β)` is a fixed point of `t_w`, so
`t_w² = t_w³` and a fortiori `t_w⁴ = t_w⁵`.
-/

section CutCoreDFA

open TransitionMonoid

/-- States of the cut-core automaton: `none` is the dead state, and
`some (p, b)` records the running phase `p` together with the bit `b` saying
whether the previous letter was the mover `g`. -/
abbrev CState := Option (Fin 3 × Bool)

/-- Transition function of the cut-core automaton. -/
def cstep (g : A4) : CState → A4 → CState
  | none, _ => none
  | some (p, b), x =>
      if p + phase x = 0 ∧ ¬ (x = g ∧ b = false) then none
      else some (p + phase x, decide (x = g))

@[simp] theorem cstep_none (g x : A4) : cstep g none x = none := rfl

theorem cstep_some (g : A4) (p : Fin 3) (b : Bool) (x : A4) :
    cstep g (some (p, b)) x =
      if p + phase x = 0 ∧ ¬ (x = g ∧ b = false) then none
      else some (p + phase x, decide (x = g)) := rfl

theorem run_cstep_none (g : A4) : ∀ w : Word A4, run (cstep g) none w = none
  | [] => rfl
  | x :: w => by rw [run_cons, cstep_none]; exact run_cstep_none g w

/-- The phase sum, as an element of `Fin 3`. -/
def phF : Word A4 → Fin 3
  | [] => 0
  | x :: w => phase x + phF w

@[simp] theorem phF_nil : phF [] = 0 := rfl

@[simp] theorem phF_cons (x : A4) (w : Word A4) : phF (x :: w) = phase x + phF w := rfl

theorem phF_append : ∀ u v : Word A4, phF (u ++ v) = phF u + phF v
  | [], v => by simp
  | x :: u, v => by
    rw [List.cons_append, phF_cons, phF_cons, phF_append u v, add_assoc]

theorem phF_val : ∀ w : Word A4, (phF w).val = phaseSum w % 3
  | [] => rfl
  | x :: w => by
    rw [phF_cons, Fin.val_add, phF_val w, phaseSum_cons]
    omega

/-- Whether the last letter of the word is `g`; the seed `b` for the empty
word.  For a nonempty word the seed is irrelevant. -/
def lastGb (g : A4) : Word A4 → Bool → Bool
  | [], b => b
  | x :: w, _ => lastGb g w (decide (x = g))

@[simp] theorem lastGb_nil (g : A4) (b : Bool) : lastGb g [] b = b := rfl

@[simp] theorem lastGb_cons (g x : A4) (w : Word A4) (b : Bool) :
    lastGb g (x :: w) b = lastGb g w (decide (x = g)) := rfl

theorem lastGb_concat (g y : A4) : ∀ (v : Word A4) (b : Bool),
    lastGb g (v ++ [y]) b = decide (y = g)
  | [], _ => rfl
  | x :: v, b => by rw [List.cons_append, lastGb_cons, lastGb_concat g y v]

/-- **Shape of a run.**  From a live state a word either dies, or advances the
phase by `phF w` and sets the bit to `lastGb g w b`. -/
theorem run_cstep_shape (g : A4) : ∀ (w : Word A4) (p : Fin 3) (b : Bool),
    run (cstep g) (some (p, b)) w = none
      ∨ run (cstep g) (some (p, b)) w = some (p + phF w, lastGb g w b)
  | [], p, b => Or.inr (by simp)
  | x :: w, p, b => by
    rw [run_cons]
    by_cases hc : p + phase x = 0 ∧ ¬ (x = g ∧ b = false)
    · left; rw [cstep_some, if_pos hc, run_cstep_none]
    · rw [cstep_some, if_neg hc]
      rcases run_cstep_shape g w (p + phase x) (decide (x = g)) with h | h
      · exact Or.inl h
      · right; rw [h, phF_cons, lastGb_cons, add_assoc]

/-- **I1.**  Started at the phase that makes its first letter a landing, a word
dies whenever the preceding letter was `g`. -/
theorem run_cstep_head_none (g x : A4) (v : Word A4) (p : Fin 3)
    (hp : p + phase x = 0) : run (cstep g) (some (p, true)) (x :: v) = none := by
  rw [run_cons, cstep_some, if_pos ⟨hp, by simp⟩, run_cstep_none]

/-- **I2.**  Started at the phase that makes its last letter a landing, a word
whose last letter is not `g` dies. -/
theorem run_cstep_last_none (g y : A4) (hy : y ≠ g) (v : Word A4) (p : Fin 3)
    (b : Bool) (hp : p + phF (v ++ [y]) = 0) :
    run (cstep g) (some (p, b)) (v ++ [y]) = none := by
  rw [run_append]
  rcases run_cstep_shape g v p b with h | h
  · rw [h, run_cstep_none]
  · have hph : (p + phF v) + phase y = 0 := by
      rw [phF_append, phF_cons, phF_nil, add_zero, ← add_assoc] at hp
      exact hp
    rw [h, run_cons, run_nil, cstep_some, if_pos ⟨hph, by simp [hy]⟩]

/-- If the phase sum vanishes, the live image is a fixed point. -/
theorem run_cstep_fix (g : A4) (w : Word A4) (β : Bool)
    (hb : ∀ c, lastGb g w c = β) (h0 : phF w = 0) (p : Fin 3) (c : Bool) :
    run (cstep g) (some (p, c)) w = none
      ∨ run (cstep g) (some (p, c)) w = some (p, β) := by
  rcases run_cstep_shape g w p c with h | h
  · exact Or.inl h
  · right; rw [h, h0, add_zero, hb]

/-- Phase-neutral words act idempotently from the second power on. -/
theorem run_cstep_idem (g : A4) (w : Word A4) (β : Bool)
    (hb : ∀ c, lastGb g w c = β) (h0 : phF w = 0) (q : CState) :
    run (cstep g) q (w ++ w ++ w) = run (cstep g) q (w ++ w) := by
  rcases q with _ | ⟨p, c⟩
  · rw [run_cstep_none, run_cstep_none]
  · simp only [run_append]
    rcases run_cstep_fix g w β hb h0 p c with h1 | h1
    · rw [h1, run_cstep_none, run_cstep_none]
    · rw [h1]
      rcases run_cstep_fix g w β hb h0 p β with h2 | h2
      · rw [h2, run_cstep_none]
      · rw [h2, h2]

/-! Three finite facts about `Fin 3`, all by exhaustion. -/

theorem fin3_cyc (p s : Fin 3) : p + s + s + s = p := by revert p s; decide

theorem fin3_cover (p s r : Fin 3) (hs : s ≠ 0) :
    r = p ∨ r = p + s ∨ r = p + s + s := by revert p s r; decide

theorem fin3_exists_neg (y : Fin 3) : ∃ r : Fin 3, r + y = 0 := by revert y; decide

/-- A nonempty word always has a starting phase from which it dies, provided
the start bit is the one its own last letter would set. -/
theorem run_cstep_exists_die (g x : A4) (v : Word A4) :
    ∃ r : Fin 3, run (cstep g) (some (r, lastGb g (x :: v) false)) (x :: v) = none := by
  cases hβ : lastGb g (x :: v) false with
  | true =>
    obtain ⟨r, hr⟩ := fin3_exists_neg (phase x)
    exact ⟨r, run_cstep_head_none g x v r hr⟩
  | false =>
    obtain ⟨v', y, hvy⟩ : ∃ v' y, x :: v = v' ++ [y] := by
      rcases List.eq_nil_or_concat (x :: v) with h | ⟨v', y, h⟩
      · exact absurd h (List.cons_ne_nil x v)
      · exact ⟨v', y, by rw [List.concat_eq_append] at h; exact h⟩
    have hy : y ≠ g := by
      rw [hvy, lastGb_concat] at hβ; simpa using hβ
    obtain ⟨r, hr⟩ := fin3_exists_neg (phF (x :: v))
    refine ⟨r, ?_⟩
    rw [hvy]
    exact run_cstep_last_none g y hy v' r false (by rw [← hvy]; exact hr)

/-- If the phase sum does not vanish, the fourth power kills every state. -/
theorem run_cstep_dead_aux (g : A4) (w : Word A4) (β : Bool)
    (hb : ∀ d, lastGb g w d = β) (hs : phF w ≠ 0)
    (hdie : ∃ r : Fin 3, run (cstep g) (some (r, β)) w = none) (q : CState) :
    run (cstep g) q (wpow w 4) = none := by
  rcases q with _ | ⟨p, c⟩
  · exact run_cstep_none g _
  by_contra hne
  have hexp : run (cstep g) (some (p, c)) (wpow w 4)
      = run (cstep g)
          (run (cstep g) (run (cstep g) (run (cstep g) (some (p, c)) w) w) w) w := by
    simp only [wpow_succ, wpow_zero, List.nil_append, run_append]
  rw [hexp] at hne
  have h1 : run (cstep g) (some (p, c)) w ≠ none := by
    intro h; exact hne (by rw [h, run_cstep_none, run_cstep_none, run_cstep_none])
  have h1' := (run_cstep_shape g w p c).resolve_left h1
  rw [hb] at h1'
  rw [h1'] at hne
  have h2 : run (cstep g) (some (p + phF w, β)) w ≠ none := by
    intro h; exact hne (by rw [h, run_cstep_none, run_cstep_none])
  have h2' := (run_cstep_shape g w (p + phF w) β).resolve_left h2
  rw [hb] at h2'
  rw [h2'] at hne
  have h3 : run (cstep g) (some (p + phF w + phF w, β)) w ≠ none := by
    intro h; exact hne (by rw [h, run_cstep_none])
  have h3' := (run_cstep_shape g w (p + phF w + phF w) β).resolve_left h3
  rw [hb, fin3_cyc] at h3'
  rw [h3'] at hne
  obtain ⟨r, hr⟩ := hdie
  rcases fin3_cover p (phF w) r hs with rfl | rfl | rfl
  · exact hne hr
  · exact h2 hr
  · exact h3 hr

/-- **Counter-freeness** of the cut-core automaton, with the uniform bound 4. -/
theorem run_cstep_aperiodic (g : A4) (q : CState) (w : Word A4) :
    run (cstep g) q (wpow w (4 + 1)) = run (cstep g) q (wpow w 4) := by
  match w with
  | [] => rw [wpow_nil, wpow_nil]
  | x :: v =>
    by_cases h0 : phF (x :: v) = 0
    · have hidem : ∀ r : CState,
          run (cstep g) r (wpow (x :: v) (2 + 1)) = run (cstep g) r (wpow (x :: v) 2) := by
        intro r
        simp only [wpow_succ, wpow_zero, List.nil_append]
        exact run_cstep_idem g (x :: v) (lastGb g v (decide (x = g))) (fun _ => rfl) h0 r
      have ha := run_wpow_stab (cstep g) (x :: v) 2 hidem 2 q
      have hc := run_wpow_stab (cstep g) (x :: v) 2 hidem 3 q
      show run (cstep g) q (wpow (x :: v) (2 + 3)) = run (cstep g) q (wpow (x :: v) (2 + 2))
      rw [ha, hc]
    · have hdead := run_cstep_dead_aux g (x :: v) (lastGb g (x :: v) false)
        (fun _ => rfl) h0 (run_cstep_exists_die g x v)
      rw [wpow_succ, run_append, hdead q, run_cstep_none]

/-! #### The automaton accepts exactly the cut core -/

/-- The residue of a natural number, as a state phase. -/
def fin3 (p : Nat) : Fin 3 := ⟨p % 3, Nat.mod_lt _ (by norm_num)⟩

theorem run_cstep_ne_none_iff (g : A4) : ∀ (w : Word A4) (p : Nat) (prev : Option A4),
    run (cstep g) (some (fin3 p, decide (prev = some g))) w ≠ none
      ↔ unm g 0 w p prev = 0
  | [], p, prev => by simp [unm, landingMarkCount_nil]
  | x :: w, p, prev => by
    have hland : (fin3 p + phase x = 0) ↔ ((p + (phase x).val) % 3 = (0 : Fin 3).val) := by
      rw [Fin.ext_iff, Fin.val_add]
      simp only [fin3, Fin.val_zero]
      omega
    have hmark : (¬ (x = g ∧ decide (prev = some g) = false))
        ↔ ((!moverMark g prev x) = true) := by
      simp only [moverMark]
      by_cases h1 : x = g <;> by_cases h2 : prev = some g <;> simp [h1, h2]
    rw [run_cons, unm, landingMarkCount_cons]
    by_cases hc : fin3 p + phase x = 0 ∧ ¬ (x = g ∧ decide (prev = some g) = false)
    · rw [cstep_some, if_pos hc, run_cstep_none]
      have hd : (p + (phase x).val) % 3 = (0 : Fin 3).val ∧ (!moverMark g prev x) = true :=
        ⟨hland.1 hc.1, hmark.1 hc.2⟩
      simp [hd]
    · rw [cstep_some, if_neg hc]
      have hd : ¬ ((p + (phase x).val) % 3 = (0 : Fin 3).val ∧ (!moverMark g prev x) = true) := by
        intro h; exact hc ⟨hland.2 h.1, hmark.2 h.2⟩
      rw [if_neg hd, Nat.zero_add]
      have hstate : fin3 p + phase x = fin3 (p + (phase x).val) := by
        apply Fin.ext
        rw [Fin.val_add]
        simp only [fin3]
        omega
      have hprev : decide (x = g) = decide (some x = some g) := by simp
      rw [hstate, hprev]
      exact run_cstep_ne_none_iff g w (p + (phase x).val) (some x)

/-- Accepting states: back at phase `0`, still alive. -/
def cutAccept : Set CState := {s | ∃ c : Bool, s = some ((0 : Fin 3), c)}

theorem cutCore_eq_run (g : A4) :
    cutCore g = {w : Word A4 | run (cstep g) (some ((0 : Fin 3), false)) w ∈ cutAccept} := by
  have hd : decide ((none : Option A4) = some g) = false := by simp
  have hf : fin3 0 = (0 : Fin 3) := rfl
  ext w
  constructor
  · rintro ⟨hps, hunm⟩
    have hne := (run_cstep_ne_none_iff g w 0 none).2 hunm
    rw [hd, hf] at hne
    rcases run_cstep_shape g w 0 false with h | h
    · exact absurd h hne
    · have h0 : phF w = 0 := by apply Fin.ext; rw [phF_val, hps]; rfl
      exact ⟨lastGb g w false, by rw [h, h0, add_zero]⟩
  · rintro ⟨c, hc⟩
    have hne : run (cstep g) (some ((0 : Fin 3), false)) w ≠ none := by rw [hc]; simp
    refine ⟨?_, (run_cstep_ne_none_iff g w 0 none).1 (by rw [hd, hf]; exact hne)⟩
    rcases run_cstep_shape g w 0 false with h | h
    · exact absurd h hne
    · rw [h] at hc
      have h0 : (0 : Fin 3) + phF w = 0 := (Prod.mk.injEq .. ▸ Option.some.inj hc : _ ∧ _).1
      have hv := phF_val w
      rw [zero_add] at h0
      rw [h0] at hv
      simpa using hv.symm

end CutCoreDFA

/--
**`N-A4-FULL-033c`** — the cut core is star-free.  Proved by exhibiting the
accepting automaton `cstep g`, showing it counter-free with the uniform bound
`4` (`run_cstep_aperiodic`), and applying Schützenberger's theorem in
automaton form.
-/
theorem starFree_cutCore (g : A4) (hg : phase g ≠ 0) :
    HasHeightAtMost (cutCore g) 0 := by
  rw [cutCore_eq_run g]
  exact TransitionMonoid.hasHeightAtMost_of_run (cstep g) (some ((0 : Fin 3), false))
    cutAccept 4 (run_cstep_aperiodic g)

theorem nil_mem_cutCore (g : A4) : [] ∈ cutCore g := ⟨rfl, rfl⟩

/-- The final landing of an unmatched block is unmatched no matter what
precedes the block. -/
theorem unm_of_mem_unmBlock {g : A4} (hg : phase g ≠ 0) {r : Word A4}
    (hr : r ∈ denote (unmBlock g)) (prev : Option A4) :
    unm g 0 r 0 prev = 1 ∧ phaseSum r % 3 = 0 := by
  rw [unmBlock, denote_inter] at hr
  obtain ⟨hfr, hnot⟩ := hr
  have hr0 : IsReturn0 r := (mem_frToken_iff_isReturn0 r).1 hfr
  obtain ⟨init, x, rfl, hinit, hsum⟩ := isReturn0_split hr0
  refine ⟨?_, hr0.2.1⟩
  show landingMarkCount _ 0 (init ++ [x]) 0 prev = 1
  rw [landingMarkCount_of_single_landing _ 0 prev hinit (by simpa using hsum)]
  -- the mark must be `false`
  have hmark : moverMark g (lastPrev init prev) x = false := by
    by_cases hxg : x = g
    · -- then `init` is nonempty and its last letter must be `g`
      have hne : init ≠ [] := by
        intro hnil
        refine hnot (Or.inl ?_)
        show init ++ [x] = [g]
        rw [hnil, List.nil_append, hxg]
      obtain ⟨init', y, hie⟩ : ∃ init' y, init = init' ++ [y] := by
        rcases List.eq_nil_or_concat init with h | ⟨i', y, h⟩
        · exact absurd h hne
        · exact ⟨i', y, by rw [List.concat_eq_append] at h; exact h⟩
      have hyg : y = g := by
        by_contra hyx
        refine hnot (Or.inr ?_)
        refine mem_denote_concat.2 ⟨init', [y] ++ [x], by rw [hie]; simp,
          mem_denote_univ _, ?_⟩
        refine mem_denote_concat.2 ⟨[y], [x], rfl, ?_, ?_⟩
        · rw [denote_atomsOf]
          exact ⟨y, by simp [List.mem_filter, A4LetterCut.mem_allA4 y, hyx], rfl⟩
        · show [x] = [g]
          rw [hxg]
      have hlast : lastPrev init prev = some y := by
        rw [hie, lastPrev_append]; rfl
      rw [hlast]
      simp [moverMark, hyg]
    · simp [moverMark, hxg]
  simp [hmark]

/-- `cutCore` absorbs a matched first-return block on the left. -/
theorem cons_block_mem_cutCore {g : A4} (hg : phase g ≠ 0) {r c : Word A4}
    (hr : IsReturn0 r) (hmr : unm g 0 r 0 none = 0) (hc : c ∈ cutCore g) :
    r ++ c ∈ cutCore g := by
  refine ⟨?_, ?_⟩
  · rw [phaseSum_append]
    have h1 := hr.2.1
    have h2 := hc.1
    omega
  · rw [unm_append, hmr, Nat.zero_add,
      unm_congr g 0 c (p' := 0) _ (by have := hr.2.1; omega),
      landingMarkCount_reset_indep g hg c (lastPrev r none) none]
    exact hc.2

theorem snoc_inj {u v : Word A4} {p q : A4} (h : u ++ [p] = v ++ [q]) :
    u = v ∧ p = q := by
  have hr := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append] at hr
  obtain ⟨h1, h2⟩ := List.cons.inj hr
  refine ⟨?_, h1⟩
  have := congrArg List.reverse h2
  simpa using this

theorem mem_denote_matchedEnd {g : A4} {r : Word A4} :
    r ∈ denote (matchedEnd g) ↔ (r = [g] ∨ ∃ a y, r = a ++ [y] ++ [g] ∧ y ≠ g) := by
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · obtain ⟨a, rest, rfl, _, hrest⟩ := mem_denote_concat.1 h
      obtain ⟨yy, gg, rfl, hy, hgg⟩ := mem_denote_concat.1 hrest
      rw [denote_atomsOf] at hy
      obtain ⟨y, hymem, rfl⟩ := hy
      refine Or.inr ⟨a, y, ?_, ?_⟩
      · rw [show gg = [g] from hgg, List.append_assoc]
      · simp only [List.mem_filter, decide_eq_true_eq] at hymem
        exact hymem.2
  · rintro (rfl | ⟨a, y, rfl, hy⟩)
    · exact Or.inl rfl
    · refine Or.inr (mem_denote_concat.2 ⟨a, [y] ++ [g], by simp,
        mem_denote_univ _, ?_⟩)
      refine mem_denote_concat.2 ⟨[y], [g], rfl, ?_, rfl⟩
      rw [denote_atomsOf]
      exact ⟨y, by simp [List.mem_filter, A4LetterCut.mem_allA4 y, hy], rfl⟩

/-- A first-return block whose end is matched contributes no cut event. -/
theorem unm_of_matched_block {g : A4} {r : Word A4} (hr : IsReturn0 r)
    (hend : r ∈ denote (matchedEnd g)) : unm g 0 r 0 none = 0 := by
  obtain ⟨init, x, hrx, hinit, hsum⟩ := isReturn0_split hr
  have hmark : moverMark g (lastPrev init none) x = true := by
    rcases mem_denote_matchedEnd.1 hend with h | ⟨a, y, h, hy⟩
    · have hs : init ++ [x] = [] ++ [g] := by rw [← hrx, h]; simp
      obtain ⟨hi, hx⟩ := snoc_inj hs
      subst hi; subst hx
      simp [moverMark]
    · have hs : init ++ [x] = (a ++ [y]) ++ [g] := by rw [← hrx, h]
      obtain ⟨hi, hx⟩ := snoc_inj hs
      subst hx
      have hlast : lastPrev init none = some y := by
        simp [hi, lastPrev_append]
      rw [hlast]
      simp [moverMark, hy]
  show landingMarkCount _ 0 r 0 none = 0
  rw [hrx, landingMarkCount_of_single_landing _ 0 none hinit (by simpa using hsum)]
  simp [hmark]

/-! ### The token, the opener and the cut system -/

/-- Token of the mover cut: matched blocks, then one unmatched block. -/
def moverToken (g : A4) (core : GRegex A4) : GRegex A4 :=
  concat core (unmBlock g)

theorem starHeight_moverToken (g : A4) {core : GRegex A4}
    (hc : starHeight core = 0) : starHeight (moverToken g core) = 0 := by
  change max (starHeight core) (starHeight (unmBlock g)) = 0
  rw [hc, starHeight_unmBlock]; rfl

theorem unm_of_mem_moverToken {g : A4} (hg : phase g ≠ 0) {core : GRegex A4}
    (hcore : denote core = cutCore g) {u : Word A4}
    (hu : u ∈ denote (moverToken g core)) (prev : Option A4) :
    unm g 0 u 0 prev = 1 ∧ phaseSum u % 3 = 0 := by
  obtain ⟨c, r, rfl, hc, hr⟩ := mem_denote_concat.1 hu
  rw [hcore] at hc
  obtain ⟨hcs, hcu⟩ := hc
  obtain ⟨hru, hrs⟩ := unm_of_mem_unmBlock hg hr (lastPrev c prev)
  constructor
  · rw [unm_append, landingMarkCount_reset_indep g hg c prev none, hcu, Nat.zero_add,
      unm_congr g 0 r (p' := 0) _ (by omega), hru]
  · rw [phaseSum_append]; omega

theorem unm_append_moverToken {g : A4} (hg : phase g ≠ 0) {core : GRegex A4}
    (hcore : denote core = cutCore g) {u : Word A4}
    (hu : u ∈ denote (moverToken g core)) (v : Word A4) (prev : Option A4) :
    unm g 0 (u ++ v) 0 prev = 1 + unm g 0 v 0 none := by
  obtain ⟨h1, h2⟩ := unm_of_mem_moverToken hg hcore hu prev
  rw [unm_append, h1, unm_congr g 0 v (p' := 0) _ (by omega),
    landingMarkCount_reset_indep g hg v (lastPrev u prev) none]

theorem exists_moverToken_prefix {g : A4} (hg : phase g ≠ 0) {core : GRegex A4}
    (hcore : denote core = cutCore g) :
    ∀ (n : Nat) (w : Word A4), w.length ≤ n → 0 < unm g 0 w 0 none →
      ∃ u v, w = u ++ v ∧ u ∈ denote (moverToken g core)
  | 0, w, hlen, hpos => by
    have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hw
    exact absurd hpos (by simp [unm, landingMarkCount_nil])
  | n + 1, w, hlen, hpos => by
    have hlc : 0 < landingCount 0 w 0 :=
      Nat.lt_of_lt_of_le hpos (unm_le g 0 w 0 none)
    obtain ⟨r, v₀, rfl, hr, _⟩ := exists_first_return_prefix hlc
    by_cases hend : r ∈ denote (matchedEnd g)
    · -- matched block: it contributes nothing, recurse on the rest
      have hru : unm g 0 r 0 none = 0 := unm_of_matched_block hr hend
      have hcount : unm g 0 (r ++ v₀) 0 none = unm g 0 v₀ 0 none := by
        rw [unm_append, hru, Nat.zero_add,
          unm_congr g 0 v₀ (p' := 0) _ (by have := hr.2.1; omega),
          landingMarkCount_reset_indep g hg v₀ (lastPrev r none) none]
      have hpos' : 0 < unm g 0 v₀ 0 none := by rw [← hcount]; exact hpos
      have hlen' : v₀.length ≤ n := by
        have hrne : 0 < r.length := List.length_pos_of_ne_nil hr.1
        simp only [List.length_append] at hlen
        omega
      obtain ⟨u', v, hveq, hu'⟩ :=
        exists_moverToken_prefix hg hcore n v₀ hlen' hpos'
      obtain ⟨c, s, hu'eq, hc, hs⟩ := mem_denote_concat.1 hu'
      rw [hcore] at hc
      refine ⟨(r ++ c) ++ s, v, by rw [hveq, hu'eq]; simp, ?_⟩
      refine mem_denote_concat.2 ⟨r ++ c, s, rfl, ?_, hs⟩
      rw [hcore]
      exact cons_block_mem_cutCore hg hr hru hc
    · -- unmatched block: the token is this block alone
      refine ⟨r, v₀, rfl, mem_denote_concat.2 ⟨[], r, rfl, ?_, ?_⟩⟩
      · rw [hcore]; exact nil_mem_cutCore g
      · rw [unmBlock, denote_inter]
        exact ⟨(mem_frToken_iff_isReturn0 r).2 hr, hend⟩

/-- Opener of the mover cut at a nonzero phase: the first arrival at `q`,
extended by matched blocks if that arrival was itself matched. -/
def moverOpener (g : A4) (q : Fin 3) (core : GRegex A4) : GRegex A4 :=
  union (inter (opener q) (compl (matchedEnd g)))
    (concat (inter (opener q) (matchedEnd g)) (moverToken g core))

theorem starHeight_moverOpener (g : A4) (q : Fin 3) {core : GRegex A4}
    (hc : starHeight core = 0) : starHeight (moverOpener g q core) = 0 := by
  change max (max (starHeight (opener q)) (starHeight (matchedEnd g)))
    (max (max (starHeight (opener q)) (starHeight (matchedEnd g)))
      (starHeight (moverToken g core))) = 0
  rw [starHeight_opener, starHeight_matchedEnd, starHeight_moverToken g hc]
  rfl

theorem moverMark_snoc_iff {g : A4} {u init : Word A4} {x : A4}
    (hux : u = init ++ [x]) :
    moverMark g (lastPrev init none) x = true ↔ u ∈ denote (matchedEnd g) := by
  constructor
  · intro hm
    simp only [moverMark, decide_eq_true_eq] at hm
    obtain ⟨hxg, hprev⟩ := hm
    subst hxg
    rcases List.eq_nil_or_concat init with hnil | ⟨a, y, hcat⟩
    · rw [hux, hnil]; exact Or.inl rfl
    · rw [List.concat_eq_append] at hcat
      have hlast : lastPrev init none = some y := by
        simp [hcat, lastPrev_append]
      rw [hlast] at hprev
      refine mem_denote_matchedEnd.2 (Or.inr ⟨a, y, ?_, ?_⟩)
      · rw [hux, hcat]
      · intro hyg; exact hprev (by rw [hyg])
  · intro hm
    rcases mem_denote_matchedEnd.1 hm with h | ⟨a, y, h, hy⟩
    · have hs : init ++ [x] = [] ++ [g] := by rw [← hux, h]; simp
      obtain ⟨hi, hx⟩ := snoc_inj hs
      subst hi; subst hx
      simp [moverMark]
    · have hs : init ++ [x] = (a ++ [y]) ++ [g] := by rw [← hux, h]
      obtain ⟨hi, hx⟩ := snoc_inj hs
      subst hx
      have hlast : lastPrev init none = some y := by
        simp [hi, lastPrev_append]
      rw [hlast]
      simp [moverMark, hy]

theorem unm_of_isArrival_matched {g : A4} {q : Fin 3} {u : Word A4}
    (hu : IsArrival q u) (hend : u ∈ denote (matchedEnd g)) :
    unm g q u 0 none = 0 := by
  obtain ⟨init, x, hux, hinit, hsum⟩ := isArrival_split hu
  have hm : moverMark g (lastPrev init none) x = true :=
    (moverMark_snoc_iff hux).2 hend
  show landingMarkCount _ q u 0 none = 0
  rw [hux, landingMarkCount_of_single_landing _ q none hinit hsum]
  simp [hm]

theorem unm_of_isArrival_unmatched {g : A4} {q : Fin 3} {u : Word A4}
    (hu : IsArrival q u) (hend : u ∉ denote (matchedEnd g)) :
    unm g q u 0 none = 1 := by
  obtain ⟨init, x, hux, hinit, hsum⟩ := isArrival_split hu
  have hm : moverMark g (lastPrev init none) x ≠ true := fun hc =>
    hend ((moverMark_snoc_iff hux).1 hc)
  show landingMarkCount _ q u 0 none = 1
  rw [hux, landingMarkCount_of_single_landing _ q none hinit hsum]
  simp [hm]

/-- The mover cut at phase `0`: opener and token coincide. -/
def moverCut0 {g : A4} (hg : phase g ≠ 0) {core : GRegex A4}
    (hcore : denote core = cutCore g) : CutSystem A4 where
  cnt0 := fun w => unm g 0 w 0 none
  cnt1 := fun w => unm g 0 w 0 none
  opener := moverToken g core
  token := moverToken g core
  opener_append := fun u hu v => unm_append_moverToken hg hcore hu v none
  token_append := fun u hu v => unm_append_moverToken hg hcore hu v none
  opener_peel := fun w hw =>
    exists_moverToken_prefix hg hcore w.length w (le_refl _) hw
  token_peel := fun w hw =>
    exists_moverToken_prefix hg hcore w.length w (le_refl _) hw

/-- The mover cut at a nonzero phase `q`. -/
def moverCut {g : A4} (hg : phase g ≠ 0) {q : Fin 3} (hq : q ≠ 0)
    {core : GRegex A4} (hcore : denote core = cutCore g) : CutSystem A4 where
  cnt0 := fun w => unm g q w 0 none
  cnt1 := fun w => unm g 0 w 0 none
  opener := moverOpener g q core
  token := moverToken g core
  opener_append := by
    intro u hu v
    rcases hu with hu | hu
    · -- the first arrival is itself the cut event
      rw [denote_inter] at hu
      obtain ⟨ho, hnot⟩ := hu
      have ha : IsArrival q u := by rw [denote_opener hq] at ho; exact ho
      rw [unm_append, unm_of_isArrival_unmatched ha hnot,
        unm_congr g q v (p' := q.val + 0) _ (by have := ha.2.1; omega),
        unm_shift g q v 0 (lastPrev u none),
        landingMarkCount_reset_indep g hg v (lastPrev u none) none]
    · -- the arrival is matched; the cut event is inside the following token
      obtain ⟨a, t, rfl, ha, ht⟩ := mem_denote_concat.1 hu
      rw [denote_inter] at ha
      obtain ⟨ho, hmem⟩ := ha
      have ha' : IsArrival q a := by rw [denote_opener hq] at ho; exact ho
      rw [List.append_assoc, unm_append, unm_of_isArrival_matched ha' hmem,
        Nat.zero_add,
        unm_congr g q (t ++ v) (p' := q.val + 0) _ (by have := ha'.2.1; omega),
        unm_shift g q (t ++ v) 0 (lastPrev a none)]
      exact unm_append_moverToken hg hcore ht v (lastPrev a none)
  token_append := fun u hu v => unm_append_moverToken hg hcore hu v none
  opener_peel := by
    intro w hw
    have hlc : 0 < landingCount q w 0 := Nat.lt_of_lt_of_le hw (unm_le g q w 0 none)
    obtain ⟨a, w', rfl, ha, _⟩ := exists_first_arrival_prefix hlc
    by_cases hmem : a ∈ denote (matchedEnd g)
    · -- peel the arrival, then a token
      have h0 : unm g q a 0 none = 0 := unm_of_isArrival_matched ha hmem
      have hrest : unm g q (a ++ w') 0 none = unm g 0 w' 0 none := by
        rw [unm_append, h0, Nat.zero_add,
          unm_congr g q w' (p' := q.val + 0) _ (by have := ha.2.1; omega),
          unm_shift g q w' 0 (lastPrev a none),
          landingMarkCount_reset_indep g hg w' (lastPrev a none) none]
      obtain ⟨t, v, hveq, ht⟩ :=
        exists_moverToken_prefix hg hcore w'.length w' (le_refl _)
          (by rw [← hrest]; exact hw)
      have hain : a ∈ denote (inter (opener q) (matchedEnd g)) := by
        rw [denote_inter]
        exact ⟨by rw [denote_opener hq]; exact ha, hmem⟩
      refine ⟨a ++ t, v, by rw [hveq]; simp, Or.inr ?_⟩
      exact mem_denote_concat.2 ⟨a, t, rfl, hain, ht⟩
    · refine ⟨a, w', rfl, Or.inl ?_⟩
      rw [denote_inter]
      exact ⟨by rw [denote_opener hq]; exact ha, hmem⟩
  token_peel := fun w hw =>
    exists_moverToken_prefix hg hcore w.length w (le_refl _) hw

/-- Parity of the unmatched-landing count is height ≤ 1. -/
theorem unmParity_hasHeightAtMost_one {g : A4} (hg : phase g ≠ 0) (q : Fin 3)
    {core : GRegex A4} (hcore : denote core = cutCore g)
    (hch : starHeight core = 0) :
    HasHeightAtMost {w : Word A4 | unm g q w 0 none % 2 = 0} 1 := by
  by_cases hq : q = 0
  · subst hq
    exact (moverCut0 hg hcore).hasHeightAtMost_one
      (starHeight_moverToken g hch) (starHeight_moverToken g hch)
  · exact (moverCut hg hq hcore).hasHeightAtMost_one
      (starHeight_moverOpener g q hch) (starHeight_moverToken g hch)

/-- Parity of the **matched**-landing count `A_q` is height ≤ 1. -/
theorem mchParity_hasHeightAtMost_one {g : A4} (hg : phase g ≠ 0) (q : Fin 3) :
    HasHeightAtMost {w : Word A4 | mch g q w 0 none % 2 = 0} 1 := by
  obtain ⟨core, hcore, hch0⟩ := starFree_cutCore g hg
  have hch : starHeight core = 0 := Nat.le_zero.mp hch0
  have hset : {w : Word A4 | mch g q w 0 none % 2 = 0}
      = {w : Word A4 | (landingCount q w 0 + unm g q w 0 none) % 2 = 0} := by
    ext w
    have h := mch_add_unm g q w 0 none
    simp only [Set.mem_setOf_eq]
    omega
  rw [hset]
  exact hasHeightAtMost_parity_add
    (landingParity_hasHeightAtMost_one q)
    (unmParity_hasHeightAtMost_one hg q hcore hch)

/-! ## 4.  Occurrence counts and the digram identity

All four counts below index the *entry* phase by a natural number tested
mod 3, which avoids `Fin` arithmetic in the index bookkeeping. -/

/-- Occurrences of `g` at entry phase `p`. -/
def occ (g : A4) (p : Nat) : Word A4 → Nat → Nat
  | [], _ => 0
  | x :: w, s =>
      (if x = g ∧ s % 3 = p % 3 then 1 else 0) + occ g p w (s + (phase x).val)

/-- Occurrences of `g` at entry phase `p` **not preceded** by `g`. -/
def occL (g : A4) (p : Nat) : Word A4 → Nat → Option A4 → Nat
  | [], _, _ => 0
  | x :: w, s, prev =>
      (if x = g ∧ s % 3 = p % 3 ∧ prev ≠ some g then 1 else 0)
        + occL g p w (s + (phase x).val) (some x)

/-- Occurrences of `g` at entry phase `p` **preceded** by `g`. -/
def occP (g : A4) (p : Nat) : Word A4 → Nat → Option A4 → Nat
  | [], _, _ => 0
  | x :: w, s, prev =>
      (if x = g ∧ s % 3 = p % 3 ∧ prev = some g then 1 else 0)
        + occP g p w (s + (phase x).val) (some x)

/-- Occurrences of `g` at entry phase `p` **not followed** by `g`. -/
def occR (g : A4) (p : Nat) : Word A4 → Nat → Nat
  | [], _ => 0
  | [x], s => if x = g ∧ s % 3 = p % 3 then 1 else 0
  | x :: y :: w, s =>
      (if x = g ∧ s % 3 = p % 3 ∧ y ≠ g then 1 else 0)
        + occR g p (y :: w) (s + (phase x).val)

/-- `gg` digrams, indexed by the entry phase of their **first** letter. -/
def dig (g : A4) (p : Nat) : Word A4 → Nat → Nat
  | [], _ => 0
  | [_], _ => 0
  | x :: y :: w, s =>
      (if x = g ∧ y = g ∧ s % 3 = p % 3 then 1 else 0)
        + dig g p (y :: w) (s + (phase x).val)

theorem occ_congr (g : A4) {p p' : Nat} (h : p % 3 = p' % 3) :
    ∀ (w : Word A4) (s : Nat), occ g p w s = occ g p' w s
  | [], _ => rfl
  | x :: w, s => by
    rw [occ, occ, occ_congr g h w (s + (phase x).val), h]

theorem occL_congr (g : A4) {p p' : Nat} (h : p % 3 = p' % 3) :
    ∀ (w : Word A4) (s : Nat) (prev : Option A4),
      occL g p w s prev = occL g p' w s prev
  | [], _, _ => rfl
  | x :: w, s, prev => by
    rw [occL, occL, occL_congr g h w (s + (phase x).val) (some x), h]

theorem occR_congr (g : A4) {p p' : Nat} (h : p % 3 = p' % 3) :
    ∀ (w : Word A4) (s : Nat), occR g p w s = occR g p' w s
  | [], _ => rfl
  | [x], s => by rw [occR, occR, h]
  | x :: y :: w, s => by
    rw [occR, occR, occR_congr g h (y :: w) (s + (phase x).val), h]

/-- Every occurrence is either preceded by `g` or not. -/
theorem occ_eq_occL_add_occP (g : A4) (p : Nat) :
    ∀ (w : Word A4) (s : Nat) (prev : Option A4),
      occ g p w s = occL g p w s prev + occP g p w s prev
  | [], _, _ => rfl
  | x :: w, s, prev => by
    rw [occ, occL, occP, occ_eq_occL_add_occP g p w (s + (phase x).val) (some x)]
    by_cases hx : x = g
    · by_cases hs : s % 3 = p % 3
      · by_cases hp : prev = some g <;> simp [hx, hs, hp] <;> omega
      · simp [hs]
    · simp [hx]

/-- Every occurrence is either followed by `g` (i.e. starts a digram) or not. -/
theorem occ_eq_occR_add_dig (g : A4) (p : Nat) :
    ∀ (w : Word A4) (s : Nat), occ g p w s = occR g p w s + dig g p w s
  | [], _ => rfl
  | [x], s => by
    rw [occ, occR, dig, occ]
  | x :: y :: w, s => by
    rw [occ, occR, dig, occ_eq_occR_add_dig g p (y :: w) (s + (phase x).val)]
    by_cases hx : x = g
    · by_cases hs : s % 3 = p % 3
      · by_cases hy : y = g <;> simp [hx, hs, hy] <;> omega
      · simp [hs]
    · simp [hx]

/-- **Digram identity.**  Counting the `gg` digrams by the entry phase of
their second letter is the same as counting them by that of their first. -/
theorem occP_eq_dig (g : A4) (p : Nat) :
    ∀ (w : Word A4) (s : Nat) (prev : Option A4),
      occP g (p + (phase g).val) w s prev
        = dig g p w s
          + (if prev = some g ∧ w.head? = some g
                ∧ s % 3 = (p + (phase g).val) % 3 then 1 else 0)
  | [], _, prev => by simp [occP, dig]
  | [x], s, prev => by
    rw [occP, dig, occP]
    simp only [List.head?_cons, Option.some.injEq, Nat.add_zero, Nat.zero_add]
    by_cases hx : x = g <;> by_cases hp : prev = some g <;>
      by_cases hs : s % 3 = (p + (phase g).val) % 3 <;> simp [hx, hp, hs]
  | x :: y :: w, s, prev => by
    rw [occP, dig, occP_eq_dig g p (y :: w) (s + (phase x).val) (some x)]
    have hT14 :
        (if x = g ∧ s % 3 = (p + (phase g).val) % 3 ∧ prev = some g then (1:Nat) else 0)
          = (if prev = some g ∧ (x :: y :: w).head? = some g
                ∧ s % 3 = (p + (phase g).val) % 3 then (1:Nat) else 0) := by
      simp only [List.head?_cons, Option.some.injEq]
      by_cases hx : x = g <;> by_cases hp : prev = some g <;>
        by_cases hs : s % 3 = (p + (phase g).val) % 3 <;> simp [hx, hp, hs]
    have hT23 :
        (if some x = some g ∧ (y :: w).head? = some g
              ∧ (s + (phase x).val) % 3 = (p + (phase g).val) % 3 then (1:Nat) else 0)
          = (if x = g ∧ y = g ∧ s % 3 = p % 3 then (1:Nat) else 0) := by
      simp only [List.head?_cons, Option.some.injEq]
      refine if_congr ?_ rfl rfl
      constructor
      · rintro ⟨hx, hy, hs⟩
        have hphase : (phase x).val = (phase g).val := by rw [hx]
        rw [hphase] at hs
        exact ⟨hx, hy, by omega⟩
      · rintro ⟨hx, hy, hs⟩
        have hphase : (phase x).val = (phase g).val := by rw [hx]
        refine ⟨hx, hy, ?_⟩
        rw [hphase]
        omega
    rw [hT14, hT23]
    omega

/-- The key linear relation, free of the total phase. -/
theorem occ_shift_add_occR (g : A4) (p : Nat) (w : Word A4) (s : Nat) :
    occ g (p + (phase g).val) w s + occR g p w s
      = occL g (p + (phase g).val) w s none + occ g p w s := by
  have h1 := occ_eq_occL_add_occP g (p + (phase g).val) w s none
  have h2 := occ_eq_occR_add_dig g p w s
  have h3 : occP g (p + (phase g).val) w s none = dig g p w s := by
    simpa using occP_eq_dig g p w s none
  omega

/-! ## 5.  Reversal: `occR` on `w` is `occL` on `w.reverse` -/

theorem occR_cons (g : A4) (p : Nat) (x : A4) (w : Word A4) (s : Nat) :
    occR g p (x :: w) s
      = (if x = g ∧ s % 3 = p % 3 ∧ w.head? ≠ some g then 1 else 0)
        + occR g p w (s + (phase x).val) := by
  cases w with
  | nil => simp [occR]
  | cons y w => rw [occR]; simp

theorem occL_append (g : A4) (p : Nat) :
    ∀ (u v : Word A4) (s : Nat) (prev : Option A4),
      occL g p (u ++ v) s prev
        = occL g p u s prev + occL g p v (s + phaseSum u) (lastPrev u prev)
  | [], v, s, prev => by simp [occL, phaseSum]
  | x :: u, v, s, prev => by
    simp only [List.cons_append, occL, phaseSum_cons, lastPrev_cons]
    rw [occL_append g p u v (s + (phase x).val) (some x)]
    simp [Nat.add_assoc]

theorem lastPrev_reverse (w : Word A4) : lastPrev w.reverse none = w.head? := by
  cases w with
  | nil => rfl
  | cons y t => rw [List.reverse_cons, lastPrev_append]; rfl

theorem occR_eq_occL_reverse (g : A4) :
    ∀ (w : Word A4) (s p r : Nat),
      (r + p + (phase g).val) % 3 = (phaseSum w + s) % 3 →
      occR g p w s = occL g r w.reverse 0 none
  | [], _, _, _, _ => rfl
  | x :: w, s, p, r, h => by
    have hIH : occR g p w (s + (phase x).val) = occL g r w.reverse 0 none := by
      refine occR_eq_occL_reverse g w (s + (phase x).val) p r ?_
      rw [phaseSum_cons] at h
      omega
    rw [occR_cons, List.reverse_cons, occL_append, hIH, lastPrev_reverse,
      phaseSum_reverse]
    have hlast : occL g r [x] (0 + phaseSum w) w.head?
        = if x = g ∧ (0 + phaseSum w) % 3 = r % 3 ∧ w.head? ≠ some g
          then 1 else 0 := by
      simp [occL]
    rw [hlast]
    have hind : (if x = g ∧ s % 3 = p % 3 ∧ w.head? ≠ some g then (1:Nat) else 0)
        = if x = g ∧ (0 + phaseSum w) % 3 = r % 3 ∧ w.head? ≠ some g
          then (1:Nat) else 0 := by
      refine if_congr ?_ rfl rfl
      constructor
      · rintro ⟨hx, hs, hh⟩
        refine ⟨hx, ?_, hh⟩
        have hphase : (phase x).val = (phase g).val := by rw [hx]
        rw [phaseSum_cons, hphase] at h
        omega
      · rintro ⟨hx, hs, hh⟩
        refine ⟨hx, ?_, hh⟩
        have hphase : (phase x).val = (phase g).val := by rw [hx]
        rw [phaseSum_cons, hphase] at h
        omega
    rw [hind]
    omega

/-! ## 6.  Bridges to the existing features -/

theorem occ_eq_typedCount (g : A4) (p : Fin 3) :
    ∀ (w : Word A4) (s : Nat), occ g p.val w s = typedCount (pairType g p) w s
  | [], _ => rfl
  | x :: w, s => by
    rw [occ, typedCount_cons, occ_eq_typedCount g p w (s + (phase x).val)]
    congr 1
    have hp := p.isLt
    by_cases hx : x = g
    · have hval : (⟨s % 3, by omega⟩ : Fin 3).val = s % 3 := rfl
      have hiff : (s % 3 = p.val % 3) ↔ ((⟨s % 3, by omega⟩ : Fin 3) = p) := by
        rw [Fin.ext_iff, hval]; omega
      simp only [pairType, decide_eq_true_eq]
      refine if_congr ?_ rfl rfl
      constructor
      · rintro ⟨_, hs⟩; exact ⟨hx, hiff.1 hs⟩
      · rintro ⟨_, hs⟩; exact ⟨hx, hiff.2 hs⟩
    · simp [pairType, hx]

theorem occL_eq_mch (g : A4) (p : Nat) :
    ∀ (w : Word A4) (s : Nat) (prev : Option A4),
      occL g p w s prev
        = mch g ⟨(p + (phase g).val) % 3, by omega⟩ w s prev
  | [], _, _ => rfl
  | x :: w, s, prev => by
    rw [occL, mch, landingMarkCount_cons, ← mch,
      occL_eq_mch g p w (s + (phase x).val) (some x)]
    congr 1
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨hx, hs, hp⟩
      have hphase : (phase x).val = (phase g).val := by rw [hx]
      refine ⟨?_, by simp [moverMark, hx, hp]⟩
      simp only []
      rw [hphase]
      omega
    · rintro ⟨hs, hm⟩
      simp only [moverMark, decide_eq_true_eq] at hm
      obtain ⟨hx, hp⟩ := hm
      have hphase : (phase x).val = (phase g).val := by rw [hx]
      refine ⟨hx, ?_, hp⟩
      simp only [] at hs
      rw [hphase] at hs
      omega

theorem occ_sum (g : A4) :
    ∀ (w : Word A4) (s : Nat),
      occ g 0 w s + occ g 1 w s + occ g 2 w s = countSet [g] w
  | [], _ => rfl
  | x :: w, s => by
    rw [occ, occ, occ, countSet_cons, ← occ_sum g w (s + (phase x).val)]
    by_cases hx : x = g
    · rcases (show s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 by omega) with h | h | h <;>
        simp [hx, h] <;> omega
    · simp [hx]

/-! ## 7.  Heights of the two auxiliary features -/

theorem occLParity_hasHeightAtMost_one {g : A4} (hg : phase g ≠ 0) (p : Nat) :
    HasHeightAtMost {w : Word A4 | occL g p w 0 none % 2 = 0} 1 := by
  have hset : {w : Word A4 | occL g p w 0 none % 2 = 0}
      = {w : Word A4 |
          mch g ⟨(p + (phase g).val) % 3, by omega⟩ w 0 none % 2 = 0} := by
    ext w
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, occL_eq_mch]
  rw [hset]
  exact mchParity_hasHeightAtMost_one hg _

theorem occRParity_hasHeightAtMost_one {g : A4} (hg : phase g ≠ 0) (p : Nat) :
    HasHeightAtMost {w : Word A4 | occR g p w 0 % 2 = 0} 1 := by
  have hlt := (phase g).isLt
  have hkey : ∀ (T : Nat) (w : Word A4), phaseSum w % 3 = T % 3 →
      occR g p w 0 = occL g ((T + 6 - p % 3 - (phase g).val) % 3) w.reverse 0 none := by
    intro T w hT
    exact occR_eq_occL_reverse g w 0 p _ (by omega)
  have hset : {w : Word A4 | occR g p w 0 % 2 = 0}
      = (({w : Word A4 | phaseSum w % 3 = (0 : Fin 3).val} ∩
            reverseLang {v : Word A4 |
              occL g ((0 + 6 - p % 3 - (phase g).val) % 3) v 0 none % 2 = 0}) ∪
         (({w : Word A4 | phaseSum w % 3 = (1 : Fin 3).val} ∩
            reverseLang {v : Word A4 |
              occL g ((1 + 6 - p % 3 - (phase g).val) % 3) v 0 none % 2 = 0}) ∪
          ({w : Word A4 | phaseSum w % 3 = (2 : Fin 3).val} ∩
            reverseLang {v : Word A4 |
              occL g ((2 + 6 - p % 3 - (phase g).val) % 3) v 0 none % 2 = 0}))) := by
    ext w
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq,
      mem_reverseLang_iff, Fin.val_zero, Fin.val_one, Fin.val_two]
    rcases (show phaseSum w % 3 = 0 ∨ phaseSum w % 3 = 1 ∨ phaseSum w % 3 = 2
      by omega) with hT | hT | hT
    · rw [hkey 0 w (by omega)]; simp [hT]
    · rw [hkey 1 w (by omega)]; simp [hT]
    · rw [hkey 2 w (by omega)]; simp [hT]
  rw [hset]
  refine hasHeightAtMost_union
    (hasHeightAtMost_inter (phaseClass_hasHeightAtMost_one 0)
      (hasHeightAtMost_reverse (occLParity_hasHeightAtMost_one hg _)))
    (hasHeightAtMost_union
      (hasHeightAtMost_inter (phaseClass_hasHeightAtMost_one 1)
        (hasHeightAtMost_reverse (occLParity_hasHeightAtMost_one hg _)))
      (hasHeightAtMost_inter (phaseClass_hasHeightAtMost_one 2)
        (hasHeightAtMost_reverse (occLParity_hasHeightAtMost_one hg _))))

/-! ## 8.  The mover case of `N-A4-FULL-033` -/

/--
**Mover case of `N-A4-FULL-033`** (obligation `N-A4-FULL-033e`).  The
recovery is the phase-free GF(2) solution
`N[g,p] ≡ |w|_g + occL (p+2ε) + occR (p+ε)`.
-/
theorem moverPairParity_hasHeightAtMost_one {g : A4} (hg : phase g ≠ 0) (p : Fin 3) :
    HasHeightAtMost {w : Word A4 | typedCount (pairType g p) w 0 % 2 = 0} 1 := by
  have hlt := (phase g).isLt
  have hp := p.isLt
  have hgv : (phase g).val ≠ 0 := fun h => hg (Fin.ext h)
  have hheight : HasHeightAtMost {w : Word A4 |
      (countSet [g] w + (occL g ((p.val + 2 * (phase g).val) % 3) w 0 none
        + occR g ((p.val + (phase g).val) % 3) w 0)) % 2 = 0} 1 :=
    hasHeightAtMost_parity_add (countMod2_hasHeightAtMost_one [g] 0)
      (hasHeightAtMost_parity_add (occLParity_hasHeightAtMost_one hg _)
        (occRParity_hasHeightAtMost_one hg _))
  have hset : {w : Word A4 | typedCount (pairType g p) w 0 % 2 = 0}
      = {w : Word A4 |
          (countSet [g] w + (occL g ((p.val + 2 * (phase g).val) % 3) w 0 none
            + occR g ((p.val + (phase g).val) % 3) w 0)) % 2 = 0} := by
    ext w
    simp only [Set.mem_setOf_eq]
    rw [← occ_eq_typedCount g p w 0]
    have hS := occ_sum g w 0
    have E0 := occ_shift_add_occR g 0 w 0
    have E1 := occ_shift_add_occR g 1 w 0
    have E2 := occ_shift_add_occR g 2 w 0
    have nOcc : ∀ i j : Nat, i % 3 = j % 3 → occ g i w 0 = occ g j w 0 :=
      fun i j h => occ_congr g h w 0
    have nOccL : ∀ i j : Nat, i % 3 = j % 3 → occL g i w 0 none = occL g j w 0 none :=
      fun i j h => occL_congr g h w 0 none
    rcases (show (phase g).val = 1 ∨ (phase g).val = 2 by omega) with he | he
    · rw [he] at E0 E1 E2
      norm_num at E0 E1 E2
      rw [nOcc 3 0 (by omega), nOccL 3 0 (by omega)] at E2
      rw [he]
      rcases (show p.val = 0 ∨ p.val = 1 ∨ p.val = 2 by omega)
        with hpv | hpv | hpv <;> rw [hpv] <;> norm_num <;> omega
    · rw [he] at E0 E1 E2
      norm_num at E0 E1 E2
      rw [nOcc 3 0 (by omega), nOccL 3 0 (by omega)] at E1
      rw [nOcc 4 1 (by omega), nOccL 4 1 (by omega)] at E2
      rw [he]
      rcases (show p.val = 0 ∨ p.val = 1 ∨ p.val = 2 by omega)
        with hpv | hpv | hpv <;> rw [hpv] <;> norm_num <;> omega
  rw [hset]
  exact hheight

end A4MoverCut
end GSH
