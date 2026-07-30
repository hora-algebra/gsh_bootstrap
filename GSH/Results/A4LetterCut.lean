import GSH.Results.A4CutFeature

/-!
# Letter-marked cuts: the filler case of `N-A4-FULL-033`

`GSH/Results/A4CutFeature.lean` proves that the unconditioned cut feature
`Z_q = landingCount q` has height ≤ 1.  This file adds the first
*letter-conditioned* cut and closes the **filler third** of
`N-A4-FULL-033`: for every letter `h` of phase `0` and every `p : Fin 3`,

    { w | N[h,p](w) even }   has generalized star height at most one.

## The construction

For a filler `h`, mark a landing as *matched* when its letter is `h`.  Two
facts make the cut core trivial:

* a first-return block whose last letter is a filler is that single letter
  (`isReturn0_eq_single_of_last_filler`), so the matched blocks are exactly
  the one-letter blocks `[h]` and the cut core is `{h}*`, which is star-free
  (`onlyLetter`);
* a first *arrival* at a phase `q ≠ 0` never ends in a filler, so the opener
  of `A4CutFeature` is reused verbatim.

Hence the token is `{h}* · (frToken \ Σ*h)`, star-free, and the cut system of
`GSH/Regex/CutParity.lean` applies.  The unmatched count is `Z_q - N[h,q]`,
so `N[h,q] ≡ Z_q + (Z_q - N[h,q]) (mod 2)` and
`hasHeightAtMost_parity_add` finishes.

Since `phase h = 0`, the *entry* phase and the *landing* phase of an
occurrence of `h` coincide, so the matched count is literally
`typedCount (pairType h q)` (`landingSetCount_eq_typedCount`).

This file contains no `sorry` and no `axiom`.
-/

set_option autoImplicit false

namespace GSH
namespace A4LetterCut

open GRegex Language A4Structure A4CutFeature CountHeight List

/-! ## 1.  Landings restricted to a set of letters -/

/-- Number of landings on `q` (from start phase `p`) whose letter satisfies
`S`. -/
def landingSetCount (S : A4 → Bool) (q : Fin 3) : Word A4 → Nat → Nat
  | [], _ => 0
  | g :: w, p =>
      (if (p + (phase g).val) % 3 = q.val ∧ S g = true then 1 else 0)
        + landingSetCount S q w (p + (phase g).val)

theorem landingSetCount_nil (S : A4 → Bool) (q : Fin 3) (p : Nat) :
    landingSetCount S q [] p = 0 := rfl

theorem landingSetCount_cons (S : A4 → Bool) (q : Fin 3) (g : A4) (w : Word A4)
    (p : Nat) :
    landingSetCount S q (g :: w) p =
      (if (p + (phase g).val) % 3 = q.val ∧ S g = true then 1 else 0)
        + landingSetCount S q w (p + (phase g).val) := rfl

theorem landingSetCount_append (S : A4 → Bool) (q : Fin 3) :
    ∀ (u v : Word A4) (p : Nat),
      landingSetCount S q (u ++ v) p
        = landingSetCount S q u p + landingSetCount S q v (p + phaseSum u)
  | [], v, p => by simp [landingSetCount_nil, phaseSum]
  | g :: u, v, p => by
    simp only [List.cons_append, landingSetCount_cons, phaseSum_cons]
    rw [landingSetCount_append S q u v (p + (phase g).val)]
    simp [Nat.add_assoc]

theorem landingSetCount_congr (S : A4 → Bool) (q : Fin 3) :
    ∀ (w : Word A4) (p p' : Nat), p % 3 = p' % 3 →
      landingSetCount S q w p = landingSetCount S q w p'
  | [], _, _, _ => rfl
  | g :: w, p, p', h => by
    have hstep : (p + (phase g).val) % 3 = (p' + (phase g).val) % 3 := by omega
    rw [landingSetCount_cons, landingSetCount_cons,
      landingSetCount_congr S q w (p + (phase g).val) (p' + (phase g).val) hstep,
      hstep]

theorem landingSetCount_shift (S : A4 → Bool) (q : Fin 3) :
    ∀ (w : Word A4) (p : Nat),
      landingSetCount S q w (q.val + p) = landingSetCount S 0 w p
  | [], _ => rfl
  | g :: w, p => by
    rw [landingSetCount_cons, landingSetCount_cons]
    have harg : q.val + p + (phase g).val = q.val + (p + (phase g).val) := by omega
    rw [harg, landingSetCount_shift S q w (p + (phase g).val)]
    congr 1
    have hqlt := q.isLt
    have hiff : ((q.val + (p + (phase g).val)) % 3 = q.val)
        ↔ ((p + (phase g).val) % 3 = (0 : Fin 3).val) := by
      simp only [Fin.val_zero]; omega
    by_cases hc : (p + (phase g).val) % 3 = (0 : Fin 3).val
    · rw [if_congr (and_congr_left fun _ => hiff) rfl rfl]
    · rw [if_congr (and_congr_left fun _ => hiff) rfl rfl]

theorem landingSetCount_le (S : A4 → Bool) (q : Fin 3) :
    ∀ (w : Word A4) (p : Nat), landingSetCount S q w p ≤ landingCount q w p
  | [], _ => Nat.le_refl _
  | g :: w, p => by
    rw [landingSetCount_cons, landingCount_cons]
    have ih := landingSetCount_le S q w (p + (phase g).val)
    by_cases hc : (p + (phase g).val) % 3 = q.val
    · by_cases hs : S g = true <;> simp [hc, hs] <;> omega
    · simp [hc]; omega

/-- Splitting the landings according to a Boolean test on their letter. -/
theorem landingCount_eq_add (S : A4 → Bool) (q : Fin 3) :
    ∀ (w : Word A4) (p : Nat),
      landingCount q w p
        = landingSetCount S q w p + landingSetCount (fun g => !S g) q w p
  | [], _ => rfl
  | g :: w, p => by
    rw [landingCount_cons, landingSetCount_cons, landingSetCount_cons,
      landingCount_eq_add S q w (p + (phase g).val)]
    by_cases hc : (p + (phase g).val) % 3 = q.val
    · by_cases hs : S g = true <;> simp [hc, hs] <;> omega
    · simp [hc]

/-- For a filler, the landing phase *is* the entry phase, so restricted
landing counts are single-pair typed counts. -/
theorem landingSetCount_eq_typedCount {h : A4} (hh : phase h = 0) (q : Fin 3) :
    ∀ (w : Word A4) (p : Nat),
      landingSetCount (fun g => decide (g = h)) q w p = typedCount (pairType h q) w p
  | [], _ => rfl
  | g :: w, p => by
    rw [landingSetCount_cons, typedCount_cons,
      landingSetCount_eq_typedCount hh q w (p + (phase g).val)]
    congr 1
    by_cases hg : g = h
    · subst hg
      have hz : (phase g).val = 0 := by rw [hh]; rfl
      rw [hz, Nat.add_zero]
      have hiff : (p % 3 = q.val) ↔ ((⟨p % 3, by omega⟩ : Fin 3) = q) := by
        rw [Fin.ext_iff]
      by_cases hc : p % 3 = q.val
      · simp [pairType, hc, (hiff.1 hc)]
      · have : ¬((⟨p % 3, by omega⟩ : Fin 3) = q) := fun hh2 => hc (hiff.2 hh2)
        simp [pairType, hc, this]
    · simp [pairType, hg]

/-! ## 2.  First-return and first-arrival blocks under a letter test -/

/-- A first-return block whose last letter is a filler is a single letter. -/
theorem isReturn0_eq_single_of_last_filler {u : Word A4} {x : A4}
    (hr : IsReturn0 (u ++ [x])) (hx : phase x = 0) : u = [] := by
  by_contra hne
  rcases isReturn0_last_phase_ne_zero hr hne with h | h <;> rw [hx] at h <;>
    exact absurd h (by decide)

theorem landingSetCount_of_landingCount_zero (S : A4 → Bool) (q : Fin 3)
    {w : Word A4} {p : Nat} (h : landingCount q w p = 0) :
    landingSetCount S q w p = 0 := by
  have := landingSetCount_le S q w p
  omega

/-- A word with a single landing, at its last letter, contributes to a
restricted count exactly according to that letter. -/
theorem landingSetCount_of_single_landing (S : A4 → Bool) (q : Fin 3)
    {init : Word A4} {x : A4} (hinit : landingCount q init 0 = 0)
    (hsum : (phaseSum init + (phase x).val) % 3 = q.val) :
    landingSetCount S q (init ++ [x]) 0 = if S x = true then 1 else 0 := by
  rw [landingSetCount_append, landingSetCount_of_landingCount_zero S q hinit,
    Nat.zero_add, landingSetCount_cons, landingSetCount_nil, Nat.add_zero]
  by_cases hs : S x = true
  · simp [hs, hsum]
  · simp [hs]

/-- Split a first-return word at its last letter. -/
theorem isReturn0_split {r : Word A4} (hr : IsReturn0 r) :
    ∃ init x, r = init ++ [x] ∧ landingCount 0 init 0 = 0 ∧
      (phaseSum init + (phase x).val) % 3 = 0 := by
  obtain ⟨init, x, hrx⟩ : ∃ init x, r = init ++ [x] := by
    rcases List.eq_nil_or_concat r with h | ⟨init, x, h⟩
    · exact absurd h hr.1
    · exact ⟨init, x, by rw [List.concat_eq_append] at h; exact h⟩
  have hlen : r.length = init.length + 1 := by rw [hrx]; simp
  refine ⟨init, x, hrx, ?_, ?_⟩
  · rw [landingCount0_eq_zero_iff]
    intro k hk
    have hpr : init.take (k + 1) = r.take (k + 1) := by
      rw [hrx, take_append_of_le_length (by omega)]
    rw [hpr]
    exact hr.2.2 (k + 1) (by omega) (by omega)
  · have := hr.2.1
    rw [hrx, phaseSum_append, phaseSum_singleton] at this
    exact this

/-- Split a first-arrival word at its last letter. -/
theorem isArrival_split {q : Fin 3} {u : Word A4} (hu : IsArrival q u) :
    ∃ init x, u = init ++ [x] ∧ landingCount q init 0 = 0 ∧
      (phaseSum init + (phase x).val) % 3 = q.val := by
  obtain ⟨init, x, hux⟩ : ∃ init x, u = init ++ [x] := by
    rcases List.eq_nil_or_concat u with h | ⟨init, x, h⟩
    · exact absurd h hu.1
    · exact ⟨init, x, by rw [List.concat_eq_append] at h; exact h⟩
  have hlen : u.length = init.length + 1 := by rw [hux]; simp
  refine ⟨init, x, hux, ?_, ?_⟩
  · rw [landingCount_eq_zero_iff]
    intro k hk
    have hpr : init.take (k + 1) = u.take (k + 1) := by
      rw [hux, take_append_of_le_length (by omega)]
    rw [Nat.zero_add, hpr]
    exact hu.2.2 (k + 1) (by omega) (by omega)
  · have := hu.2.1
    rw [hux, phaseSum_append, phaseSum_singleton] at this
    exact this

/-! ## 3.  The letter-conditioned token -/

/-- All twelve letters of `A₄`. -/
def allA4 : List A4 := lettersOfPhase 0 ++ lettersOfPhase 1 ++ lettersOfPhase 2

theorem mem_allA4 (g : A4) : g ∈ allA4 := by
  have hmem : g ∈ lettersOfPhase (phase g) := (mem_lettersOfPhase_iff g _).2 rfl
  match hph : phase g with
  | ⟨0, _⟩ => simp only [allA4, List.mem_append]; exact Or.inl (Or.inl (by rwa [hph] at hmem))
  | ⟨1, _⟩ => simp only [allA4, List.mem_append]; exact Or.inl (Or.inr (by rwa [hph] at hmem))
  | ⟨2, _⟩ => simp only [allA4, List.mem_append]; exact Or.inr (by rwa [hph] at hmem)

/-- `{h}*`, written star-free as "avoid every other letter". -/
def onlyLetter (h : A4) : GRegex A4 :=
  avoidSet (allA4.filter (fun x => decide (x ≠ h)))

theorem starHeight_onlyLetter (h : A4) : starHeight (onlyLetter h) = 0 :=
  starHeight_avoidSet _

theorem denote_onlyLetter (h : A4) :
    denote (onlyLetter h) = {w : Word A4 | ∀ x ∈ w, x = h} := by
  rw [onlyLetter, denote_avoidSet]
  ext w
  simp only [Set.mem_setOf_eq, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro hyp x hx
    by_contra hne
    exact hyp x ⟨mem_allA4 x, hne⟩ hx
  · intro hyp a ha hax
    exact ha.2 (hyp a hax)

/-- Words ending with the letter `h`. -/
def endsWith (h : A4) : GRegex A4 := concat univ (atom h)

theorem starHeight_endsWith (h : A4) : starHeight (endsWith h) = 0 := by
  change max (starHeight (univ : GRegex A4)) (starHeight (atom h)) = 0
  rw [starHeight_univ, starHeight_atom]; rfl

theorem mem_denote_endsWith {h : A4} {w : Word A4} :
    w ∈ denote (endsWith h) ↔ ∃ u, w = u ++ [h] := by
  simp only [endsWith]
  constructor
  · intro hmem
    obtain ⟨u, v, rfl, _, hv⟩ := mem_denote_concat.1 hmem
    exact ⟨u, by rw [show v = [h] from hv]⟩
  · rintro ⟨u, rfl⟩
    exact mem_denote_concat.2 ⟨u, [h], rfl, mem_denote_univ u, rfl⟩

/-- Token of the `h`-conditioned cut: any number of matched `[h]` blocks,
then one first-return block that does **not** end in `h`. -/
def fillerToken (h : A4) : GRegex A4 :=
  concat (onlyLetter h) (inter frToken (compl (endsWith h)))

theorem starHeight_fillerToken (h : A4) : starHeight (fillerToken h) = 0 := by
  change max (starHeight (onlyLetter h))
    (max (starHeight frToken) (starHeight (endsWith h))) = 0
  rw [starHeight_onlyLetter, starHeight_frToken, starHeight_endsWith]; rfl

/-! ## 4.  The unmatched-landing count -/

/-- Landings whose letter is **not** `h`. -/
def unmatched (h : A4) (q : Fin 3) (w : Word A4) (p : Nat) : Nat :=
  landingSetCount (fun g => !decide (g = h)) q w p

theorem unmatched_append (h : A4) (q : Fin 3) (u v : Word A4) (p : Nat) :
    unmatched h q (u ++ v) p = unmatched h q u p + unmatched h q v (p + phaseSum u) :=
  landingSetCount_append _ _ u v p

theorem unmatched_le (h : A4) (q : Fin 3) (w : Word A4) (p : Nat) :
    unmatched h q w p ≤ landingCount q w p := landingSetCount_le _ _ w p

theorem unmatched_congr (h : A4) (q : Fin 3) (w : Word A4) {p p' : Nat}
    (hp : p % 3 = p' % 3) : unmatched h q w p = unmatched h q w p' :=
  landingSetCount_congr _ q w p p' hp

theorem unmatched_of_onlyLetter {h : A4} {f : Word A4}
    (hf : ∀ x ∈ f, x = h) (q : Fin 3) (p : Nat) : unmatched h q f p = 0 := by
  induction f generalizing p with
  | nil => rfl
  | cons a l ih =>
    have ha : a = h := hf a (by simp)
    subst ha
    rw [unmatched, landingSetCount_cons]
    simp only [decide_true, Bool.not_true, Bool.false_eq_true, and_false, if_false,
      Nat.zero_add]
    exact ih (fun x hx => hf x (by simp [hx])) _

/-- A first-return block contributes one unmatched landing exactly when its
last letter is not `h`. -/
theorem unmatched_of_isReturn0 {h : A4} {r : Word A4} (hr : IsReturn0 r)
    (hnot : r ∉ denote (endsWith h)) : unmatched h 0 r 0 = 1 := by
  obtain ⟨init, x, rfl, hinit, hsum⟩ := isReturn0_split hr
  have hx : x ≠ h := by
    intro hxh
    exact hnot (mem_denote_endsWith.2 ⟨init, by rw [hxh]⟩)
  rw [unmatched,
    landingSetCount_of_single_landing _ 0 hinit (by simpa using hsum)]
  simp [hx]

/-- A first-arrival block at `q ≠ 0` never ends in a filler, so it always
contributes one unmatched landing. -/
theorem unmatched_of_isArrival {h : A4} (hh : phase h = 0) {q : Fin 3} (hq : q ≠ 0)
    {u : Word A4} (hu : IsArrival q u) : unmatched h q u 0 = 1 := by
  obtain ⟨init, x, rfl, hinit, hsum⟩ := isArrival_split hu
  have hx : x ≠ h := by
    intro hxh
    subst hxh
    have hxz : (phase x).val = 0 := by rw [hh]; rfl
    rw [hxz, Nat.add_zero] at hsum
    -- then `init` already reaches phase `q`, contradicting first arrival
    rcases Nat.eq_zero_or_pos init.length with h0 | hpos
    · have : init = [] := List.eq_nil_of_length_eq_zero h0
      subst this
      simp only [phaseSum, List.map_nil, List.sum_nil, Nat.zero_mod] at hsum
      exact hq (Fin.ext hsum.symm)
    · have hlt : init.length < (init ++ [x]).length := by simp
      have hpref : (init ++ [x]).take init.length = init := by
        rw [take_append_of_length_le _ _ (le_refl _)]; simp
      have hne := hu.2.2 init.length hpos hlt
      rw [hpref] at hne
      exact hne hsum
  rw [unmatched, landingSetCount_of_single_landing _ q hinit hsum]
  simp [hx]

theorem unmatched_shift (h : A4) (q : Fin 3) (w : Word A4) :
    unmatched h q w q.val = unmatched h 0 w 0 := by
  show landingSetCount (fun g => !decide (g = h)) q w q.val
      = landingSetCount (fun g => !decide (g = h)) 0 w 0
  have := landingSetCount_shift (fun g => !decide (g = h)) q w 0
  simpa using this

theorem unmatched_append_zero (h : A4) (q : Fin 3) {u : Word A4} (v : Word A4)
    (hu : phaseSum u % 3 = 0) :
    unmatched h q (u ++ v) 0 = unmatched h q u 0 + unmatched h q v 0 := by
  rw [unmatched_append, Nat.zero_add]
  congr 1
  exact landingSetCount_congr _ q v (phaseSum u) 0 (by omega)

/-! ## 5.  Peeling the token -/

theorem mem_fillerToken_of_isReturn0 {h : A4} {r : Word A4} (hr : IsReturn0 r)
    (hnot : r ∉ denote (endsWith h)) : r ∈ denote (fillerToken h) := by
  refine mem_denote_concat.2 ⟨[], r, rfl, ?_, ?_⟩
  · rw [denote_onlyLetter]; intro x hx; simp at hx
  · rw [denote_inter]
    exact ⟨(mem_frToken_iff_isReturn0 r).2 hr, hnot⟩

theorem mem_fillerToken_cons {h : A4} {u : Word A4}
    (hu : u ∈ denote (fillerToken h)) : (h :: u) ∈ denote (fillerToken h) := by
  obtain ⟨f, r, rfl, hf, hr⟩ := mem_denote_concat.1 hu
  refine mem_denote_concat.2 ⟨h :: f, r, rfl, ?_, hr⟩
  rw [denote_onlyLetter] at hf ⊢
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · rfl
  · exact hf x hx

theorem phaseSum_of_onlyLetter {h : A4} (hh : phase h = 0) {f : Word A4}
    (hf : ∀ x ∈ f, x = h) : phaseSum f = 0 := by
  apply phaseSum_of_mem_fill
  rw [denote_fill]
  intro x hx
  rw [hf x hx, hh]

theorem unmatched_append_fillerToken {h : A4} (hh : phase h = 0)
    {u : Word A4} (hu : u ∈ denote (fillerToken h)) (v : Word A4) :
    unmatched h 0 (u ++ v) 0 = 1 + unmatched h 0 v 0 := by
  obtain ⟨f, r, rfl, hf, hr⟩ := mem_denote_concat.1 hu
  rw [denote_onlyLetter] at hf
  rw [denote_inter] at hr
  have hr0 : IsReturn0 r := (mem_frToken_iff_isReturn0 r).1 hr.1
  have hfs : phaseSum f = 0 := phaseSum_of_onlyLetter hh hf
  have hus : phaseSum (f ++ r) % 3 = 0 := by
    rw [phaseSum_append, hfs, Nat.zero_add]; exact hr0.2.1
  have hu1 : unmatched h 0 (f ++ r) 0 = 1 := by
    rw [unmatched_append_zero h 0 r (by rw [hfs]),
      unmatched_of_onlyLetter hf 0 0, Nat.zero_add,
      unmatched_of_isReturn0 hr0 hr.2]
  rw [unmatched_append_zero h 0 v hus, hu1]

theorem unmatched_append_opener {h : A4} (hh : phase h = 0) {q : Fin 3} (hq : q ≠ 0)
    {u : Word A4} (hu : u ∈ denote (opener q)) (v : Word A4) :
    unmatched h q (u ++ v) 0 = 1 + unmatched h 0 v 0 := by
  have hu' : IsArrival q u := by rw [denote_opener hq] at hu; exact hu
  rw [unmatched_append, Nat.zero_add, unmatched_of_isArrival hh hq hu']
  congr 1
  rw [unmatched_congr h q v (p' := q.val) (by rw [hu'.2.1]; omega)]
  exact unmatched_shift h q v

theorem exists_fillerToken_prefix {h : A4} (hh : phase h = 0) :
    ∀ (n : Nat) (w : Word A4), w.length ≤ n → 0 < unmatched h 0 w 0 →
      ∃ u v, w = u ++ v ∧ u ∈ denote (fillerToken h) ∧
        unmatched h 0 v 0 = unmatched h 0 w 0 - 1
  | 0, w, hlen, hpos => by
    have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hw
    exact absurd hpos (by simp [unmatched, landingSetCount_nil])
  | n + 1, w, hlen, hpos => by
    have hlc : 0 < landingCount 0 w 0 :=
      Nat.lt_of_lt_of_le hpos (unmatched_le h 0 w 0)
    obtain ⟨r, v₀, rfl, hr, _⟩ := exists_first_return_prefix hlc
    by_cases hend : r ∈ denote (endsWith h)
    · -- matched block: it is the single letter `[h]`
      obtain ⟨init', hinit'⟩ := mem_denote_endsWith.1 hend
      have hnil : init' = [] :=
        isReturn0_eq_single_of_last_filler (by rw [← hinit']; exact hr) hh
      have hrh : r = [h] := by rw [hinit', hnil]; rfl
      subst hrh
      have hcount : unmatched h 0 ([h] ++ v₀) 0 = unmatched h 0 v₀ 0 := by
        rw [unmatched_append_zero h 0 v₀ (by rw [phaseSum_singleton, hh]; rfl),
          unmatched_of_onlyLetter (by intro x hx; simpa using hx) 0 0, Nat.zero_add]
      have hpos' : 0 < unmatched h 0 v₀ 0 := by rw [← hcount]; exact hpos
      have hlen' : v₀.length ≤ n := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
      obtain ⟨u', v, hveq, hu', hv⟩ := exists_fillerToken_prefix hh n v₀ hlen' hpos'
      refine ⟨h :: u', v, by rw [hveq]; rfl, mem_fillerToken_cons hu', ?_⟩
      rw [hcount]; exact hv
    · -- unmatched block
      refine ⟨r, v₀, rfl, mem_fillerToken_of_isReturn0 hr hend, ?_⟩
      rw [unmatched_append_zero h 0 v₀ hr.2.1, unmatched_of_isReturn0 hr hend]
      omega

/-! ## 6.  The cut systems and the filler pair parities -/

/-- Cut at the unmatched landings on phase `0`. -/
def fillerCut0 {h : A4} (hh : phase h = 0) : CutSystem A4 where
  cnt0 := fun w => unmatched h 0 w 0
  cnt1 := fun w => unmatched h 0 w 0
  opener := fillerToken h
  token := fillerToken h
  opener_append := fun u hu v => unmatched_append_fillerToken hh hu v
  token_append := fun u hu v => unmatched_append_fillerToken hh hu v
  opener_peel := by
    intro w hw
    obtain ⟨u, v, hsplit, hu, _⟩ :=
      exists_fillerToken_prefix hh w.length w (le_refl _) hw
    exact ⟨u, v, hsplit, hu⟩
  token_peel := by
    intro w hw
    obtain ⟨u, v, hsplit, hu, _⟩ :=
      exists_fillerToken_prefix hh w.length w (le_refl _) hw
    exact ⟨u, v, hsplit, hu⟩

/-- Cut at the unmatched landings on a nonzero phase `q`. -/
def fillerCut {h : A4} (hh : phase h = 0) {q : Fin 3} (hq : q ≠ 0) : CutSystem A4 where
  cnt0 := fun w => unmatched h q w 0
  cnt1 := fun w => unmatched h 0 w 0
  opener := opener q
  token := fillerToken h
  opener_append := fun u hu v => unmatched_append_opener hh hq hu v
  token_append := fun u hu v => unmatched_append_fillerToken hh hu v
  opener_peel := by
    intro w hw
    have hlc : 0 < landingCount q w 0 := Nat.lt_of_lt_of_le hw (unmatched_le h q w 0)
    obtain ⟨u, v, hsplit, hu, _⟩ := exists_first_arrival_prefix hlc
    exact ⟨u, v, hsplit, by rw [denote_opener hq]; exact hu⟩
  token_peel := by
    intro w hw
    obtain ⟨u, v, hsplit, hu, _⟩ :=
      exists_fillerToken_prefix hh w.length w (le_refl _) hw
    exact ⟨u, v, hsplit, hu⟩

theorem unmatchedParity_hasHeightAtMost_one {h : A4} (hh : phase h = 0) (q : Fin 3) :
    HasHeightAtMost {w : Word A4 | unmatched h q w 0 % 2 = 0} 1 := by
  by_cases hq : q = 0
  · subst hq
    exact (fillerCut0 hh).hasHeightAtMost_one
      (starHeight_fillerToken h) (starHeight_fillerToken h)
  · exact (fillerCut hh hq).hasHeightAtMost_one
      (starHeight_opener q) (starHeight_fillerToken h)

/--
**Filler case of `N-A4-FULL-033`.**  For a letter `h` of phase `0` and any
`q : Fin 3`, the single-pair parity `N[h,q] mod 2` has generalized star
height at most one.
-/
theorem fillerPairParity_hasHeightAtMost_one {h : A4} (hh : phase h = 0) (q : Fin 3) :
    HasHeightAtMost {w : Word A4 | typedCount (pairType h q) w 0 % 2 = 0} 1 := by
  have hsplit : ∀ w : Word A4,
      landingCount q w 0 = typedCount (pairType h q) w 0 + unmatched h q w 0 := by
    intro w
    rw [landingCount_eq_add (fun g => decide (g = h)) q w 0,
      landingSetCount_eq_typedCount hh q w 0]
    rfl
  have hset : {w : Word A4 | typedCount (pairType h q) w 0 % 2 = 0}
      = {w : Word A4 | (landingCount q w 0 + unmatched h q w 0) % 2 = 0} := by
    ext w
    have := hsplit w
    simp only [Set.mem_setOf_eq]
    omega
  rw [hset]
  exact hasHeightAtMost_parity_add
    (landingParity_hasHeightAtMost_one q)
    (unmatchedParity_hasHeightAtMost_one hh q)

end A4LetterCut
end GSH
