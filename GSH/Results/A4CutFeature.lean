import GSH.Regex.Sugar
import GSH.Regex.HeightClosure
import GSH.Regex.CountHeight
import GSH.Regex.CutParity
import GSH.Groups.A4Structure
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Pattern-free cut features for the `A₄` phase counter

Unconditional cuts at phase `q` count landings on `q`.  A candidate height-1
expression used the five vertex-simple `C₃` cycles
`+0`, `+1+2`, `+2+1`, `+1³`, `+2³` with phase-0 fillers (`returnToken`,
star-free).  That language is a **proper subset** of first-return words
`IsReturn0` (counterexample: mover word `t·t·t²·t²`, phases `1,1,2,2`).

The corrected token `frToken` uses the *boundary-pair characterization*:
a first-return word is a single phase-0 letter, a mixed two-mover pair, or
has ≥ 3 movers with first and last adjacent-mover pairs same-type and no
same-type pair strictly inside.  This is certified computationally in
`scripts/research/a4_first_return_token.py`; `starHeight frToken = 0` is proved
below, and `denote frToken = IsReturn0` is obligation `N-A4-FULL-038`.
`evenReturns`/`noReturn` are built on `frToken`.  See `RESULTS.md` §5.5
for the pattern-conditioned cut construction (`Z_q`).
-/

set_option autoImplicit false

namespace GSH
namespace A4CutFeature

open GRegex Language A4Structure CountHeight List

/-! ## Alphabet partitions by phase -/

def fill : GRegex A4 :=
  avoidSet (lettersOfPhase 1 ++ lettersOfPhase 2)

def A0 : GRegex A4 := atomsOf (lettersOfPhase 0)
def A1 : GRegex A4 := atomsOf (lettersOfPhase 1)
def A2 : GRegex A4 := atomsOf (lettersOfPhase 2)

theorem starHeight_fill : starHeight fill = 0 := starHeight_avoidSet _
theorem starHeight_A0 : starHeight A0 = 0 := starHeight_atomsOf _
theorem starHeight_A1 : starHeight A1 = 0 := starHeight_atomsOf _
theorem starHeight_A2 : starHeight A2 = 0 := starHeight_atomsOf _

theorem denote_fill :
    denote fill = {w : Word A4 | ∀ g ∈ w, phase g = 0} := by
  ext w
  simp only [fill, denote_avoidSet, Set.mem_setOf_eq, mem_append]
  constructor
  · intro h g hg
    by_contra hne
    have hmem : g ∈ lettersOfPhase (phase g) := (mem_lettersOfPhase_iff g _).2 rfl
    match hph : phase g with
    | ⟨0, _⟩ => exact hne (by simp [hph])
    | ⟨1, _⟩ =>
      exact h g (Or.inl (by simpa [hph] using hmem)) hg
    | ⟨2, _⟩ =>
      exact h g (Or.inr (by simpa [hph] using hmem)) hg
  · intro h a ha hw
    rcases ha with ha | ha
    · have hph : phase a = 1 := (mem_lettersOfPhase_iff a 1).1 ha
      have := h a hw
      simp [hph] at this
    · have hph : phase a = 2 := (mem_lettersOfPhase_iff a 2).1 ha
      have := h a hw
      simp [hph] at this

theorem mem_denote_A0 {w : Word A4} :
    w ∈ denote A0 ↔ ∃ g, phase g = 0 ∧ w = [g] := by
  simp only [A0, denote_atomsOf]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, (mem_lettersOfPhase_iff g 0).1 hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, (mem_lettersOfPhase_iff g 0).2 hg, rfl⟩

theorem mem_denote_A1 {w : Word A4} :
    w ∈ denote A1 ↔ ∃ g, phase g = 1 ∧ w = [g] := by
  simp only [A1, denote_atomsOf]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, (mem_lettersOfPhase_iff g 1).1 hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, (mem_lettersOfPhase_iff g 1).2 hg, rfl⟩

theorem mem_denote_A2 {w : Word A4} :
    w ∈ denote A2 ↔ ∃ g, phase g = 2 ∧ w = [g] := by
  simp only [A2, denote_atomsOf]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, (mem_lettersOfPhase_iff g 2).1 hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, (mem_lettersOfPhase_iff g 2).2 hg, rfl⟩

/-! ### Elementary membership helpers -/

theorem mem_denote_concat {r s : GRegex A4} {w : Word A4} :
    w ∈ denote (concat r s) ↔
      ∃ u v, w = u ++ v ∧ u ∈ denote r ∧ v ∈ denote s := by
  simp only [denote, mem_concat_iff]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, v, rfl, hu, hv⟩
  · rintro ⟨u, v, rfl, hu, hv⟩; exact ⟨u, hu, v, hv, rfl⟩

theorem mem_denote_compl {r : GRegex A4} {w : Word A4} :
    w ∈ denote (compl r) ↔ w ∉ denote r := Iff.rfl

theorem mem_denote_univ (w : Word A4) : w ∈ denote (univ : GRegex A4) := by
  rw [denote_univ]; exact Set.mem_univ w

theorem phaseSum_singleton (g : A4) : phaseSum [g] = (phase g).val := by
  simp [phaseSum]

theorem phaseSum_of_mem_fill {w : Word A4} (hw : w ∈ denote fill) :
    phaseSum w = 0 := by
  rw [denote_fill] at hw
  induction w with
  | nil => rfl
  | cons g gs ih =>
    simp [phaseSum_cons, hw g (by simp), ih fun x hx => hw x (by simp [hx])]

theorem phaseSum_append (u v : Word A4) :
    phaseSum (u ++ v) = phaseSum u + phaseSum v := by
  induction u with
  | nil => simp [phaseSum]
  | cons g gs ih => simp [phaseSum_cons, ih, Nat.add_assoc]

theorem phaseSum_take_fill {f : Word A4} (hf : f ∈ denote fill) (n : Nat) :
    phaseSum (f.take n) = 0 := by
  apply phaseSum_of_mem_fill
  rw [denote_fill] at hf ⊢
  intro x hx
  exact hf x (List.mem_of_mem_take hx)

theorem take_append_of_length_le {α : Type*} (l₁ l₂ : List α) {n : Nat}
    (h : l₁.length ≤ n) :
    (l₁ ++ l₂).take n = l₁ ++ l₂.take (n - l₁.length) := by
  rw [take_append, take_of_length_le h]


theorem landingCount_append (q : Fin 3) :
    ∀ (u v : Word A4) (p : Nat),
      landingCount q (u ++ v) p =
        landingCount q u p + landingCount q v (p + phaseSum u)
  | [], v, p => by simp [landingCount_nil, phaseSum]
  | g :: u, v, p => by
    simp only [cons_append, landingCount_cons, phaseSum_cons]
    rw [landingCount_append q u v (p + (phase g).val)]
    simp [Nat.add_assoc]

theorem landingCount_fill_offcut (q : Fin 3) {p : Nat} {w : Word A4}
    (hp : p % 3 ≠ q.val) (hw : w ∈ denote fill) :
    landingCount q w p = 0 := by
  rw [denote_fill] at hw
  induction w generalizing p with
  | nil => rfl
  | cons g gs ih =>
    have hg : phase g = 0 := hw g (by simp)
    have hgs : gs ∈ {w : Word A4 | ∀ x ∈ w, phase x = 0} := by
      simp only [Set.mem_setOf_eq]
      exact fun x hx => hw x (by simp [hx])
    simp only [landingCount_cons, hg, Nat.add_zero]
    have : ¬ p % 3 = q.val := hp
    simp [this]
    exact ih (by simpa [Nat.add_mod_right] using hp) hgs

/-! ### Phase classes have height ≤ 1

`phaseSum` is the weighted mod-3 count `n₁ + 2 n₂` of the phase-1 and phase-2
letters, so each phase class is a union of three intersections of mod-3 count
languages.  (`GSH/Results/A4FullAlphabet.lean` proves the `c = 0` case
separately for the `phaseZero` route; this is the general statement, used by
`GSH/Results/A4MoverCut.lean`.) -/

theorem phaseSum_eq_weighted (w : Word A4) :
    phaseSum w =
      countSet (lettersOfPhase 1) w + 2 * countSet (lettersOfPhase 2) w := by
  induction w with
  | nil => simp [phaseSum, countSet]
  | cons g gs ih =>
    rw [phaseSum_cons, countSet_cons, countSet_cons, ih]
    have hmem : ∀ e : Fin 3, g ∈ lettersOfPhase e ↔ phase g = e :=
      fun e => mem_lettersOfPhase_iff g e
    match h : phase g with
    | ⟨0, _⟩ =>
      have h1 : (g ∈ lettersOfPhase 1) = False := by simp [hmem 1, h]
      have h2 : (g ∈ lettersOfPhase 2) = False := by simp [hmem 2, h]
      simp [h, h1, h2]
    | ⟨1, _⟩ =>
      have h1 : g ∈ lettersOfPhase 1 := (hmem 1).2 (by simpa using h)
      have h2 : g ∉ lettersOfPhase 2 := by
        intro hgg; have := (hmem 2).1 hgg; simp [h] at this
      simp [h, h1, h2]
      ring
    | ⟨2, _⟩ =>
      have h1 : g ∉ lettersOfPhase 1 := by
        intro hgg; have := (hmem 1).1 hgg; simp [h] at this
      have h2 : g ∈ lettersOfPhase 2 := (hmem 2).2 (by simpa using h)
      simp [h, h1, h2]
      ring

theorem phaseClass_hasHeightAtMost_one (c : Fin 3) :
    HasHeightAtMost {w : Word A4 | phaseSum w % 3 = c.val} 1 := by
  have hset : {w : Word A4 | phaseSum w % 3 = c.val} =
      ({w : Word A4 | countSet (lettersOfPhase 1) w % 3 = c.val} ∩
          {w : Word A4 | countSet (lettersOfPhase 2) w % 3 = 0}) ∪
      (({w : Word A4 | countSet (lettersOfPhase 1) w % 3 = (c.val + 1) % 3} ∩
          {w : Word A4 | countSet (lettersOfPhase 2) w % 3 = 1}) ∪
        ({w : Word A4 | countSet (lettersOfPhase 1) w % 3 = (c.val + 2) % 3} ∩
          {w : Word A4 | countSet (lettersOfPhase 2) w % 3 = 2})) := by
    ext w
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq,
      phaseSum_eq_weighted]
    have hc := c.isLt
    generalize countSet (lettersOfPhase 1) w = m
    generalize countSet (lettersOfPhase 2) w = n
    rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with hn | hn | hn <;>
      rcases (show m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 by omega) with hm | hm | hm <;>
      rcases (show c.val = 0 ∨ c.val = 1 ∨ c.val = 2 by omega) with hcv | hcv | hcv <;>
      omega
  rw [hset]
  refine hasHeightAtMost_union (hasHeightAtMost_inter ?_ ?_)
    (hasHeightAtMost_union (hasHeightAtMost_inter ?_ ?_)
      (hasHeightAtMost_inter ?_ ?_))
  · exact countMod3_hasHeightAtMost_one _ c
  · exact countMod3_hasHeightAtMost_one _ 0
  · exact countMod3_hasHeightAtMost_one _ ⟨(c.val + 1) % 3, by omega⟩
  · exact countMod3_hasHeightAtMost_one _ 1
  · exact countMod3_hasHeightAtMost_one _ ⟨(c.val + 2) % 3, by omega⟩
  · exact countMod3_hasHeightAtMost_one _ 2

/-! ## First-return token -/

/--
Star-free first-return token: one simple `C₃` cycle with fillers only on
intermediate phases (never a leading fill at the cut phase).
-/
def returnToken : GRegex A4 :=
  union A0
    (union (concat3 A1 fill A2)
      (union (concat3 A2 fill A1)
        (union
          (concat5 A1 fill A1 fill A1)
          (concat5 A2 fill A2 fill A2))))

theorem starHeight_returnToken : starHeight returnToken = 0 := by
  change
    max (starHeight A0)
      (max (starHeight (concat3 A1 fill A2))
        (max (starHeight (concat3 A2 fill A1))
          (max (starHeight (concat5 A1 fill A1 fill A1))
            (starHeight (concat5 A2 fill A2 fill A2))))) = 0
  simp only [starHeight_concat3, starHeight_concat5, starHeight,
    starHeight_A0, starHeight_A1, starHeight_A2, starHeight_fill]
  rfl

/-!
## Corrected first-return token (boundary-pair characterization)

The five shapes above are a **proper subset** of first-return (witness
`t·t·t²·t²`).  The correct star-free description, certified by
`scripts/research/a4_first_return_token.py` (exhaustive ≤ 13 + 200k random words):
a word is first-return at phase 0 iff it is a single phase-0 letter, or a
two-mover word `M1·fill·M2` / `M2·fill·M1`, or it has ≥ 3 movers, starts and
ends with a mover, its first and last adjacent-mover pairs are same-type,
and no same-type pair occurs strictly inside.
-/

def movers : GRegex A4 := union A1 A2

theorem starHeight_movers : starHeight movers = 0 := by
  change max (starHeight A1) (starHeight A2) = 0
  rw [starHeight_A1, starHeight_A2]; rfl

def anyLetter : GRegex A4 :=
  atomsOf (lettersOfPhase 0 ++ lettersOfPhase 1 ++ lettersOfPhase 2)

theorem starHeight_anyLetter : starHeight anyLetter = 0 := starHeight_atomsOf _

/-- `Σ⁺`: at least one letter. -/
def sigmaPlus : GRegex A4 := concat anyLetter univ

theorem starHeight_sigmaPlus : starHeight sigmaPlus = 0 := by
  change max (starHeight anyLetter) (starHeight univ) = 0
  rw [starHeight_anyLetter, starHeight_univ]; rfl

/-- Adjacent same-type mover pair (fills between). -/
def pairSame : GRegex A4 :=
  union (concat3 A1 fill A1) (concat3 A2 fill A2)

theorem starHeight_pairSame : starHeight pairSame = 0 := by
  change max (starHeight (concat3 A1 fill A1))
    (starHeight (concat3 A2 fill A2)) = 0
  simp only [starHeight_concat3, starHeight_A1, starHeight_A2, starHeight_fill]
  rfl

/-- At least three movers: `Σ* M Σ* M Σ* M Σ*`. -/
def threeMovers : GRegex A4 :=
  concat univ (concat movers
    (concat univ (concat movers (concat univ (concat movers univ)))))

theorem starHeight_threeMovers : starHeight threeMovers = 0 := by
  change max (starHeight univ) (max (starHeight movers)
    (max (starHeight univ) (max (starHeight movers)
      (max (starHeight univ) (max (starHeight movers)
        (starHeight univ)))))) = 0
  rw [starHeight_univ, starHeight_movers]; rfl

/-- ≥ 3-mover first-return words: start and end with a same-type pair, no
same-type pair strictly inside. -/
def frLong : GRegex A4 :=
  inter (concat pairSame univ)
    (inter (concat univ pairSame)
      (inter (compl (concat sigmaPlus (concat pairSame sigmaPlus)))
        threeMovers))

theorem starHeight_frLong : starHeight frLong = 0 := by
  have h1 : starHeight (concat pairSame univ) = 0 := by
    change max (starHeight pairSame) (starHeight univ) = 0
    rw [starHeight_pairSame, starHeight_univ]; rfl
  have h2 : starHeight (concat univ pairSame) = 0 := by
    change max (starHeight univ) (starHeight pairSame) = 0
    rw [starHeight_pairSame, starHeight_univ]; rfl
  have h3 : starHeight (compl (concat sigmaPlus (concat pairSame sigmaPlus))) = 0 := by
    change max (starHeight sigmaPlus)
      (max (starHeight pairSame) (starHeight sigmaPlus)) = 0
    rw [starHeight_pairSame, starHeight_sigmaPlus]; rfl
  simp only [frLong, starHeight_inter, h1, h2, h3, starHeight_threeMovers]
  rfl

/-- Corrected star-free first-return token at phase 0. -/
def frToken : GRegex A4 :=
  union A0
    (union (concat3 A1 fill A2)
      (union (concat3 A2 fill A1) frLong))

theorem starHeight_frToken : starHeight frToken = 0 := by
  change max (starHeight A0)
    (max (starHeight (concat3 A1 fill A2))
      (max (starHeight (concat3 A2 fill A1)) (starHeight frLong))) = 0
  simp only [starHeight_concat3, starHeight_A0, starHeight_A1, starHeight_A2,
    starHeight_fill, starHeight_frLong]
  rfl

def returnToken2 : GRegex A4 := concat frToken frToken

theorem starHeight_returnToken2 : starHeight returnToken2 = 0 := by
  change max (starHeight frToken) (starHeight frToken) = 0
  rw [starHeight_frToken]; rfl

def noReturn : GRegex A4 := compl (concat frToken univ)

theorem starHeight_noReturn : starHeight noReturn = 0 := by
  simpa [noReturn, starHeight, starHeight_univ] using starHeight_frToken

def evenReturns : GRegex A4 := concat (star returnToken2) noReturn

theorem starHeight_evenReturns : starHeight evenReturns ≤ 1 := by
  change max (starHeight returnToken2 + 1) (starHeight noReturn) ≤ 1
  rw [starHeight_returnToken2, starHeight_noReturn]
  decide

/-! ### Openers: first arrival at a nonzero phase

The former five-shape openers `union A1 (concat3 A2 fill A2)` (and its mirror)
were COMPUTED-incomplete: they miss `fill·A1`, `fill·A2·fill·A2`, and ≥3-mover
shapes such as `A2·A1·A1` (opener diagnosis in
`scripts/research/a4_first_return_token.py`).  They are replaced here by the
boundary-pair construction; the statement change is recorded under
`N-A4-FULL-034` in `PROOF_OBLIGATIONS.md`.

For `q ≠ 0`, a word avoids running phase `q` on every nonempty prefix exactly
when its movers alternate in type and the first mover does not have phase `q`
(the `C₃` walk on `{0, 3-q}` is deterministic).  `avoidP q` is that star-free
condition, and the first arrival at `q` is one letter past an avoiding word
while no longer avoiding. -/

/-- Single letters of a given phase. -/
def Aph (q : Fin 3) : GRegex A4 := atomsOf (lettersOfPhase q)

theorem starHeight_Aph (q : Fin 3) : starHeight (Aph q) = 0 := starHeight_atomsOf _

theorem mem_denote_Aph {q : Fin 3} {w : Word A4} :
    w ∈ denote (Aph q) ↔ ∃ g, phase g = q ∧ w = [g] := by
  simp only [Aph, denote_atomsOf]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, (mem_lettersOfPhase_iff g q).1 hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, (mem_lettersOfPhase_iff g q).2 hg, rfl⟩

/-- Star-free description of "no nonempty prefix reaches running phase `q`"
(for `q ≠ 0`). -/
def avoidP (q : Fin 3) : GRegex A4 :=
  inter (compl (concat univ (concat pairSame univ)))
    (compl (concat fill (concat (Aph q) univ)))

theorem starHeight_avoidP (q : Fin 3) : starHeight (avoidP q) = 0 := by
  change max (max (starHeight (univ : GRegex A4))
      (max (starHeight pairSame) (starHeight (univ : GRegex A4))))
    (max (starHeight fill)
      (max (starHeight (Aph q)) (starHeight (univ : GRegex A4)))) = 0
  rw [starHeight_univ, starHeight_pairSame, starHeight_fill, starHeight_Aph]
  rfl

/-- First arrival at phase `q`. -/
def opener (q : Fin 3) : GRegex A4 :=
  inter (concat (avoidP q) anyLetter) (compl (avoidP q))

theorem starHeight_opener (q : Fin 3) : starHeight (opener q) = 0 := by
  change max (max (starHeight (avoidP q)) (starHeight anyLetter))
    (starHeight (avoidP q)) = 0
  rw [starHeight_avoidP, starHeight_anyLetter]
  rfl

def opener1 : GRegex A4 := opener 1
def opener2 : GRegex A4 := opener 2

theorem starHeight_opener1 : starHeight opener1 = 0 := starHeight_opener 1

theorem starHeight_opener2 : starHeight opener2 = 0 := starHeight_opener 2

def noLand (O : GRegex A4) : GRegex A4 := compl (concat O univ)

theorem starHeight_noLand (O : GRegex A4) (h : starHeight O = 0) :
    starHeight (noLand O) = 0 := by
  simp [noLand, starHeight, h]

def oddReturnsAfter (O : GRegex A4) : GRegex A4 :=
  concat O (concat frToken evenReturns)

theorem starHeight_oddReturnsAfter (O : GRegex A4) (h : starHeight O = 0) :
    starHeight (oddReturnsAfter O) ≤ 1 := by
  have he := starHeight_evenReturns
  have hr := starHeight_frToken
  change max (starHeight O)
      (max (starHeight frToken) (starHeight evenReturns)) ≤ 1
  rw [h, hr]
  exact max_le (by decide) (max_le (by decide) he)

def evenLandings0 : GRegex A4 := evenReturns
def evenLandings1 : GRegex A4 := union (noLand opener1) (oddReturnsAfter opener1)
def evenLandings2 : GRegex A4 := union (noLand opener2) (oddReturnsAfter opener2)

theorem starHeight_evenLandings0 : starHeight evenLandings0 ≤ 1 := starHeight_evenReturns

theorem starHeight_evenLandings1 : starHeight evenLandings1 ≤ 1 := by
  have h1 := starHeight_noLand opener1 starHeight_opener1
  have h2 := starHeight_oddReturnsAfter opener1 starHeight_opener1
  change max (starHeight (noLand opener1)) (starHeight (oddReturnsAfter opener1)) ≤ 1
  rw [h1]; exact max_le (by decide) h2

theorem starHeight_evenLandings2 : starHeight evenLandings2 ≤ 1 := by
  have h1 := starHeight_noLand opener2 starHeight_opener2
  have h2 := starHeight_oddReturnsAfter opener2 starHeight_opener2
  change max (starHeight (noLand opener2)) (starHeight (oddReturnsAfter opener2)) ≤ 1
  rw [h1]; exact max_le (by decide) h2

def evenLandings : Fin 3 → GRegex A4
  | ⟨0, _⟩ => evenLandings0
  | ⟨1, _⟩ => evenLandings1
  | ⟨2, _⟩ => evenLandings2

theorem starHeight_evenLandings (q : Fin 3) : starHeight (evenLandings q) ≤ 1 := by
  match q with
  | ⟨0, _⟩ => exact starHeight_evenLandings0
  | ⟨1, _⟩ => exact starHeight_evenLandings1
  | ⟨2, _⟩ => exact starHeight_evenLandings2

def landingParity (q : Fin 3) : Language A4 :=
  {w | landingCount q w 0 % 2 = 0}

/-! ## First-return semantics at phase 0

A landing on phase 0 starting from 0 occurs exactly when a nonempty prefix
has `phaseSum ≡ 0 (mod 3)`.  First-return tokens are the nonempty words whose
*only* such prefix is the whole word.
-/

def IsReturn0 (w : Word A4) : Prop :=
  w ≠ [] ∧
    phaseSum w % 3 = 0 ∧
      ∀ k : Nat, 0 < k → k < w.length → phaseSum (w.take k) % 3 ≠ 0

/-- No landing on `q` (from start phase `p`) iff no positive-length prefix
brings the running phase to `q`.  Direct induction (avoids the buggy
five-shape counting route); the blueprint's `landingCount0_eq_zero_prefix_count`
had an off-by-one (`range w.length` dropped the terminal landing), so
`N-A4-FULL-037` is discharged through this equivalent characterization. -/
theorem landingCount_eq_zero_iff (q : Fin 3) :
    ∀ (w : Word A4) (p : Nat),
      landingCount q w p = 0 ↔
        ∀ k : Nat, k < w.length →
          (p + phaseSum (w.take (k + 1))) % 3 ≠ q.val
  | [], _ => by
    constructor
    · intro _ k hk; exact absurd hk (by simp)
    · intro _; rfl
  | g :: w, p => by
    have ih := landingCount_eq_zero_iff q w (p + (phase g).val)
    rw [landingCount_cons]
    constructor
    · intro hz
      by_cases hc : (p + (phase g).val) % 3 = q.val
      · rw [if_pos hc] at hz; exact absurd hz (by omega)
      · rw [if_neg hc, Nat.zero_add] at hz
        have htail := ih.1 hz
        intro k hk
        cases k with
        | zero =>
          have he : (g :: w).take (0 + 1) = [g] := rfl
          rw [he]; simpa [phaseSum_cons, phaseSum] using hc
        | succ k =>
          have hk' : k < w.length := by
            simp only [List.length_cons] at hk; omega
          have hthis := htail k hk'
          have he : (g :: w).take (k + 1 + 1) = g :: w.take (k + 1) := rfl
          rw [he, phaseSum_cons, ← Nat.add_assoc]
          exact hthis
    · intro h
      have hc : (p + (phase g).val) % 3 ≠ q.val := by
        have h0 := h 0 (by simp)
        have he : (g :: w).take (0 + 1) = [g] := rfl
        rw [he] at h0
        simpa [phaseSum_cons, phaseSum] using h0
      have htail : landingCount q w (p + (phase g).val) = 0 := by
        rw [ih]
        intro k hk
        have hthis := h (k + 1) (by simp only [List.length_cons]; omega)
        have he : (g :: w).take (k + 1 + 1) = g :: w.take (k + 1) := rfl
        rw [he, phaseSum_cons, ← Nat.add_assoc] at hthis
        exact hthis
      rw [if_neg hc, htail]

/-- No landing on 0 (start 0) iff no positive-length prefix hits phase 0. -/
theorem landingCount0_eq_zero_iff (w : Word A4) :
    landingCount 0 w 0 = 0 ↔
      ∀ k : Nat, k < w.length → phaseSum (w.take (k + 1)) % 3 ≠ 0 := by
  have h := landingCount_eq_zero_iff 0 w 0
  simpa using h

-- BLUEPRINT: N-A4-FULL-037
theorem isReturn0_iff_landingCount (w : Word A4) :
    IsReturn0 w ↔
      w ≠ [] ∧ landingCount 0 w 0 = 1 ∧
        ∀ k : Nat, 0 < k → k < w.length → landingCount 0 (w.take k) 0 = 0 := by
  constructor
  · rintro ⟨hne, hsum, hint⟩
    refine ⟨hne, ?_, ?_⟩
    · -- write w = init ++ [last]; interior prefixes never land, last does
      obtain ⟨init, last, hw⟩ : ∃ init last, w = init ++ [last] := by
        rcases List.eq_nil_or_concat w with h | ⟨init, last, h⟩
        · exact absurd h hne
        · exact ⟨init, last, by rw [List.concat_eq_append] at h; exact h⟩
      have hlen : w.length = init.length + 1 := by rw [hw]; simp
      rw [hw, landingCount_append]
      have hinit0 : landingCount 0 init 0 = 0 := by
        rw [landingCount0_eq_zero_iff]
        intro k hk
        have hpr : init.take (k + 1) = w.take (k + 1) := by
          rw [hw, List.take_append_of_le_length (by omega)]
        rw [hpr]
        exact hint (k + 1) (by omega) (by omega)
      have hcond : (0 + phaseSum init + (phase last).val) % 3 = (0 : Fin 3).val := by
        have hh : phaseSum w % 3 = 0 := hsum
        rw [hw, phaseSum_append] at hh
        have hlast : phaseSum ([last] : Word A4) = (phase last).val := by
          simp [phaseSum_cons, phaseSum]
        rw [hlast] at hh
        simpa [Nat.zero_add] using hh
      rw [hinit0, Nat.zero_add, landingCount_cons, landingCount_nil,
        Nat.add_zero, if_pos hcond]
    · intro k hk hlt
      rw [landingCount0_eq_zero_iff]
      intro j hj
      have hjk : (w.take k).length = k := by
        rw [List.length_take]; omega
      rw [hjk] at hj
      rw [List.take_take]
      rw [show min (j + 1) k = j + 1 from by omega]
      exact hint (j + 1) (by omega) (by omega)
  · rintro ⟨hne, h1, hint⟩
    refine ⟨hne, ?_, ?_⟩
    · -- terminal landing: phaseSum w ≡ 0
      by_contra hsum
      have hnl : landingCount 0 w 0 = 0 := by
        rw [landingCount0_eq_zero_iff]
        intro k hk
        rcases Nat.lt_or_ge (k + 1) w.length with hklt | hkge
        · have hz := hint (k + 1) (by omega) hklt
          rw [landingCount0_eq_zero_iff] at hz
          have hjj := hz k (by rw [List.length_take]; omega)
          rw [List.take_take, show min (k + 1) (k + 1) = k + 1 from by omega]
            at hjj
          exact hjj
        · have hke : k + 1 = w.length := by omega
          rw [hke, List.take_length]
          exact hsum
      rw [hnl] at h1; exact absurd h1 (by decide)
    · intro k hk hlt
      have hz := hint k hk hlt
      rw [landingCount0_eq_zero_iff] at hz
      have hjj := hz (k - 1) (by rw [List.length_take]; omega)
      rw [List.take_take, show min (k - 1 + 1) k = k from by omega] at hjj
      exact hjj

theorem isReturn0_A0 {g : A4} (hg : phase g = 0) : IsReturn0 [g] := by
  refine ⟨by simp, ?_, ?_⟩
  · simp [phaseSum_cons, phaseSum, hg]
  · intro k hk hlt
    simp at hlt; omega

theorem phaseSum_take_of_fill_prefix {g : A4} {f : Word A4} {k : Nat}
    (hg : phase g = 1 ∨ phase g = 2) (hf : f ∈ denote fill)
    (hk : 0 < k) (hk' : k ≤ f.length + 1) :
    phaseSum ((g :: f).take k) % 3 ≠ 0 := by
  have hs := phaseSum_of_mem_fill hf
  cases k with
  | zero => exact absurd hk (Nat.not_lt_zero _)
  | succ k =>
    cases k with
    | zero =>
      simp only [take, phaseSum_cons, phaseSum]
      rcases hg with hg | hg <;> simp [hg]
    | succ k =>
      have hk'' : k + 1 ≤ f.length := by omega
      simp only [take]
      have hft : phaseSum (f.take (k + 1)) = 0 := by
        apply phaseSum_of_mem_fill
        rw [denote_fill] at hf ⊢
        intro x hx
        exact hf x (List.mem_of_mem_take hx)
      simp only [phaseSum_cons, hft, Nat.add_zero]
      rcases hg with hg | hg <;> simp [hg]

theorem isReturn0_A1_fill_A2 {g₁ g₂ : A4} {f : Word A4}
    (h1 : phase g₁ = 1) (h2 : phase g₂ = 2) (hf : f ∈ denote fill) :
    IsReturn0 ([g₁] ++ f ++ [g₂]) := by
  have hs := phaseSum_of_mem_fill hf
  refine ⟨by simp, ?_, ?_⟩
  · change (List.map (fun g => (phase g).val) ([g₁] ++ f ++ [g₂])).sum % 3 = 0
    simp [h1, h2, show (f.map (fun g => (phase g).val)).sum = 0 from hs]
  · intro k hk hlt
    have hlen : ([g₁] ++ f ++ [g₂]).length = f.length + 2 := by
      simp [length_append]
    rw [hlen] at hlt
    have hk' : k ≤ f.length + 1 := by omega
    have hpref : (([g₁] ++ f ++ [g₂]).take k) = (g₁ :: f).take k := by
      change take k ((([g₁] ++ f) ++ [g₂])) = take k (g₁ :: f)
      have : [g₁] ++ f = g₁ :: f := rfl
      rw [this]
      exact take_append_of_le_length (by simp [hk'])
    rw [hpref]
    exact phaseSum_take_of_fill_prefix (Or.inl h1) hf hk hk'

theorem isReturn0_A2_fill_A1 {g₁ g₂ : A4} {f : Word A4}
    (h2 : phase g₁ = 2) (h1 : phase g₂ = 1) (hf : f ∈ denote fill) :
    IsReturn0 ([g₁] ++ f ++ [g₂]) := by
  have hs := phaseSum_of_mem_fill hf
  refine ⟨by simp, ?_, ?_⟩
  · change (List.map (fun g => (phase g).val) ([g₁] ++ f ++ [g₂])).sum % 3 = 0
    simp [h1, h2, show (f.map (fun g => (phase g).val)).sum = 0 from hs]
  · intro k hk hlt
    have hlen : ([g₁] ++ f ++ [g₂]).length = f.length + 2 := by
      simp [length_append]
    rw [hlen] at hlt
    have hk' : k ≤ f.length + 1 := by omega
    have hpref : (([g₁] ++ f ++ [g₂]).take k) = (g₁ :: f).take k := by
      change take k ((([g₁] ++ f) ++ [g₂])) = take k (g₁ :: f)
      have : [g₁] ++ f = g₁ :: f := rfl
      rw [this]
      exact take_append_of_le_length (by simp [hk'])
    rw [hpref]
    exact phaseSum_take_of_fill_prefix (Or.inr h2) hf hk hk'

theorem isReturn0_A1_thrice {g₁ g₂ g₃ : A4} {f₁ f₂ : Word A4}
    (h1 : phase g₁ = 1) (h2 : phase g₂ = 1) (h3 : phase g₃ = 1)
    (hf1 : f₁ ∈ denote fill) (hf2 : f₂ ∈ denote fill) :
    IsReturn0 ([g₁] ++ f₁ ++ [g₂] ++ f₂ ++ [g₃]) := by
  have hs1 := phaseSum_of_mem_fill hf1
  have hs2 := phaseSum_of_mem_fill hf2
  set w : Word A4 := [g₁] ++ f₁ ++ [g₂] ++ f₂ ++ [g₃]
  refine ⟨by simp [w], ?_, ?_⟩
  · change (List.map (fun g => (phase g).val) w).sum % 3 = 0
    simp [w, h1, h2, h3,
      show (f₁.map (fun g => (phase g).val)).sum = 0 from hs1,
      show (f₂.map (fun g => (phase g).val)).sum = 0 from hs2]
  · intro k hk hlt
    have hlen : w.length = f₁.length + f₂.length + 3 := by
      simp [w, length_append, length_cons]; try omega
    rw [hlen] at hlt
    have hk' : k ≤ f₁.length + f₂.length + 2 := by omega
    by_cases hreg : k ≤ f₁.length + 1
    · have hw' : w = (g₁ :: f₁) ++ ([g₂] ++ f₂ ++ [g₃]) := by simp [w]
      have hpref : w.take k = (g₁ :: f₁).take k := by
        rw [hw']; exact take_append_of_le_length (by simp [hreg])
      rw [hpref]
      exact phaseSum_take_of_fill_prefix (Or.inl h1) hf1 hk hreg
    · push Not at hreg
      set mid : Word A4 := (g₁ :: f₁) ++ [g₂] ++ f₂
      have hmid_len : mid.length = f₁.length + f₂.length + 2 := by
        simp [mid, length_append, length_cons]; try omega
      have hw' : w = mid ++ [g₃] := by simp [w, mid]
      have hpref : w.take k = mid.take k := by
        rw [hw']; exact take_append_of_le_length (by omega)
      rw [hpref]
      set u : Word A4 := (g₁ :: f₁) ++ [g₂]
      have hu_len : u.length = f₁.length + 2 := by
        simp [u, length_append, length_cons]
      have hulen : u.length ≤ k := by omega
      have hmid_u : mid = u ++ f₂ := by simp [mid, u]
      have htake : mid.take k = u ++ f₂.take (k - u.length) := by
        rw [hmid_u]; exact take_append_of_length_le u f₂ hulen
      rw [htake, phaseSum_append]
      have hu : phaseSum u = 2 := by
        simp only [u]
        rw [phaseSum_append, phaseSum_cons, h1, hs1]
        simp [phaseSum, h2]
      have hf : phaseSum (f₂.take (k - u.length)) = 0 := phaseSum_take_fill hf2 _
      simp [hu, hf]

theorem isReturn0_A2_thrice {g₁ g₂ g₃ : A4} {f₁ f₂ : Word A4}
    (h1 : phase g₁ = 2) (h2 : phase g₂ = 2) (h3 : phase g₃ = 2)
    (hf1 : f₁ ∈ denote fill) (hf2 : f₂ ∈ denote fill) :
    IsReturn0 ([g₁] ++ f₁ ++ [g₂] ++ f₂ ++ [g₃]) := by
  have hs1 := phaseSum_of_mem_fill hf1
  have hs2 := phaseSum_of_mem_fill hf2
  set w : Word A4 := [g₁] ++ f₁ ++ [g₂] ++ f₂ ++ [g₃]
  refine ⟨by simp [w], ?_, ?_⟩
  · change (List.map (fun g => (phase g).val) w).sum % 3 = 0
    simp [w, h1, h2, h3,
      show (f₁.map (fun g => (phase g).val)).sum = 0 from hs1,
      show (f₂.map (fun g => (phase g).val)).sum = 0 from hs2]
  · intro k hk hlt
    have hlen : w.length = f₁.length + f₂.length + 3 := by
      simp [w, length_append, length_cons]; try omega
    rw [hlen] at hlt
    have hk' : k ≤ f₁.length + f₂.length + 2 := by omega
    by_cases hreg : k ≤ f₁.length + 1
    · have hw' : w = (g₁ :: f₁) ++ ([g₂] ++ f₂ ++ [g₃]) := by simp [w]
      have hpref : w.take k = (g₁ :: f₁).take k := by
        rw [hw']; exact take_append_of_le_length (by simp [hreg])
      rw [hpref]
      exact phaseSum_take_of_fill_prefix (Or.inr h1) hf1 hk hreg
    · push Not at hreg
      set mid : Word A4 := (g₁ :: f₁) ++ [g₂] ++ f₂
      have hmid_len : mid.length = f₁.length + f₂.length + 2 := by
        simp [mid, length_append, length_cons]; try omega
      have hw' : w = mid ++ [g₃] := by simp [w, mid]
      have hpref : w.take k = mid.take k := by
        rw [hw']; exact take_append_of_le_length (by omega)
      rw [hpref]
      set u : Word A4 := (g₁ :: f₁) ++ [g₂]
      have hu_len : u.length = f₁.length + 2 := by
        simp [u, length_append, length_cons]
      have hulen : u.length ≤ k := by omega
      have hmid_u : mid = u ++ f₂ := by simp [mid, u]
      have htake : mid.take k = u ++ f₂.take (k - u.length) := by
        rw [hmid_u]; exact take_append_of_length_le u f₂ hulen
      rw [htake, phaseSum_append]
      have hu : phaseSum u = 4 := by
        simp only [u]
        rw [phaseSum_append, phaseSum_cons, h1, hs1]
        simp [phaseSum, h2]
      have hf : phaseSum (f₂.take (k - u.length)) = 0 := phaseSum_take_fill hf2 _
      simp [hu, hf]

/-- Split at the first non-fill letter, if any exist. -/
theorem exists_first_nonfill {w : Word A4}
    (hne : ¬∀ g ∈ w, phase g = 0) :
    ∃ f g rest, w = f ++ g :: rest ∧ (∀ x ∈ f, phase x = 0) ∧ phase g ≠ 0 := by
  induction w with
  | nil =>
    exact absurd (by intro _ h; cases h) hne
  | cons a as ih =>
    by_cases ha : phase a = 0
    · by_cases has : ∀ g ∈ as, phase g = 0
      · exact absurd (by
          intro g hg
          simp only [mem_cons] at hg
          rcases hg with rfl | hg
          · exact ha
          · exact has g hg) hne
      · rcases ih has with ⟨f, g, rest, rfl, hf, hg⟩
        refine ⟨a :: f, g, rest, ?_, ?_, hg⟩
        · simp
        · intro x hx
          simp only [mem_cons] at hx
          rcases hx with rfl | hx
          · exact ha
          · exact hf x hx
    · exact ⟨[], a, as, rfl, ⟨(by intro x hx; cases hx), ha⟩⟩

theorem isReturn0_of_length_one {g : A4} (hw : IsReturn0 [g]) : phase g = 0 := by
  have h := hw.2.1
  simp [phaseSum] at h
  have : (phase g).val < 3 := (phase g).isLt
  omega

theorem isReturn0_first_phase_ne_zero {g : A4} {rest : Word A4}
    (hw : IsReturn0 (g :: rest)) (hne : rest ≠ []) :
    phase g = 1 ∨ phase g = 2 := by
  have hlt : 1 < (g :: rest).length := by
    cases rest with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have h := hw.2.2 1 (by omega) hlt
  simp [phaseSum] at h
  match hph : phase g with
  | ⟨0, _⟩ => simp [hph] at h
  | ⟨1, _⟩ => exact Or.inl rfl
  | ⟨2, _⟩ => exact Or.inr rfl

theorem mem_denote_concat3 {r s t : GRegex A4} {w : Word A4} :
    w ∈ denote (concat3 r s t) ↔
      ∃ u v x, w = u ++ v ++ x ∧ u ∈ denote r ∧ v ∈ denote s ∧ x ∈ denote t := by
  simp only [concat3, denote, mem_concat_iff]
  constructor
  · rintro ⟨u, hu, rest, ⟨v, hv, x, hx, rfl⟩, rfl⟩
    exact ⟨u, v, x, by simp, hu, hv, hx⟩
  · rintro ⟨u, v, x, rfl, hu, hv, hx⟩
    exact ⟨u, hu, v ++ x, ⟨v, hv, x, hx, rfl⟩, by simp⟩

theorem mem_denote_concat5 {r₁ r₂ r₃ r₄ r₅ : GRegex A4} {w : Word A4} :
    w ∈ denote (concat5 r₁ r₂ r₃ r₄ r₅) ↔
      ∃ a b c d e, w = a ++ b ++ c ++ d ++ e ∧
        a ∈ denote r₁ ∧ b ∈ denote r₂ ∧ c ∈ denote r₃ ∧
        d ∈ denote r₄ ∧ e ∈ denote r₅ := by
  simp only [concat5, denote, mem_concat_iff]
  constructor
  · rintro ⟨a, ha, w₂, ⟨b, hb, w₃, ⟨c, hc, w₄, ⟨d, hd, e, he, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, b, c, d, e, by simp, ha, hb, hc, hd, he⟩
  · rintro ⟨a, b, c, d, e, rfl, ha, hb, hc, hd, he⟩
    exact ⟨a, ha, b ++ c ++ d ++ e,
      ⟨b, hb, c ++ d ++ e, ⟨c, hc, d ++ e, ⟨d, hd, e, he, rfl⟩, by simp⟩, by simp⟩, by simp⟩

/-! ### `pairSame` membership -/

theorem mem_denote_pairSame {m₁ m₂ : A4} {f : Word A4}
    (h₁ : phase m₁ ≠ 0) (hsame : phase m₂ = phase m₁)
    (hf : ∀ x ∈ f, phase x = 0) :
    ([m₁] ++ f ++ [m₂]) ∈ denote pairSame := by
  have hfill : f ∈ denote fill := by rw [denote_fill]; exact hf
  have hlt := (phase m₁).isLt
  have hne : (phase m₁).val ≠ 0 := fun hh => h₁ (Fin.ext hh)
  have h12 : phase m₁ = 1 ∨ phase m₁ = 2 := by
    rcases (by omega : (phase m₁).val = 1 ∨ (phase m₁).val = 2) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases h12 with h | h
  · refine Or.inl (mem_denote_concat3.2 ⟨[m₁], f, [m₂], rfl, ?_, hfill, ?_⟩)
    · exact mem_denote_A1.2 ⟨m₁, h, rfl⟩
    · exact mem_denote_A1.2 ⟨m₂, by rw [hsame, h], rfl⟩
  · refine Or.inr (mem_denote_concat3.2 ⟨[m₁], f, [m₂], rfl, ?_, hfill, ?_⟩)
    · exact mem_denote_A2.2 ⟨m₁, h, rfl⟩
    · exact mem_denote_A2.2 ⟨m₂, by rw [hsame, h], rfl⟩

theorem of_mem_pairSame {w : Word A4} (hw : w ∈ denote pairSame) :
    ∃ a f b, w = [a] ++ f ++ [b] ∧ phase a ≠ 0 ∧ phase b = phase a ∧
      ∀ x ∈ f, phase x = 0 := by
  rcases hw with h | h
  · obtain ⟨u, v, x, rfl, hu, hv, hx⟩ := mem_denote_concat3.1 h
    obtain ⟨a, ha, rfl⟩ := mem_denote_A1.1 hu
    obtain ⟨b, hb, rfl⟩ := mem_denote_A1.1 hx
    exact ⟨a, v, b, rfl, by rw [ha]; decide, by rw [ha, hb],
      by rw [denote_fill] at hv; exact hv⟩
  · obtain ⟨u, v, x, rfl, hu, hv, hx⟩ := mem_denote_concat3.1 h
    obtain ⟨a, ha, rfl⟩ := mem_denote_A2.1 hu
    obtain ⟨b, hb, rfl⟩ := mem_denote_A2.1 hx
    exact ⟨a, v, b, rfl, by rw [ha]; decide, by rw [ha, hb],
      by rw [denote_fill] at hv; exact hv⟩

/-- The five-shape token language is contained in first-return. -/
theorem isReturn0_of_mem_returnToken {w : Word A4}
    (hw : w ∈ denote returnToken) : IsReturn0 w := by
  simp only [returnToken, denote, Set.mem_union] at hw
  rcases hw with h | hw
  · obtain ⟨g, hg, rfl⟩ := mem_denote_A0.1 h
    exact isReturn0_A0 hg
  rcases hw with h | hw
  · obtain ⟨u, v, x, rfl, hu, hv, hx⟩ := mem_denote_concat3.1 h
    obtain ⟨g₁, h1, rfl⟩ := mem_denote_A1.1 hu
    obtain ⟨g₂, h2, rfl⟩ := mem_denote_A2.1 hx
    exact isReturn0_A1_fill_A2 h1 h2 hv
  rcases hw with h | hw
  · obtain ⟨u, v, x, rfl, hu, hv, hx⟩ := mem_denote_concat3.1 h
    obtain ⟨g₁, h1, rfl⟩ := mem_denote_A2.1 hu
    obtain ⟨g₂, h2, rfl⟩ := mem_denote_A1.1 hx
    exact isReturn0_A2_fill_A1 h1 h2 hv
  rcases hw with h | h
  · obtain ⟨a, b, c, d, e, rfl, ha, hb, hc, hd, he⟩ := mem_denote_concat5.1 h
    obtain ⟨g₁, h1, rfl⟩ := mem_denote_A1.1 ha
    obtain ⟨g₂, h2, rfl⟩ := mem_denote_A1.1 hc
    obtain ⟨g₃, h3, rfl⟩ := mem_denote_A1.1 he
    exact isReturn0_A1_thrice h1 h2 h3 hb hd
  · obtain ⟨a, b, c, d, e, rfl, ha, hb, hc, hd, he⟩ := mem_denote_concat5.1 h
    obtain ⟨g₁, h1, rfl⟩ := mem_denote_A2.1 ha
    obtain ⟨g₂, h2, rfl⟩ := mem_denote_A2.1 hc
    obtain ⟨g₃, h3, rfl⟩ := mem_denote_A2.1 he
    exact isReturn0_A2_thrice h1 h2 h3 hb hd

/--
Counterexample: mover phases `1,1,2,2` is first-return but not a five-shape token.
-/
theorem isReturn0_four_movers_1122 :
    IsReturn0 [t, t, t ^ 2, t ^ 2] := by
  have h1 : phase t = 1 := phase_t
  have h2 : phase (t ^ 2) = 2 := phase_t_sq
  refine ⟨by simp, ?_, ?_⟩
  · simp [phaseSum, h1, h2]
  · intro k hk hlt
    simp at hlt
    interval_cases k <;> simp [phaseSum, h1, h2]

theorem fill_eq_nil_of_no_phase_zero {v : Word A4}
    (hv : v ∈ denote fill) (h : ∀ g ∈ v, phase g ≠ 0) : v = [] := by
  rw [denote_fill] at hv
  match v with
  | [] => rfl
  | g :: _ => exact (h g (by simp) (hv g (by simp))).elim

theorem returnToken_all_movers_length_le_three {w : Word A4}
    (hw : w ∈ denote returnToken) (hmov : ∀ g ∈ w, phase g ≠ 0) :
    w.length ≤ 3 := by
  simp only [returnToken, denote, Set.mem_union] at hw
  rcases hw with h | hw
  · obtain ⟨g, _, rfl⟩ := mem_denote_A0.1 h; simp
  rcases hw with h | hw
  · obtain ⟨u, v, x, rfl, hu, hv, hx⟩ := mem_denote_concat3.1 h
    obtain ⟨g₁, _, rfl⟩ := mem_denote_A1.1 hu
    obtain ⟨g₂, _, rfl⟩ := mem_denote_A2.1 hx
    have hvnil := fill_eq_nil_of_no_phase_zero hv fun g hg =>
      hmov g (by simp [hg])
    simp [hvnil]
  rcases hw with h | hw
  · obtain ⟨u, v, x, rfl, hu, hv, hx⟩ := mem_denote_concat3.1 h
    obtain ⟨g₁, _, rfl⟩ := mem_denote_A2.1 hu
    obtain ⟨g₂, _, rfl⟩ := mem_denote_A1.1 hx
    have hvnil := fill_eq_nil_of_no_phase_zero hv fun g hg =>
      hmov g (by simp [hg])
    simp [hvnil]
  rcases hw with h | h
  · obtain ⟨a, b, c, d, e, rfl, ha, hb, hc, hd, he⟩ := mem_denote_concat5.1 h
    obtain ⟨g₁, _, rfl⟩ := mem_denote_A1.1 ha
    obtain ⟨g₂, _, rfl⟩ := mem_denote_A1.1 hc
    obtain ⟨g₃, _, rfl⟩ := mem_denote_A1.1 he
    have hbnil := fill_eq_nil_of_no_phase_zero hb fun g hg =>
      hmov g (by simp [hg])
    have hdnil := fill_eq_nil_of_no_phase_zero hd fun g hg =>
      hmov g (by simp [hg])
    simp [hbnil, hdnil]
  · obtain ⟨a, b, c, d, e, rfl, ha, hb, hc, hd, he⟩ := mem_denote_concat5.1 h
    obtain ⟨g₁, _, rfl⟩ := mem_denote_A2.1 ha
    obtain ⟨g₂, _, rfl⟩ := mem_denote_A2.1 hc
    obtain ⟨g₃, _, rfl⟩ := mem_denote_A2.1 he
    have hbnil := fill_eq_nil_of_no_phase_zero hb fun g hg =>
      hmov g (by simp [hg])
    have hdnil := fill_eq_nil_of_no_phase_zero hd fun g hg =>
      hmov g (by simp [hg])
    simp [hbnil, hdnil]

theorem not_mem_returnToken_four_movers_1122 :
    [t, t, t ^ 2, t ^ 2] ∉ denote returnToken := by
  intro hw
  have h1 : phase t = 1 := phase_t
  have h2 : phase (t ^ 2) = 2 := phase_t_sq
  have hmov : ∀ g ∈ ([t, t, t ^ 2, t ^ 2] : Word A4), phase g ≠ 0 := by
    intro g hg
    simp only [mem_cons, not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp [h1, h2]
  have hle := returnToken_all_movers_length_le_three hw hmov
  simp at hle

/-!
The corrected token `frToken` uses the boundary-pair characterization of
first-return (certified in `scripts/research/a4_first_return_token.py`).  The refuted
five-shape equivalence is recorded at `N-A4-FULL-035`
(`isReturn0_four_movers_1122`, `not_mem_returnToken_four_movers_1122`).
-/

/-! ### Mover-count infrastructure (backward classification) -/

/-- A letter is a *mover* if it changes the running phase. -/
def isMover (g : A4) : Bool := decide (phase g ≠ 0)

/-- Number of movers (phase ≠ 0 letters) in a word. -/
def moverCount (w : Word A4) : Nat := (w.filter isMover).length

theorem moverCount_nil : moverCount [] = 0 := rfl

theorem moverCount_cons (g : A4) (w : Word A4) :
    moverCount (g :: w) =
      (if phase g = 0 then moverCount w else moverCount w + 1) := by
  by_cases h : phase g = 0
  · simp [moverCount, List.filter_cons, isMover, h]
  · simp [moverCount, List.filter_cons, isMover, h]

theorem moverCount_append (u v : Word A4) :
    moverCount (u ++ v) = moverCount u + moverCount v := by
  simp [moverCount, List.filter_append]

theorem moverCount_eq_zero_iff (w : Word A4) :
    moverCount w = 0 ↔ ∀ g ∈ w, phase g = 0 := by
  unfold moverCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  constructor
  · intro h g hg
    have hh := h g hg
    simp only [isMover, decide_eq_true_eq, not_not] at hh
    exact hh
  · intro h g hg
    simp only [isMover, decide_eq_true_eq, not_not]
    exact h g hg

/-- A word with exactly one mover splits as `fillers · [mover] · fillers`. -/
theorem exists_one_mover_split {u : Word A4} (h : moverCount u = 1) :
    ∃ f1 g f2, u = f1 ++ [g] ++ f2 ∧ (∀ x ∈ f1, phase x = 0) ∧
      phase g ≠ 0 ∧ (∀ x ∈ f2, phase x = 0) := by
  have hnf : ¬ ∀ g ∈ u, phase g = 0 := by
    rw [← moverCount_eq_zero_iff]; omega
  obtain ⟨f1, g, rest, rfl, hf1, hg⟩ := exists_first_nonfill hnf
  have hf1z : moverCount f1 = 0 := (moverCount_eq_zero_iff f1).2 hf1
  rw [moverCount_append, hf1z, Nat.zero_add, moverCount_cons, if_neg hg] at h
  have hrest : moverCount rest = 0 := by omega
  have hf2 : ∀ x ∈ rest, phase x = 0 := (moverCount_eq_zero_iff rest).1 hrest
  exact ⟨f1, g, rest, by simp, hf1, hg, hf2⟩

/-- A first-return word with a mover cannot end with a filler: the prefix up to
the last mover would itself land on phase 0. -/
theorem isReturn0_last_phase_ne_zero {init : Word A4} {g : A4}
    (hw : IsReturn0 (init ++ [g])) (hne : init ≠ []) :
    phase g = 1 ∨ phase g = 2 := by
  by_contra hc
  push_neg at hc
  obtain ⟨hc1, hc2⟩ := hc
  have hg0 : phase g = 0 := by
    match h : phase g with
    | 0 => rfl
    | 1 => exact absurd h hc1
    | 2 => exact absurd h hc2
  have hsumw : phaseSum (init ++ [g]) % 3 = 0 := hw.2.1
  rw [phaseSum_append] at hsumw
  have hlast : phaseSum ([g] : Word A4) = (phase g).val := by
    simp [phaseSum_cons, phaseSum]
  rw [hlast, hg0] at hsumw
  simp only [Fin.val_zero, Nat.add_zero] at hsumw
  have hlen : (init ++ [g]).length = init.length + 1 := by simp
  have hk : 0 < init.length := List.length_pos_of_ne_nil hne
  have hklt : init.length < (init ++ [g]).length := by rw [hlen]; omega
  have hint := hw.2.2 init.length hk hklt
  have htake : (init ++ [g]).take init.length = init := by
    rw [take_append_of_length_le init [g] (le_refl _)]; simp
  rw [htake] at hint
  exact hint hsumw

/-- A first-return word all of whose letters are fillers is a single letter. -/
theorem isReturn0_no_mover_eq_single {w : Word A4}
    (hw : IsReturn0 w) (hmov : ∀ g ∈ w, phase g = 0) :
    ∃ g, phase g = 0 ∧ w = [g] := by
  cases w with
  | nil => exact absurd rfl hw.1
  | cons g rest =>
    cases rest with
    | nil => exact ⟨g, hmov g (by simp), rfl⟩
    | cons g2 rest2 =>
      have hne : (g2 :: rest2) ≠ [] := by simp
      have hph := isReturn0_first_phase_ne_zero hw hne
      have h0 := hmov g (by simp)
      rcases hph with h | h <;> rw [h0] at h <;> exact absurd h (by decide)

/-! ### The mover subword

`movs w` is the subsequence of movers.  Fillers contribute nothing to
`phaseSum`, so the whole first-return analysis of `frLong` can be carried out
on `movs w`, where the boundary-pair conditions become conditions on a list of
phases in `{1,2}`. -/

/-- The subword of `w` consisting of its movers. -/
def movs (w : Word A4) : Word A4 := w.filter isMover

@[simp] theorem movs_nil : movs [] = [] := rfl

theorem length_movs (w : Word A4) : (movs w).length = moverCount w := rfl

theorem movs_append (u v : Word A4) : movs (u ++ v) = movs u ++ movs v := by
  simp [movs, List.filter_append]

theorem movs_cons_mover {g : A4} (hg : phase g ≠ 0) (w : Word A4) :
    movs (g :: w) = g :: movs w := by
  simp [movs, isMover, hg]

theorem movs_cons_fill {g : A4} (hg : phase g = 0) (w : Word A4) :
    movs (g :: w) = movs w := by
  simp [movs, isMover, hg]

theorem movs_singleton_mover {m : A4} (h : phase m ≠ 0) : movs [m] = [m] := by
  rw [movs_cons_mover h]; rfl

theorem movs_eq_nil_of_fill {f : Word A4} (hf : ∀ x ∈ f, phase x = 0) :
    movs f = [] := by
  induction f with
  | nil => rfl
  | cons a l ih =>
    rw [movs_cons_fill (hf a (by simp)) l]
    exact ih fun x hx => hf x (by simp [hx])

theorem phase_ne_zero_of_mem_movs {w : Word A4} {g : A4} (h : g ∈ movs w) :
    phase g ≠ 0 := by
  have h' : isMover g = true := (List.mem_filter.1 h).2
  simpa [isMover] using h'

theorem phaseSum_movs (w : Word A4) : phaseSum (movs w) = phaseSum w := by
  induction w with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : phase g = 0
    · rw [movs_cons_fill h, ih, phaseSum_cons, h]
      simp
    · rw [movs_cons_mover h, phaseSum_cons, phaseSum_cons, ih]

theorem movs_ne_nil_iff (w : Word A4) : movs w ≠ [] ↔ ¬ ∀ g ∈ w, phase g = 0 := by
  rw [← moverCount_eq_zero_iff]
  constructor
  · intro h hc
    exact h (List.length_eq_zero_iff.1 (by rw [length_movs]; exact hc))
  · intro h hm
    exact h (by rw [← length_movs, hm]; rfl)

/-- Generic split of a filtered list: a factorisation of `l.filter p` lifts to
a factorisation of `l`. -/
theorem filter_split {α : Type*} (p : α → Bool) :
    ∀ (l A B : List α), l.filter p = A ++ B →
      ∃ u v, l = u ++ v ∧ u.filter p = A ∧ v.filter p = B
  | [], A, B, h => by
    have hnil : A ++ B = [] := by simpa using h.symm
    obtain ⟨hA, hB⟩ := List.append_eq_nil_iff.1 hnil
    exact ⟨[], [], rfl, by simp [hA], by simp [hB]⟩
  | a :: l, A, B, h => by
    by_cases hp : p a
    · rw [List.filter_cons_of_pos hp] at h
      cases A with
      | nil =>
        refine ⟨[], a :: l, rfl, rfl, ?_⟩
        rw [List.filter_cons_of_pos hp]
        simpa using h
      | cons a' A' =>
        rw [List.cons_append] at h
        have ha : a' = a := (List.cons.inj h).1.symm
        subst ha
        obtain ⟨u, v, rfl, hu, hv⟩ := filter_split p l A' B (List.cons.inj h).2
        exact ⟨a' :: u, v, rfl, by rw [List.filter_cons_of_pos hp, hu], hv⟩
    · rw [List.filter_cons_of_neg (by simpa using hp)] at h
      obtain ⟨u, v, rfl, hu, hv⟩ := filter_split p l A B h
      exact ⟨a :: u, v, rfl, by rw [List.filter_cons_of_neg (by simpa using hp), hu], hv⟩

theorem movs_split {w A B : Word A4} (h : movs w = A ++ B) :
    ∃ u v, w = u ++ v ∧ movs u = A ∧ movs v = B :=
  filter_split isMover w A B h

/-- Two consecutive entries of `movs w` are two movers of `w` separated only by
fillers. -/
theorem exists_adjacent_movers {w A B : Word A4} {x y : A4}
    (h : movs w = A ++ x :: y :: B) :
    ∃ u f v, w = u ++ ([x] ++ f ++ [y]) ++ v ∧ (∀ z ∈ f, phase z = 0) ∧
      movs u = A ∧ movs v = B := by
  obtain ⟨u₀, w₁, rfl, hu₀, hw₁⟩ := movs_split h
  -- peel the first mover of `w₁`
  have hx : ¬ ∀ g ∈ w₁, phase g = 0 := by
    rw [← movs_ne_nil_iff]; rw [hw₁]; simp
  obtain ⟨f₀, m, r₁, rfl, hf₀, hm⟩ := exists_first_nonfill hx
  have hm₁ : movs (f₀ ++ m :: r₁) = m :: movs r₁ := by
    rw [movs_append, movs_eq_nil_of_fill hf₀, List.nil_append, movs_cons_mover hm]
  rw [hm₁] at hw₁
  have hmx : m = x := (List.cons.inj hw₁).1
  have hr₁ : movs r₁ = y :: B := (List.cons.inj hw₁).2
  subst hmx
  -- peel the next mover
  have hy : ¬ ∀ g ∈ r₁, phase g = 0 := by
    rw [← movs_ne_nil_iff]; rw [hr₁]; simp
  obtain ⟨f₁, m', r₂, rfl, hf₁, hm'⟩ := exists_first_nonfill hy
  have hm₂ : movs (f₁ ++ m' :: r₂) = m' :: movs r₂ := by
    rw [movs_append, movs_eq_nil_of_fill hf₁, List.nil_append, movs_cons_mover hm']
  rw [hm₂] at hr₁
  have hm'y : m' = y := (List.cons.inj hr₁).1
  have hr₂ : movs r₂ = B := (List.cons.inj hr₁).2
  subst hm'y
  refine ⟨u₀ ++ f₀, f₁, r₂, by simp, hf₁, ?_, hr₂⟩
  rw [movs_append, movs_eq_nil_of_fill hf₀, List.append_nil, hu₀]

theorem mem_denote_sigmaPlus {w : Word A4} (h : w ≠ []) : w ∈ denote sigmaPlus := by
  cases w with
  | nil => exact absurd rfl h
  | cons a l =>
    refine mem_denote_concat.2 ⟨[a], l, rfl, ?_, mem_denote_univ l⟩
    simp only [anyLetter, denote_atomsOf]
    refine ⟨a, ?_, rfl⟩
    have hmem : a ∈ lettersOfPhase (phase a) := (mem_lettersOfPhase_iff a _).2 rfl
    match hph : phase a with
    | ⟨0, _⟩ => simp only [List.mem_append]; exact Or.inl (Or.inl (by rwa [hph] at hmem))
    | ⟨1, _⟩ => simp only [List.mem_append]; exact Or.inl (Or.inr (by rwa [hph] at hmem))
    | ⟨2, _⟩ => simp only [List.mem_append]; exact Or.inr (by rwa [hph] at hmem)

theorem of_mem_movers {u : Word A4} (h : u ∈ denote movers) :
    ∃ m, u = [m] ∧ phase m ≠ 0 := by
  rcases h with h | h
  · obtain ⟨m, hm, rfl⟩ := mem_denote_A1.1 h
    exact ⟨m, rfl, by rw [hm]; decide⟩
  · obtain ⟨m, hm, rfl⟩ := mem_denote_A2.1 h
    exact ⟨m, rfl, by rw [hm]; decide⟩

theorem moverCount_of_mem_threeMovers {w : Word A4} (h : w ∈ denote threeMovers) :
    3 ≤ moverCount w := by
  simp only [threeMovers] at h
  obtain ⟨a, r₁, rfl, _, h₁⟩ := mem_denote_concat.1 h
  obtain ⟨m₁, r₂, rfl, hm₁, h₂⟩ := mem_denote_concat.1 h₁
  obtain ⟨b, r₃, rfl, _, h₃⟩ := mem_denote_concat.1 h₂
  obtain ⟨m₂, r₄, rfl, hm₂, h₄⟩ := mem_denote_concat.1 h₃
  obtain ⟨c, r₅, rfl, _, h₅⟩ := mem_denote_concat.1 h₄
  obtain ⟨m₃, d, rfl, hm₃, _⟩ := mem_denote_concat.1 h₅
  obtain ⟨g₁, rfl, hg₁⟩ := of_mem_movers hm₁
  obtain ⟨g₂, rfl, hg₂⟩ := of_mem_movers hm₂
  obtain ⟨g₃, rfl, hg₃⟩ := of_mem_movers hm₃
  simp only [moverCount_append, moverCount_cons, moverCount_nil, if_neg hg₁,
    if_neg hg₂, if_neg hg₃]
  omega

/-! ### The alternating phase pattern -/

/-- `AltM e v`: the mover list `v` continues an alternating run whose previous
phase is `e`, and terminates with a repeated phase. -/
inductive AltM : Fin 3 → Word A4 → Prop
  | last {e : Fin 3} {m : A4} (h : phase m = e) : AltM e [m]
  | step {e : Fin 3} {m : A4} {rest : Word A4} (hne : phase m ≠ e)
      (h0 : phase m ≠ 0) (hrest : AltM (phase m) rest) : AltM e (m :: rest)

/-- Running sums along an alternating run stay in `{e, 2e}` and close at `0`.
The invariant is `S ≡ 2e (mod 3)` at the entry of the run. -/
theorem altM_sum {e : Fin 3} {v : Word A4} (h : AltM e v) (he : e ≠ 0) :
    (2 * e.val + phaseSum v) % 3 = 0 ∧
      ∀ j, j < v.length → (2 * e.val + phaseSum (v.take j)) % 3 ≠ 0 := by
  induction h with
  | @last e m hm =>
    have hev : e.val ≠ 0 := fun hh => he (Fin.ext hh)
    have helt := e.isLt
    have hmv : (phase m).val = e.val := congrArg Fin.val hm
    constructor
    · rw [phaseSum_singleton, hmv]; omega
    · intro j hj
      have hj0 : j = 0 := by simpa using Nat.lt_one_iff.1 (by simpa using hj)
      subst hj0
      simp only [List.take_zero, phaseSum, List.map_nil, List.sum_nil, Nat.add_zero]
      omega
  | @step e m rest hne h0 hrest ih =>
    have hev : e.val ≠ 0 := fun hh => he (Fin.ext hh)
    have hmv0 : (phase m).val ≠ 0 := fun hh => h0 (Fin.ext hh)
    have hmne : (phase m).val ≠ e.val := fun hh => hne (Fin.ext hh)
    have helt := e.isLt
    have hmlt := (phase m).isLt
    obtain ⟨ih1, ih2⟩ := ih h0
    -- `phase m ≡ 2 e (mod 3)` because both lie in `{1,2}` and differ
    have hkey : (2 * e.val) % 3 = (phase m).val := by
      rcases (show e.val = 1 ∨ e.val = 2 by omega) with ha | ha <;>
        rw [ha] at hmne ⊢ <;> omega
    constructor
    · rw [phaseSum_cons]
      omega
    · intro j hj
      cases j with
      | zero =>
        simp only [List.take_zero, phaseSum, List.map_nil, List.sum_nil, Nat.add_zero]
        omega
      | succ k =>
        have hk : k < rest.length := by
          simp only [List.length_cons] at hj; omega
        have hik := ih2 k hk
        have hte : (m :: rest).take (k + 1) = m :: rest.take k := rfl
        rw [hte, phaseSum_cons]
        omega

/-- Boundary-pair phase pattern on a mover list: opening pair, alternating
middle, closing pair. -/
theorem structM_sum {m₁ m₂ : A4} {rest : Word A4}
    (hsame : phase m₂ = phase m₁) (h0 : phase m₁ ≠ 0)
    (halt : AltM (phase m₂) rest) :
    phaseSum (m₁ :: m₂ :: rest) % 3 = 0 ∧
      ∀ j, 0 < j → j < (m₁ :: m₂ :: rest).length →
        phaseSum ((m₁ :: m₂ :: rest).take j) % 3 ≠ 0 := by
  have h0' : phase m₂ ≠ 0 := by rw [hsame]; exact h0
  obtain ⟨hs, hp⟩ := altM_sum halt h0'
  have hv : (phase m₂).val = (phase m₁).val := congrArg Fin.val hsame
  have hne : (phase m₁).val ≠ 0 := fun hh => h0 (Fin.ext hh)
  have hlt := (phase m₁).isLt
  constructor
  · rw [phaseSum_cons, phaseSum_cons]; omega
  · intro j hj hjlt
    cases j with
    | zero => omega
    | succ k =>
      cases k with
      | zero =>
        show phaseSum [m₁] % 3 ≠ 0
        rw [phaseSum_singleton]; omega
      | succ k' =>
        have hk : k' < rest.length := by
          simp only [List.length_cons] at hjlt; omega
        have hik := hp k' hk
        have hte : (m₁ :: m₂ :: rest).take (k' + 1 + 1) = m₁ :: m₂ :: rest.take k' := rfl
        rw [hte, phaseSum_cons, phaseSum_cons]
        omega

/-- Peeling the alternating pattern off a mover list satisfying the
boundary-pair conditions. -/
theorem altM_of_tail {M : Word A4}
    (hall : ∀ z ∈ M, phase z ≠ 0)
    (hint : ∀ X Y : Word A4, ∀ x y : A4,
      M = X ++ x :: y :: Y → X ≠ [] → Y ≠ [] → phase y ≠ phase x)
    (hlast : ∃ A' : Word A4, ∃ x y : A4, M = A' ++ [x, y] ∧ phase y = phase x) :
    ∀ (rest pre : Word A4) (x : A4), M = pre ++ x :: rest → pre ≠ [] →
      rest ≠ [] → AltM (phase x) rest
  | [], _, _, _, _, hne => absurd rfl hne
  | [m], pre, x, hM, _, _ => by
    obtain ⟨A', x', y', hA', hxy⟩ := hlast
    have hrev : y' :: x' :: A'.reverse = m :: x :: pre.reverse := by
      have h1 : (A' ++ [x', y']).reverse = y' :: x' :: A'.reverse := by simp
      have h2 : (pre ++ x :: [m]).reverse = m :: x :: pre.reverse := by simp
      rw [← h1, ← h2, ← hA', ← hM]
    have hy : y' = m := (List.cons.inj hrev).1
    have hx : x' = x := (List.cons.inj (List.cons.inj hrev).2).1
    subst hy; subst hx
    exact AltM.last hxy
  | m :: m' :: rest', pre, x, hM, hpre, _ => by
    have hmemM : m ∈ M := by rw [hM]; simp
    have h0 : phase m ≠ 0 := hall m hmemM
    have hne : phase m ≠ phase x :=
      hint pre (m' :: rest') x m (by rw [hM]) hpre (by simp)
    refine AltM.step hne h0 ?_
    exact altM_of_tail hall hint hlast (m' :: rest') (pre ++ [x]) m
      (by rw [hM]; simp) (by simp) (by simp)

/-- `frLong` (≥ 3 movers, same-type boundary pairs, no interior same-type
pair) is first-return.  The proof runs the `C₃` boundary-pair arithmetic on
`movs w` (obligation `N-A4-FULL-038a`); the characterisation itself was
certified computationally in `scripts/research/a4_first_return_token.py`. -/
-- BLUEPRINT: N-A4-FULL-038a
theorem isReturn0_of_mem_frLong {w : Word A4} (hw : w ∈ denote frLong) :
    IsReturn0 w := by
  simp only [frLong, denote_inter, Set.mem_inter_iff] at hw
  obtain ⟨h1, h2, h3, h4⟩ := hw
  -- (1) opening pair: `w` starts with two same-phase movers
  obtain ⟨p, tl, hwp, hp, _⟩ := mem_denote_concat.1 h1
  obtain ⟨m₁, f, m₂, rfl, hm₁0, hm₂1, hf⟩ := of_mem_pairSame hp
  have hm₂0 : phase m₂ ≠ 0 := by rw [hm₂1]; exact hm₁0
  have hwform : w = m₁ :: (f ++ [m₂] ++ tl) := by rw [hwp]; simp
  have hmovs : movs w = m₁ :: m₂ :: movs tl := by
    rw [hwp, movs_append, movs_append, movs_append, movs_eq_nil_of_fill hf,
      movs_singleton_mover hm₁0, movs_singleton_mover hm₂0]
    simp
  -- (2) closing pair: `w` ends with two same-phase movers
  obtain ⟨hd, s, hws, _, hs⟩ := mem_denote_concat.1 h2
  obtain ⟨a, f', b, rfl, ha0, hba, hf'⟩ := of_mem_pairSame hs
  have hb0 : phase b ≠ 0 := by rw [hba]; exact ha0
  have hlastmover : ∃ init, w = init ++ [b] := ⟨hd ++ [a] ++ f', by rw [hws]; simp⟩
  have hlast : ∃ A' : Word A4, ∃ x y : A4,
      movs w = A' ++ [x, y] ∧ phase y = phase x := by
    refine ⟨movs hd, a, b, ?_, hba⟩
    rw [hws, movs_append, movs_append, movs_append, movs_eq_nil_of_fill hf',
      movs_singleton_mover ha0, movs_singleton_mover hb0]
    simp
  -- (3) no interior same-phase adjacent pair
  have hint : ∀ X Y : Word A4, ∀ x y : A4,
      movs w = X ++ x :: y :: Y → X ≠ [] → Y ≠ [] → phase y ≠ phase x := by
    intro X Y x y hsplit hX hY hxy
    obtain ⟨u, fm, v, hwuv, hfm, hu, hv⟩ := exists_adjacent_movers hsplit
    have hx0 : phase x ≠ 0 := by
      apply phase_ne_zero_of_mem_movs (w := w)
      rw [hsplit]; simp
    have hune : u ≠ [] := by
      rintro rfl
      exact hX (by rw [← hu]; rfl)
    have hvne : v ≠ [] := by
      rintro rfl
      exact hY (by rw [← hv]; rfl)
    apply h3
    exact mem_denote_concat.2 ⟨u, ([x] ++ fm ++ [y]) ++ v,
      by rw [hwuv, List.append_assoc],
      mem_denote_sigmaPlus hune,
      mem_denote_concat.2 ⟨[x] ++ fm ++ [y], v, rfl,
        mem_denote_pairSame hx0 hxy hfm, mem_denote_sigmaPlus hvne⟩⟩
  have hall : ∀ z ∈ movs w, phase z ≠ 0 := fun z hz => phase_ne_zero_of_mem_movs hz
  -- (4) at least three movers, so the alternating tail is nonempty
  have hcount : 3 ≤ moverCount w := moverCount_of_mem_threeMovers h4
  have htl : movs tl ≠ [] := by
    intro hnil
    rw [← length_movs, hmovs, hnil] at hcount
    simp at hcount
  have halt : AltM (phase m₂) (movs tl) :=
    altM_of_tail hall hint hlast (movs tl) [m₁] m₂ (by rw [hmovs]; rfl)
      (by simp) htl
  obtain ⟨hsum, hpref⟩ := structM_sum hm₂1 hm₁0 halt
  rw [← hmovs] at hsum hpref
  refine ⟨by rw [hwform]; simp, ?_, ?_⟩
  · rw [← phaseSum_movs]; exact hsum
  · intro k hk hklt
    rw [← phaseSum_movs]
    -- `movs (w.take k)` is a proper nonempty prefix of `movs w`
    have hsplitw : w = w.take k ++ w.drop k := (List.take_append_drop k w).symm
    have hmsplit : movs w = movs (w.take k) ++ movs (w.drop k) := by
      conv_lhs => rw [hsplitw]
      rw [movs_append]
    have hpos : 0 < (movs (w.take k)).length := by
      have hstart : w.take k = m₁ :: (f ++ [m₂] ++ tl).take (k - 1) := by
        rw [hwform]
        cases k with
        | zero => omega
        | succ k' => simp
      rw [hstart, movs_cons_mover hm₁0]
      simp
    have hlt : (movs (w.take k)).length < (movs w).length := by
      have hdropne : movs (w.drop k) ≠ [] := by
        obtain ⟨init, hinit⟩ := hlastmover
        have hb : b ∈ w.drop k := by
          have hmem : b ∈ w := by rw [hinit]; simp
          have hlen : w.length = init.length + 1 := by rw [hinit]; simp
          have : w.drop k = (w.take (w.length - 1)).drop k ++ [b] := by
            rw [hinit]
            simp only [List.length_append, List.length_cons, List.length_nil]
            rw [show init.length + 1 - 1 = init.length from rfl,
              List.take_left, List.drop_append_of_le_length (by omega)]
          rw [this]; simp
        intro hnil
        have hb' : b ∈ movs (w.drop k) := by
          rw [movs]
          exact List.mem_filter.2 ⟨hb, by simpa [isMover] using (by rw [hba]; exact ha0)⟩
        rw [hnil] at hb'; simp at hb'
      rw [hmsplit, List.length_append]
      have := List.length_pos_of_ne_nil hdropne
      omega
    have htake : (movs w).take (movs (w.take k)).length = movs (w.take k) := by
      conv_lhs => rw [hmsplit]
      rw [take_append_of_length_le _ _ (le_refl _)]
      simp
    have := hpref (movs (w.take k)).length hpos hlt
    rw [htake] at this
    exact this

/-- Forward inclusion `denote frToken ⊆ IsReturn0`.  The single-letter and
two-mover shapes reuse the proved cycle lemmas; the ≥ 3-mover shape is
`isReturn0_of_mem_frLong`. -/
theorem isReturn0_of_mem_frToken {w : Word A4}
    (hw : w ∈ denote frToken) : IsReturn0 w := by
  simp only [frToken, denote, Set.mem_union] at hw
  rcases hw with h | hw
  · obtain ⟨g, hg, rfl⟩ := mem_denote_A0.1 h
    exact isReturn0_A0 hg
  rcases hw with h | hw
  · obtain ⟨u, v, x, rfl, hu, hv, hx⟩ := mem_denote_concat3.1 h
    obtain ⟨g₁, h1, rfl⟩ := mem_denote_A1.1 hu
    obtain ⟨g₂, h2, rfl⟩ := mem_denote_A2.1 hx
    exact isReturn0_A1_fill_A2 h1 h2 hv
  rcases hw with h | h
  · obtain ⟨u, v, x, rfl, hu, hv, hx⟩ := mem_denote_concat3.1 h
    obtain ⟨g₁, h1, rfl⟩ := mem_denote_A2.1 hu
    obtain ⟨g₂, h2, rfl⟩ := mem_denote_A1.1 hx
    exact isReturn0_A2_fill_A1 h1 h2 hv
  · exact isReturn0_of_mem_frLong h

/-- Backward, all-filler case: a first-return word with no mover lands in the
`A0` disjunct of `frToken`. -/
theorem mem_frToken_of_isReturn0_no_mover {w : Word A4}
    (hw : IsReturn0 w) (hmov : ∀ g ∈ w, phase g = 0) :
    w ∈ denote frToken := by
  obtain ⟨g, hg, rfl⟩ := isReturn0_no_mover_eq_single hw hmov
  have hA0 : [g] ∈ denote A0 := mem_denote_A0.2 ⟨g, hg, rfl⟩
  exact Or.inl hA0

/-- Backward, two-mover case: a first-return word with exactly two movers is a
mixed pair `A1·fill·A2` or `A2·fill·A1`. -/
theorem mem_frToken_of_isReturn0_two_movers {w : Word A4}
    (hw : IsReturn0 w) (hc : moverCount w = 2) :
    w ∈ denote frToken := by
  obtain ⟨g1, t, rfl⟩ : ∃ g1 t, w = g1 :: t := by
    cases w with
    | nil => exact absurd rfl hw.1
    | cons g1 t => exact ⟨g1, t, rfl⟩
  have ht : t ≠ [] := by
    rintro rfl
    rw [moverCount_cons, moverCount_nil] at hc
    split at hc <;> omega
  have hg1 : phase g1 ≠ 0 := by
    intro h0
    rcases isReturn0_first_phase_ne_zero hw ht with h | h <;>
      rw [h0] at h <;> exact absurd h (by decide)
  have hct : moverCount t = 1 := by
    rw [moverCount_cons, if_neg hg1] at hc; omega
  obtain ⟨f1, g2, f2, rfl, hf1, hg2, hf2⟩ := exists_one_mover_split hct
  -- trailing fillers `f2` must be empty (else an interior landing)
  have hf2nil : f2 = [] := by
    by_contra hf2ne
    set P : Word A4 := g1 :: f1 ++ [g2] with hP
    have hwP : g1 :: (f1 ++ [g2] ++ f2) = P ++ f2 := by simp [hP]
    have hPlen : P.length = f1.length + 2 := by simp [hP]
    have hlt : P.length < (g1 :: (f1 ++ [g2] ++ f2)).length := by
      rw [hwP]; simp only [List.length_append]
      have : 0 < f2.length := List.length_pos_of_ne_nil hf2ne
      omega
    have hpos : 0 < P.length := by rw [hPlen]; omega
    have hint := hw.2.2 P.length hpos hlt
    have htake : (g1 :: (f1 ++ [g2] ++ f2)).take P.length = P := by
      rw [hwP, take_append_of_length_le P f2 (le_refl _)]; simp
    rw [htake] at hint
    -- phaseSum P ≡ 0 since total ≡ 0 and f2 fillers
    have hsumw : phaseSum (g1 :: (f1 ++ [g2] ++ f2)) % 3 = 0 := hw.2.1
    have hf2sum : phaseSum f2 = 0 := by
      apply phaseSum_of_mem_fill; rw [denote_fill]; exact hf2
    rw [hwP, phaseSum_append, hf2sum, Nat.add_zero] at hsumw
    exact hint hsumw
  subst hf2nil
  -- now `w = [g1] ++ f1 ++ [g2]`, f1 fillers, g1 g2 movers, mixed phases
  have hf1sum : phaseSum f1 = 0 := by
    apply phaseSum_of_mem_fill; rw [denote_fill]; exact hf1
  have hsum0 : ((phase g1).val + (phase g2).val) % 3 = 0 := by
    have hsumw : phaseSum (g1 :: (f1 ++ [g2] ++ [])) % 3 = 0 := hw.2.1
    have hval : phaseSum (g1 :: (f1 ++ [g2] ++ [])) =
        (phase g1).val + (phase g2).val := by
      rw [List.append_nil, phaseSum_cons, phaseSum_append, hf1sum]
      simp [phaseSum]
    rw [hval] at hsumw
    exact hsumw
  have hv1 : (phase g1).val = 1 ∨ (phase g1).val = 2 := by
    have hlt3 := (phase g1).isLt
    have hne : (phase g1).val ≠ 0 := fun hh => hg1 (Fin.ext hh)
    omega
  have hv2 : (phase g2).val = 1 ∨ (phase g2).val = 2 := by
    have hlt3 := (phase g2).isLt
    have hne : (phase g2).val ≠ 0 := fun hh => hg2 (Fin.ext hh)
    omega
  have hmixed : (phase g1 = 1 ∧ phase g2 = 2) ∨ (phase g1 = 2 ∧ phase g2 = 1) := by
    rcases hv1 with h1 | h1
    · rcases hv2 with h2 | h2
      · rw [h1, h2] at hsum0; exact absurd hsum0 (by decide)
      · exact Or.inl ⟨Fin.ext h1, Fin.ext h2⟩
    · rcases hv2 with h2 | h2
      · exact Or.inr ⟨Fin.ext h1, Fin.ext h2⟩
      · rw [h1, h2] at hsum0; exact absurd hsum0 (by decide)
  have hfillmem : f1 ∈ denote fill := by rw [denote_fill]; exact hf1
  rcases hmixed with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
  · have hmem : g1 :: (f1 ++ [g2] ++ []) ∈ denote (concat3 A1 fill A2) :=
      mem_denote_concat3.2 ⟨[g1], f1, [g2], by simp, mem_denote_A1.2 ⟨g1, hp1, rfl⟩,
        hfillmem, mem_denote_A2.2 ⟨g2, hp2, rfl⟩⟩
    exact Or.inr (Or.inl hmem)
  · have hmem : g1 :: (f1 ++ [g2] ++ []) ∈ denote (concat3 A2 fill A1) :=
      mem_denote_concat3.2 ⟨[g1], f1, [g2], by simp, mem_denote_A2.2 ⟨g1, hp1, rfl⟩,
        hfillmem, mem_denote_A1.2 ⟨g2, hp2, rfl⟩⟩
    exact Or.inr (Or.inr (Or.inl hmem))

/-! ### ≥3-mover backward case: `IsReturn0` + `moverCount ≥ 3` → `frLong`

The four `frLong` components follow from first-return separately:
* prefix pair: the first two movers must be same-type, else the prefix through
  the second mover lands on 0;
* suffix pair: the last two movers must be same-type, else the prefix before
  them sums to 0;
* no interior pair: around an interior same-type pair the running sums
  `s, s+p, s+2p` cover all residues mod 3, so one of the three interior
  prefixes would land on 0;
* three movers: direct decomposition. -/

/-- Workhorse: any nonempty proper append-prefix of a first-return word has
`phaseSum ≢ 0 (mod 3)`. -/
theorem isReturn0_prefix_sum_ne_zero {w P S : Word A4} (hw : IsReturn0 w)
    (hsplit : w = P ++ S) (hP : P ≠ []) (hS : S ≠ []) :
    phaseSum P % 3 ≠ 0 := by
  have hpos : 0 < P.length := List.length_pos_of_ne_nil hP
  have hlt : P.length < w.length := by
    rw [hsplit, List.length_append]
    have := List.length_pos_of_ne_nil hS
    omega
  have h := hw.2.2 P.length hpos hlt
  have htake : w.take P.length = P := by
    rw [hsplit, take_append_of_length_le P S (le_refl _)]; simp
  rw [htake] at h
  exact h

theorem mem_denote_movers {g : A4} (hg : phase g ≠ 0) :
    [g] ∈ denote movers := by
  have hlt := (phase g).isLt
  have hne : (phase g).val ≠ 0 := fun hh => hg (Fin.ext hh)
  have h12 : (phase g).val = 1 ∨ (phase g).val = 2 := by omega
  rcases h12 with h | h
  · exact Or.inl (mem_denote_A1.2 ⟨g, Fin.ext h, rfl⟩)
  · exact Or.inr (mem_denote_A2.2 ⟨g, Fin.ext h, rfl⟩)

theorem ne_nil_of_mem_sigmaPlus {w : Word A4} (h : w ∈ denote sigmaPlus) :
    w ≠ [] := by
  simp only [sigmaPlus] at h
  obtain ⟨u, v, rfl, hu, _⟩ := mem_denote_concat.1 h
  simp only [anyLetter, denote_atomsOf] at hu
  obtain ⟨a, _, rfl⟩ := hu
  simp

/-- Split at the last non-fill letter, if any exist. -/
theorem exists_last_nonfill {w : Word A4}
    (hne : ¬∀ g ∈ w, phase g = 0) :
    ∃ init g f, w = init ++ g :: f ∧ phase g ≠ 0 ∧ ∀ x ∈ f, phase x = 0 := by
  have hne' : ¬∀ g ∈ w.reverse, phase g = 0 := by
    intro h; exact hne fun g hg => h g (List.mem_reverse.2 hg)
  obtain ⟨f, g, rest, heq, hf, hg⟩ := exists_first_nonfill hne'
  refine ⟨rest.reverse, g, f.reverse, ?_, hg, ?_⟩
  · have h2 := congrArg List.reverse heq
    simpa using h2
  · intro x hx
    exact hf x (List.mem_reverse.1 hx)

/-- First-return with ≥3 movers: the first two movers are same-type,
giving the `pairSame · Σ*` prefix. -/
theorem prefix_pairSame_of_isReturn0 {w : Word A4}
    (hw : IsReturn0 w) (hc : 3 ≤ moverCount w) :
    w ∈ denote (concat pairSame univ) := by
  obtain ⟨m₁, t, rfl⟩ : ∃ m₁ t, w = m₁ :: t := by
    cases w with
    | nil => exact absurd rfl hw.1
    | cons a b => exact ⟨a, b, rfl⟩
  have ht : t ≠ [] := by
    rintro rfl
    rw [moverCount_cons, moverCount_nil] at hc
    split at hc <;> omega
  have hm₁ : phase m₁ ≠ 0 := by
    intro h0
    rcases isReturn0_first_phase_ne_zero hw ht with h | h <;>
      rw [h0] at h <;> exact absurd h (by decide)
  have hct : 2 ≤ moverCount t := by
    rw [moverCount_cons, if_neg hm₁] at hc; omega
  have htm : ¬∀ g ∈ t, phase g = 0 := by
    rw [← moverCount_eq_zero_iff]; omega
  obtain ⟨f, m₂, t₂, rfl, hf, hm₂⟩ := exists_first_nonfill htm
  have hct₂ : 1 ≤ moverCount t₂ := by
    rw [moverCount_append, (moverCount_eq_zero_iff f).2 hf, Nat.zero_add,
      moverCount_cons, if_neg hm₂] at hct
    omega
  have ht₂ : t₂ ≠ [] := by
    rintro rfl; rw [moverCount_nil] at hct₂; omega
  have hfsum : phaseSum f = 0 := by
    apply phaseSum_of_mem_fill; rw [denote_fill]; exact hf
  have hval : phaseSum (m₁ :: (f ++ [m₂])) =
      (phase m₁).val + (phase m₂).val := by
    rw [phaseSum_cons, phaseSum_append, hfsum, Nat.zero_add, phaseSum_singleton]
  have hsame : phase m₂ = phase m₁ := by
    have hkey : phaseSum (m₁ :: (f ++ [m₂])) % 3 ≠ 0 :=
      isReturn0_prefix_sum_ne_zero hw (by simp) (by simp) ht₂
    rw [hval] at hkey
    have hv₁ : (phase m₁).val ≠ 0 := fun hh => hm₁ (Fin.ext hh)
    have hv₂ : (phase m₂).val ≠ 0 := fun hh => hm₂ (Fin.ext hh)
    have hl₁ := (phase m₁).isLt
    have hl₂ := (phase m₂).isLt
    exact Fin.ext (by omega)
  exact mem_denote_concat.2 ⟨[m₁] ++ f ++ [m₂], t₂, by simp,
    mem_denote_pairSame hm₁ hsame hf, mem_denote_univ t₂⟩

/-- First-return with ≥3 movers: the last two movers are same-type,
giving the `Σ* · pairSame` suffix. -/
theorem suffix_pairSame_of_isReturn0 {w : Word A4}
    (hw : IsReturn0 w) (hc : 3 ≤ moverCount w) :
    w ∈ denote (concat univ pairSame) := by
  obtain ⟨init, g, rfl⟩ : ∃ init g, w = init ++ [g] := by
    cases hrev : w.reverse with
    | nil => exact absurd (by simpa using congrArg List.reverse hrev) hw.1
    | cons g t =>
      exact ⟨t.reverse, g, by simpa using congrArg List.reverse hrev⟩
  have hinit : init ≠ [] := by
    rintro rfl
    rw [List.nil_append, moverCount_cons, moverCount_nil] at hc
    split at hc <;> omega
  have hg : phase g ≠ 0 := by
    rcases isReturn0_last_phase_ne_zero hw hinit with h | h <;>
      rw [h] <;> decide
  have hcinit : 2 ≤ moverCount init := by
    rw [moverCount_append, moverCount_cons, if_neg hg, moverCount_nil] at hc
    omega
  have hinitm : ¬∀ x ∈ init, phase x = 0 := by
    rw [← moverCount_eq_zero_iff]; omega
  obtain ⟨init', m, f, rfl, hm, hf⟩ := exists_last_nonfill hinitm
  have hf0 : moverCount f = 0 := (moverCount_eq_zero_iff f).2 hf
  have hcinit' : 1 ≤ moverCount init' := by
    rw [moverCount_append, moverCount_cons, if_neg hm, hf0] at hcinit
    omega
  have hinit'ne : init' ≠ [] := by
    rintro rfl; rw [moverCount_nil] at hcinit'; omega
  have hfsum : phaseSum f = 0 := by
    apply phaseSum_of_mem_fill; rw [denote_fill]; exact hf
  have hmsum : phaseSum (m :: f) = (phase m).val := by
    rw [phaseSum_cons, hfsum, Nat.add_zero]
  have hs' : phaseSum init' % 3 ≠ 0 :=
    isReturn0_prefix_sum_ne_zero (S := m :: (f ++ [g])) hw (by simp) hinit'ne
      (by simp)
  have htotal := hw.2.1
  rw [phaseSum_append, phaseSum_append, hmsum, phaseSum_singleton] at htotal
  have hvm : (phase m).val ≠ 0 := fun hh => hm (Fin.ext hh)
  have hvg : (phase g).val ≠ 0 := fun hh => hg (Fin.ext hh)
  have hlm := (phase m).isLt
  have hlg := (phase g).isLt
  have hsame : phase g = phase m := Fin.ext (by omega)
  exact mem_denote_concat.2 ⟨init', [m] ++ f ++ [g], by simp,
    mem_denote_univ init', mem_denote_pairSame hm hsame hf⟩

/-- First-return words have no interior same-type adjacent-mover pair: the
running sums `s, s+p, s+2p` around such a pair cover all residues mod 3. -/
theorem not_mem_interior_pairSame {w : Word A4} (hw : IsReturn0 w) :
    w ∉ denote (concat sigmaPlus (concat pairSame sigmaPlus)) := by
  intro hmem
  obtain ⟨u, rest, rfl, hu, hrest⟩ := mem_denote_concat.1 hmem
  obtain ⟨x, v, rfl, hx, hv⟩ := mem_denote_concat.1 hrest
  obtain ⟨a, f, b, rfl, ha, hba, hf⟩ := of_mem_pairSame hx
  have hune := ne_nil_of_mem_sigmaPlus hu
  have hvne := ne_nil_of_mem_sigmaPlus hv
  have hfsum : phaseSum f = 0 := by
    apply phaseSum_of_mem_fill; rw [denote_fill]; exact hf
  have h1 : phaseSum u % 3 ≠ 0 :=
    isReturn0_prefix_sum_ne_zero hw rfl hune (by simp)
  have h2 : phaseSum (u ++ [a]) % 3 ≠ 0 :=
    isReturn0_prefix_sum_ne_zero (S := f ++ ([b] ++ v)) hw (by simp) (by simp)
      (by simp)
  have h3 : phaseSum (u ++ [a] ++ f ++ [b]) % 3 ≠ 0 :=
    isReturn0_prefix_sum_ne_zero (S := v) hw (by simp) (by simp) hvne
  have hs2 : phaseSum (u ++ [a]) = phaseSum u + (phase a).val := by
    rw [phaseSum_append, phaseSum_singleton]
  have hs3 : phaseSum (u ++ [a] ++ f ++ [b]) =
      phaseSum u + (phase a).val + (phase a).val := by
    rw [phaseSum_append, phaseSum_append, phaseSum_append, hfsum,
      phaseSum_singleton, phaseSum_singleton, hba, Nat.add_zero]
  rw [hs2] at h2
  rw [hs3] at h3
  have hva : (phase a).val ≠ 0 := fun hh => ha (Fin.ext hh)
  have hla := (phase a).isLt
  have hp12 : (phase a).val = 1 ∨ (phase a).val = 2 := by omega
  rcases hp12 with hp | hp <;> rw [hp] at h2 h3 <;> omega

/-- A word with at least three movers matches `Σ* M Σ* M Σ* M Σ*`. -/
theorem mem_denote_threeMovers {w : Word A4} (hc : 3 ≤ moverCount w) :
    w ∈ denote threeMovers := by
  have h1 : ¬∀ x ∈ w, phase x = 0 := by
    rw [← moverCount_eq_zero_iff]; omega
  obtain ⟨f₁, m₁, t₁, rfl, hf₁, hm₁⟩ := exists_first_nonfill h1
  have hc₁ : 2 ≤ moverCount t₁ := by
    rw [moverCount_append, (moverCount_eq_zero_iff f₁).2 hf₁, Nat.zero_add,
      moverCount_cons, if_neg hm₁] at hc
    omega
  have h2 : ¬∀ x ∈ t₁, phase x = 0 := by
    rw [← moverCount_eq_zero_iff]; omega
  obtain ⟨f₂, m₂, t₂, rfl, hf₂, hm₂⟩ := exists_first_nonfill h2
  have hc₂ : 1 ≤ moverCount t₂ := by
    rw [moverCount_append, (moverCount_eq_zero_iff f₂).2 hf₂, Nat.zero_add,
      moverCount_cons, if_neg hm₂] at hc₁
    omega
  have h3 : ¬∀ x ∈ t₂, phase x = 0 := by
    rw [← moverCount_eq_zero_iff]; omega
  obtain ⟨f₃, m₃, t₃, rfl, hf₃, hm₃⟩ := exists_first_nonfill h3
  simp only [threeMovers]
  refine mem_denote_concat.2 ⟨f₁, m₁ :: (f₂ ++ m₂ :: (f₃ ++ m₃ :: t₃)), rfl,
    mem_denote_univ _, ?_⟩
  refine mem_denote_concat.2 ⟨[m₁], f₂ ++ m₂ :: (f₃ ++ m₃ :: t₃), rfl,
    mem_denote_movers hm₁, ?_⟩
  refine mem_denote_concat.2 ⟨f₂, m₂ :: (f₃ ++ m₃ :: t₃), rfl,
    mem_denote_univ _, ?_⟩
  refine mem_denote_concat.2 ⟨[m₂], f₃ ++ m₃ :: t₃, rfl,
    mem_denote_movers hm₂, ?_⟩
  refine mem_denote_concat.2 ⟨f₃, m₃ :: t₃, rfl, mem_denote_univ _, ?_⟩
  exact mem_denote_concat.2 ⟨[m₃], t₃, rfl, mem_denote_movers hm₃,
    mem_denote_univ _⟩

/-- Backward, ≥3-mover case: a first-return word with at least three movers
lies in the `frLong` disjunct. -/
theorem mem_frLong_of_isReturn0_three_movers {w : Word A4}
    (hw : IsReturn0 w) (hc : 3 ≤ moverCount w) :
    w ∈ denote frLong := by
  have h1 := prefix_pairSame_of_isReturn0 hw hc
  have h2 := suffix_pairSame_of_isReturn0 hw hc
  have h3 : w ∈ denote (compl (concat sigmaPlus (concat pairSame sigmaPlus))) :=
    mem_denote_compl.2 (not_mem_interior_pairSame hw)
  have h4 := mem_denote_threeMovers hc
  simp only [frLong, denote_inter]
  exact ⟨h1, h2, h3, h4⟩

-- BLUEPRINT: N-A4-FULL-038
theorem mem_frToken_iff_isReturn0 (w : Word A4) :
    w ∈ denote frToken ↔ IsReturn0 w := by
  constructor
  · exact isReturn0_of_mem_frToken
  · intro hw
    by_cases hmov : ∀ g ∈ w, phase g = 0
    · exact mem_frToken_of_isReturn0_no_mover hw hmov
    · rcases Nat.lt_trichotomy (moverCount w) 2 with hlt | heq | hgt
      · -- 0 or 1 movers: 0 contradicts hmov, 1 contradicts phaseSum ≡ 0
        exfalso
        have h01 : moverCount w = 0 ∨ moverCount w = 1 := by omega
        rcases h01 with h0 | h1
        · exact hmov ((moverCount_eq_zero_iff w).1 h0)
        · -- exactly one mover ⇒ phaseSum ≡ its phase ∈ {1,2} ≢ 0
          obtain ⟨f1, g, f2, hweq, hf1, hg, hf2⟩ := exists_one_mover_split h1
          have hsumw : phaseSum (f1 ++ [g] ++ f2) % 3 = 0 := by
            rw [← hweq]; exact hw.2.1
          have hf1s : phaseSum f1 = 0 := by
            apply phaseSum_of_mem_fill; rw [denote_fill]; exact hf1
          have hf2s : phaseSum f2 = 0 := by
            apply phaseSum_of_mem_fill; rw [denote_fill]; exact hf2
          have hgs : phaseSum ([g] : Word A4) = (phase g).val := by
            simp [phaseSum_cons, phaseSum]
          rw [phaseSum_append, phaseSum_append, hf1s, hf2s, hgs,
            Nat.zero_add, Nat.add_zero] at hsumw
          have hgv : (phase g).val ≠ 0 := fun hh => hg (Fin.ext hh)
          have := (phase g).isLt
          omega
      · exact mem_frToken_of_isReturn0_two_movers hw heq
      · exact Or.inr (Or.inr (Or.inr
          (mem_frLong_of_isReturn0_three_movers hw (by omega))))

/-! ### Unique first-return factorisation (`N-A4-FULL-036`)

The generic language-power helpers `power_add` / `power_two` /
`power_concat_self` live in `GSH/Regex/CutParity.lean`. -/

theorem landingCount_congr (q : Fin 3) : ∀ (w : Word A4) (p p' : Nat),
    p % 3 = p' % 3 → landingCount q w p = landingCount q w p'
  | [], _, _, _ => rfl
  | g :: w, p, p', h => by
    have hstep : (p + (phase g).val) % 3 = (p' + (phase g).val) % 3 := by omega
    rw [landingCount_cons, landingCount_cons,
      landingCount_congr q w (p + (phase g).val) (p' + (phase g).val) hstep, hstep]

/-- Landing counts are additive across a phase-neutral split. -/
theorem landingCount_append_zero (q : Fin 3) {u : Word A4} (v : Word A4)
    (h : phaseSum u % 3 = 0) :
    landingCount q (u ++ v) 0 = landingCount q u 0 + landingCount q v 0 := by
  rw [landingCount_append, Nat.zero_add]
  congr 1
  exact landingCount_congr q v (phaseSum u) 0 (by omega)

/-- Peel one first-return prefix when the word has at least one landing. -/
-- BLUEPRINT: N-A4-FULL-036
theorem exists_first_return_prefix {w : Word A4}
    (hpos : 0 < landingCount 0 w 0) :
    ∃ u v : Word A4, w = u ++ v ∧ IsReturn0 u ∧
      landingCount 0 v 0 = landingCount 0 w 0 - 1 := by
  -- the first landing index exists; take the least one
  have hex : ∃ k, k < w.length ∧ phaseSum (w.take (k + 1)) % 3 = 0 := by
    by_contra hc
    push Not at hc
    have hz : landingCount 0 w 0 = 0 := by
      rw [landingCount0_eq_zero_iff]
      intro k hk
      exact hc k hk
    omega
  obtain ⟨hklt, hk0⟩ := Nat.find_spec hex
  set k := Nat.find hex with hkdef
  have hlen : (w.take (k + 1)).length = k + 1 := by
    rw [List.length_take]; omega
  have hret : IsReturn0 (w.take (k + 1)) := by
    refine ⟨?_, hk0, ?_⟩
    · intro hnil
      rw [hnil] at hlen; simp at hlen
    · intro j hj hjlt
      rw [hlen] at hjlt
      rw [List.take_take, show min j (k + 1) = j from by omega]
      cases j with
      | zero => omega
      | succ j' =>
        have hmin := Nat.find_min hex (m := j') (by omega)
        push Not at hmin
        exact hmin (by omega)
  refine ⟨w.take (k + 1), w.drop (k + 1), (List.take_append_drop _ _).symm, hret, ?_⟩
  have h1 : landingCount 0 (w.take (k + 1)) 0 = 1 :=
    ((isReturn0_iff_landingCount _).1 hret).2.1
  have hsplit : landingCount 0 w 0
      = landingCount 0 (w.take (k + 1)) 0 + landingCount 0 (w.drop (k + 1)) 0 := by
    conv_lhs => rw [← List.take_append_drop (k + 1) w]
    exact landingCount_append_zero 0 _ hk0
  omega

-- BLUEPRINT: N-A4-FULL-036
theorem denote_noReturn :
    denote noReturn = {w : Word A4 | landingCount 0 w 0 = 0} := by
  ext w
  simp only [noReturn, mem_denote_compl, Set.mem_setOf_eq]
  constructor
  · intro h
    by_contra hne
    obtain ⟨u, v, rfl, hu, _⟩ := exists_first_return_prefix (Nat.pos_of_ne_zero hne)
    exact h (mem_denote_concat.2 ⟨u, v, rfl, (mem_frToken_iff_isReturn0 u).2 hu,
      mem_denote_univ v⟩)
  · intro h hmem
    obtain ⟨u, v, rfl, hu, _⟩ := mem_denote_concat.1 hmem
    have hru := (mem_frToken_iff_isReturn0 u).1 hu
    have h1 : landingCount 0 u 0 = 1 := ((isReturn0_iff_landingCount _).1 hru).2.1
    have hsplit := landingCount_append_zero 0 (u := u) v hru.2.1
    omega

/-- Factorisation into `landingCount` first-return tokens plus a no-return
suffix. -/
theorem exists_return0_factorization_aux : ∀ (n : Nat) (w : Word A4),
    landingCount 0 w 0 = n →
    ∃ u pref : Word A4,
      u ∈ Language.power (denote frToken) n ∧ w = u ++ pref ∧
      pref ∈ denote noReturn
  | 0, w, h => ⟨[], w, rfl, rfl, by rw [denote_noReturn]; exact h⟩
  | n + 1, w, h => by
    obtain ⟨u₁, v, rfl, hu₁, hv⟩ := exists_first_return_prefix (w := w) (by omega)
    obtain ⟨u₂, pref, hu₂, hveq, hpref⟩ :=
      exists_return0_factorization_aux n v (by omega)
    refine ⟨u₁ ++ u₂, pref, ?_, by rw [hveq, List.append_assoc], hpref⟩
    rw [Language.power_succ, concat_power_comm]
    exact ⟨u₁, (mem_frToken_iff_isReturn0 u₁).2 hu₁, u₂, hu₂, rfl⟩

/-- Factor into `n` return tokens plus a no-return suffix; `n = landingCount`. -/
-- BLUEPRINT: N-A4-FULL-036
theorem exists_return0_factorization (w : Word A4) :
    ∃ n : Nat, ∃ u pref : Word A4,
      u ∈ Language.power (denote frToken) n ∧
      w = u ++ pref ∧
      pref ∈ denote noReturn ∧
      landingCount 0 w 0 = n := by
  obtain ⟨u, pref, hu, hw, hpref⟩ :=
    exists_return0_factorization_aux (landingCount 0 w 0) w rfl
  exact ⟨_, u, pref, hu, hw, hpref, rfl⟩

theorem phaseSum_of_mem_power_frToken : ∀ (n : Nat) (u : Word A4),
    u ∈ Language.power (denote frToken) n → phaseSum u % 3 = 0
  | 0, u, h => by rw [show u = [] from h]; rfl
  | n + 1, u, h => by
    obtain ⟨x, hx, t, ht, rfl⟩ := h
    have h1 := phaseSum_of_mem_power_frToken n x hx
    have h2 := ((mem_frToken_iff_isReturn0 t).1 ht).2.1
    rw [phaseSum_append]; omega

theorem landingCount_of_mem_power_frToken : ∀ (n : Nat) (u : Word A4),
    u ∈ Language.power (denote frToken) n → landingCount 0 u 0 = n
  | 0, u, h => by rw [show u = [] from h]; rfl
  | n + 1, u, h => by
    obtain ⟨x, hx, t, ht, rfl⟩ := h
    have h1 := landingCount_of_mem_power_frToken n x hx
    have hps := phaseSum_of_mem_power_frToken n x hx
    have h2 : landingCount 0 t 0 = 1 :=
      ((isReturn0_iff_landingCount t).1 ((mem_frToken_iff_isReturn0 t).1 ht)).2.1
    rw [landingCount_append_zero 0 t hps]
    omega

-- BLUEPRINT: N-A4-FULL-036
theorem denote_evenReturns :
    denote evenReturns = {w : Word A4 | landingCount 0 w 0 % 2 = 0} := by
  ext w
  constructor
  · intro hw
    obtain ⟨u, pref, rfl, hu, hpref⟩ := mem_denote_concat.1 hw
    obtain ⟨m, hm⟩ := hu
    have hm' : u ∈ Language.power (denote frToken) (2 * m) := by
      have heq : Language.power (denote returnToken2) m
          = Language.power (denote frToken) (2 * m) :=
        power_concat_self (denote frToken) m
      rwa [heq] at hm
    have hc := landingCount_of_mem_power_frToken (2 * m) u hm'
    have hps := phaseSum_of_mem_power_frToken (2 * m) u hm'
    have hpz : landingCount 0 pref 0 = 0 := by
      rw [denote_noReturn] at hpref; exact hpref
    show landingCount 0 (u ++ pref) 0 % 2 = 0
    rw [landingCount_append_zero 0 pref hps, hc, hpz]
    omega
  · intro hw
    have hev : landingCount 0 w 0 % 2 = 0 := hw
    obtain ⟨n, u, pref, hu, hweq, hpref, hn⟩ := exists_return0_factorization w
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    refine mem_denote_concat.2 ⟨u, pref, hweq, ?_, hpref⟩
    refine ⟨m, ?_⟩
    show u ∈ Language.power (Language.concat (denote frToken) (denote frToken)) m
    rw [power_concat_self]
    exact hu

/-! ### First arrival at a nonzero phase (`N-A4-FULL-034`) -/

theorem mem_denote_anyLetter {w : Word A4} :
    w ∈ denote anyLetter ↔ ∃ g : A4, w = [g] := by
  simp only [anyLetter, denote_atomsOf]
  constructor
  · rintro ⟨g, _, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    refine ⟨g, ?_, rfl⟩
    have hmem : g ∈ lettersOfPhase (phase g) := (mem_lettersOfPhase_iff g _).2 rfl
    match hph : phase g with
    | ⟨0, _⟩ => simp only [List.mem_append]; exact Or.inl (Or.inl (by rwa [hph] at hmem))
    | ⟨1, _⟩ => simp only [List.mem_append]; exact Or.inl (Or.inr (by rwa [hph] at hmem))
    | ⟨2, _⟩ => simp only [List.mem_append]; exact Or.inr (by rwa [hph] at hmem)

/-- Every nonempty prefix keeps the running phase away from `q`. -/
def AvoidPhase (q : Fin 3) (v : Word A4) : Prop :=
  ∀ k, 0 < k → k ≤ v.length → phaseSum (v.take k) % 3 ≠ q.val

/-- No two adjacent entries of a mover list share a phase. -/
def NoSamePair (M : Word A4) : Prop :=
  ∀ (A B : Word A4) (x y : A4), M = A ++ x :: y :: B → phase y ≠ phase x

theorem noSamePair_movs_iff {v : Word A4} :
    NoSamePair (movs v) ↔ v ∉ denote (concat univ (concat pairSame univ)) := by
  constructor
  · intro h hmem
    obtain ⟨u, rest, rfl, _, hrest⟩ := mem_denote_concat.1 hmem
    obtain ⟨p, z, rfl, hp, _⟩ := mem_denote_concat.1 hrest
    obtain ⟨x, fm, y, rfl, hx0, hyx, hfm⟩ := of_mem_pairSame hp
    refine h (movs u) (movs z) x y ?_ hyx
    rw [movs_append, movs_append, movs_append, movs_append,
      movs_eq_nil_of_fill hfm, movs_singleton_mover hx0,
      movs_singleton_mover (by rw [hyx]; exact hx0)]
    simp
  · intro h A B x y hsplit hxy
    obtain ⟨u, fm, z, hveq, hfm, _, _⟩ := exists_adjacent_movers hsplit
    have hx0 : phase x ≠ 0 :=
      phase_ne_zero_of_mem_movs (w := v) (by rw [hsplit]; simp)
    exact h (mem_denote_concat.2 ⟨u, ([x] ++ fm ++ [y]) ++ z,
      by rw [hveq, List.append_assoc],
      mem_denote_univ u,
      mem_denote_concat.2 ⟨[x] ++ fm ++ [y], z, rfl,
        mem_denote_pairSame hx0 hxy hfm, mem_denote_univ z⟩⟩)

theorem headPhase_movs_iff {v : Word A4} {q : Fin 3} (hq : q ≠ 0) :
    (∀ m rest, movs v = m :: rest → phase m ≠ q)
      ↔ v ∉ denote (concat fill (concat (Aph q) univ)) := by
  constructor
  · intro h hmem
    obtain ⟨fm, rest, rfl, hfm, hrest⟩ := mem_denote_concat.1 hmem
    obtain ⟨gg, z, rfl, hg, _⟩ := mem_denote_concat.1 hrest
    obtain ⟨g, hgq, rfl⟩ := mem_denote_Aph.1 hg
    rw [denote_fill] at hfm
    have hg0 : phase g ≠ 0 := by rw [hgq]; exact hq
    refine h g (movs z) ?_ hgq
    rw [movs_append, movs_append, movs_eq_nil_of_fill hfm,
      movs_singleton_mover hg0]
    simp
  · intro h m rest hsplit hmq
    have hm0 : phase m ≠ 0 := by rw [hmq]; exact hq
    have hnf : ¬ ∀ g ∈ v, phase g = 0 := by
      rw [← movs_ne_nil_iff, hsplit]; simp
    obtain ⟨fm, g, r, rfl, hfm, hg0⟩ := exists_first_nonfill hnf
    have hmv : movs (fm ++ g :: r) = g :: movs r := by
      rw [movs_append, movs_eq_nil_of_fill hfm, List.nil_append,
        movs_cons_mover hg0]
    rw [hmv] at hsplit
    have hgm : g = m := (List.cons.inj hsplit).1
    subst hgm
    exact h (mem_denote_concat.2 ⟨fm, g :: r, rfl,
      by rw [denote_fill]; exact hfm,
      mem_denote_concat.2 ⟨[g], r, rfl, mem_denote_Aph.2 ⟨g, hmq, rfl⟩,
        mem_denote_univ r⟩⟩)

/-- Alternating movers keep the running phase away from `q ≠ 0`: consecutive
distinct phases sum to `0` mod `3`, so the running sum is 2-periodic. -/
theorem avoid_of_noSamePair (q : Fin 3) (hq : q.val ≠ 0) :
    ∀ (M : Word A4) (s : Nat), (∀ m ∈ M, phase m ≠ 0) → s % 3 ≠ q.val →
      NoSamePair M →
      (∀ m rest, M = m :: rest → (s + (phase m).val) % 3 ≠ q.val) →
      ∀ j, 0 < j → j ≤ M.length → (s + phaseSum (M.take j)) % 3 ≠ q.val
  | [], _, _, _, _, _ => by
    intro j hj hjle; simp only [List.length_nil] at hjle; omega
  | [m], s, _, _, _, hhead => by
    intro j hj hjle
    simp only [List.length_cons, List.length_nil] at hjle
    have hj1 : j = 1 := by omega
    subst hj1
    show (s + phaseSum [m]) % 3 ≠ q.val
    rw [phaseSum_singleton]
    exact hhead m [] rfl
  | m :: m' :: rest, s, hmov, hs, hnp, hhead => by
    have hmm' : phase m' ≠ phase m := hnp [] rest m m' rfl
    have h1 : (s + (phase m).val) % 3 ≠ q.val := hhead m _ rfl
    have hm0 : phase m ≠ 0 := hmov m (by simp)
    have hm'0 : phase m' ≠ 0 := hmov m' (by simp)
    have hsum0 : ((phase m).val + (phase m').val) % 3 = 0 := by
      have hl1 := (phase m).isLt
      have hl2 := (phase m').isLt
      have a1 : (phase m).val ≠ 0 := fun hh => hm0 (Fin.ext hh)
      have a2 : (phase m').val ≠ 0 := fun hh => hm'0 (Fin.ext hh)
      have a3 : (phase m').val ≠ (phase m).val := fun hh => hmm' (Fin.ext hh)
      omega
    have ih := avoid_of_noSamePair q hq (m' :: rest) (s + (phase m).val)
      (fun x hx => hmov x (by simp [hx])) h1
      (fun A B x y heq hxy => hnp (m :: A) B x y (by rw [heq]; simp) hxy)
      (fun x r heq => by
        have hx : m' = x := (List.cons.inj heq).1
        subst hx
        omega)
    intro j hj hjle
    cases j with
    | zero => omega
    | succ j' =>
      cases j' with
      | zero =>
        show (s + phaseSum [m]) % 3 ≠ q.val
        rw [phaseSum_singleton]; exact h1
      | succ j'' =>
        have hle : j'' + 1 ≤ (m' :: rest).length := by
          simp only [List.length_cons] at hjle ⊢; omega
        have hthis := ih (j'' + 1) (by omega) hle
        have hte : (m :: m' :: rest).take (j'' + 1 + 1)
            = m :: (m' :: rest).take (j'' + 1) := rfl
        rw [hte, phaseSum_cons]
        omega

/-- Converse: avoiding `q ≠ 0` forces alternating movers. -/
theorem noSamePair_of_avoid (q : Fin 3) (_hq : q.val ≠ 0)
    {M : Word A4} {s : Nat} (hs : s % 3 ≠ q.val)
    (hmov : ∀ m ∈ M, phase m ≠ 0)
    (havoid : ∀ j, 0 < j → j ≤ M.length → (s + phaseSum (M.take j)) % 3 ≠ q.val) :
    NoSamePair M ∧ (∀ m rest, M = m :: rest → (s + (phase m).val) % 3 ≠ q.val) := by
  constructor
  · intro A B x y hsplit hxy
    subst hsplit
    have hx0 : phase x ≠ 0 := hmov x (by simp)
    have hxv : (phase x).val ≠ 0 := fun hh => hx0 (Fin.ext hh)
    have hxlt := (phase x).isLt
    have hyx : (phase y).val = (phase x).val := congrArg Fin.val hxy
    have hlenM : (A ++ x :: y :: B).length = A.length + 2 + B.length := by
      simp only [List.length_append, List.length_cons]; omega
    have ht0 : (A ++ x :: y :: B).take A.length = A := by
      rw [take_append_of_length_le _ _ (le_refl _)]; simp
    have ht1 : (A ++ x :: y :: B).take (A.length + 1) = A ++ [x] := by
      rw [take_append_of_length_le _ _ (by omega)]
      simp
    have ht2 : (A ++ x :: y :: B).take (A.length + 2) = A ++ [x, y] := by
      rw [take_append_of_length_le _ _ (by omega)]
      simp
    have hs0 : (s + phaseSum A) % 3 ≠ q.val := by
      rcases Nat.eq_zero_or_pos A.length with h0 | hpos
      · have hA : A = [] := List.length_eq_zero_iff.1 h0
        rw [hA]; simpa [phaseSum] using hs
      · have := havoid A.length hpos (by omega)
        rwa [ht0] at this
    have hs1 : (s + phaseSum A + (phase x).val) % 3 ≠ q.val := by
      have := havoid (A.length + 1) (by omega) (by omega)
      rw [ht1, phaseSum_append, phaseSum_singleton] at this
      omega
    have hs2 : (s + phaseSum A + (phase x).val + (phase x).val) % 3 ≠ q.val := by
      have := havoid (A.length + 2) (by omega) (by omega)
      rw [ht2] at this
      have hval : phaseSum (A ++ [x, y]) = phaseSum A + (phase x).val + (phase y).val := by
        rw [phaseSum_append]
        simp [phaseSum, Nat.add_assoc]
      rw [hval, hyx] at this
      omega
    -- three consecutive multiples of `phase x` cover all residues mod 3
    rcases (show (phase x).val = 1 ∨ (phase x).val = 2 by omega) with hc | hc <;>
      rw [hc] at hs1 hs2 <;>
      rcases (show (s + phaseSum A) % 3 = 0 ∨ (s + phaseSum A) % 3 = 1 ∨
        (s + phaseSum A) % 3 = 2 by omega) with hr | hr | hr <;> omega
  · intro m rest hsplit
    have := havoid 1 (by omega) (by rw [hsplit]; simp)
    rw [hsplit] at this
    show (s + (phase m).val) % 3 ≠ q.val
    have hte : (m :: rest).take 1 = [m] := rfl
    rw [hte, phaseSum_singleton] at this
    exact this

/-- Every prefix of `movs v` is realised by a prefix of `v`. -/
theorem exists_take_of_movs_take : ∀ (v : Word A4) (j : Nat), j ≤ (movs v).length →
    ∃ k, k ≤ v.length ∧ movs (v.take k) = (movs v).take j ∧ (0 < j → 0 < k)
  | [], j, hj => by
    simp only [movs_nil, List.length_nil] at hj
    exact ⟨0, by simp, by simp, by omega⟩
  | g :: v', j, hj => by
    by_cases hg : phase g = 0
    · rw [movs_cons_fill hg] at hj ⊢
      obtain ⟨k, hkle, hk, _⟩ := exists_take_of_movs_take v' j hj
      refine ⟨k + 1, by simp only [List.length_cons]; omega, ?_, fun _ => by omega⟩
      have hte : (g :: v').take (k + 1) = g :: v'.take k := rfl
      rw [hte, movs_cons_fill hg, hk]
    · rw [movs_cons_mover hg] at hj ⊢
      cases j with
      | zero => exact ⟨0, by simp, by simp, by omega⟩
      | succ j' =>
        simp only [List.length_cons] at hj
        obtain ⟨k, hkle, hk, _⟩ := exists_take_of_movs_take v' j' (by omega)
        refine ⟨k + 1, by simp only [List.length_cons]; omega, ?_, fun _ => by omega⟩
        have hte : (g :: v').take (k + 1) = g :: v'.take k := rfl
        rw [hte, movs_cons_mover hg, hk]
        rfl

theorem avoidPhase_of_movs {q : Fin 3} (hqv : q.val ≠ 0) {v : Word A4}
    (h : ∀ j, 0 < j → j ≤ (movs v).length →
      phaseSum ((movs v).take j) % 3 ≠ q.val) :
    AvoidPhase q v := by
  intro k hk hkle
  have hsplit : movs v = movs (v.take k) ++ movs (v.drop k) := by
    conv_lhs => rw [← List.take_append_drop k v]
    rw [movs_append]
  have htake : (movs v).take (movs (v.take k)).length = movs (v.take k) := by
    conv_lhs => rw [hsplit]
    rw [take_append_of_length_le _ _ (le_refl _)]
    simp
  have hjle : (movs (v.take k)).length ≤ (movs v).length := by
    rw [hsplit, List.length_append]; omega
  rw [← phaseSum_movs]
  rcases Nat.eq_zero_or_pos (movs (v.take k)).length with hj0 | hjpos
  · have hnil : movs (v.take k) = [] := List.length_eq_zero_iff.1 hj0
    rw [hnil]
    intro hh
    exact hqv (by simpa [phaseSum] using hh.symm)
  · have hres := h _ hjpos hjle
    rwa [htake] at hres

theorem movs_avoid_of_avoidPhase {q : Fin 3} {v : Word A4} (h : AvoidPhase q v) :
    ∀ j, 0 < j → j ≤ (movs v).length → phaseSum ((movs v).take j) % 3 ≠ q.val := by
  intro j hj hjle
  obtain ⟨k, hkle, hk, hkpos⟩ := exists_take_of_movs_take v j hjle
  rw [← hk, phaseSum_movs]
  exact h k (hkpos hj) hkle

theorem denote_avoidP {q : Fin 3} (hq : q ≠ 0) :
    denote (avoidP q) = {v : Word A4 | AvoidPhase q v} := by
  have hqv : q.val ≠ 0 := fun hh => hq (Fin.ext hh)
  ext v
  simp only [avoidP, denote_inter, Set.mem_inter_iff, mem_denote_compl,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have hnp : NoSamePair (movs v) := noSamePair_movs_iff.2 h1
    have hhd : ∀ m rest, movs v = m :: rest → phase m ≠ q :=
      (headPhase_movs_iff hq).2 h2
    refine avoidPhase_of_movs hqv ?_
    have hmov : ∀ m ∈ movs v, phase m ≠ 0 := fun m hm => phase_ne_zero_of_mem_movs hm
    have := avoid_of_noSamePair q hqv (movs v) 0 hmov (by simpa using Ne.symm hqv) hnp
      (fun m rest heq => by
        have hm := hhd m rest heq
        have hlt := (phase m).isLt
        have hqlt := q.isLt
        have : (phase m).val ≠ q.val := fun hh => hm (Fin.ext hh)
        omega)
    intro j hj hjle
    simpa using this j hj hjle
  · intro hv
    have hmovavoid := movs_avoid_of_avoidPhase hv
    have hmov : ∀ m ∈ movs v, phase m ≠ 0 := fun m hm => phase_ne_zero_of_mem_movs hm
    obtain ⟨hnp, hhd⟩ := noSamePair_of_avoid q hqv (M := movs v) (s := 0)
      (by simpa using Ne.symm hqv) hmov (by simpa using hmovavoid)
    refine ⟨noSamePair_movs_iff.1 hnp, (headPhase_movs_iff hq).1 ?_⟩
    intro m rest heq hmq
    have := hhd m rest heq
    rw [hmq] at this
    simp only [Nat.zero_add] at this
    exact this (Nat.mod_eq_of_lt q.isLt)

/-- The first arrival at phase `q`. -/
def IsArrival (q : Fin 3) (u : Word A4) : Prop :=
  u ≠ [] ∧ phaseSum u % 3 = q.val ∧
    ∀ k, 0 < k → k < u.length → phaseSum (u.take k) % 3 ≠ q.val

theorem denote_opener {q : Fin 3} (hq : q ≠ 0) :
    denote (opener q) = {u : Word A4 | IsArrival q u} := by
  ext u
  simp only [opener, denote_inter, Set.mem_inter_iff, mem_denote_compl,
    denote_avoidP hq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hcat, hnot⟩
    obtain ⟨v, x, rfl, hv, hx⟩ := mem_denote_concat.1 hcat
    obtain ⟨g, rfl⟩ := mem_denote_anyLetter.1 hx
    have hvav : AvoidPhase q v := by rw [denote_avoidP hq] at hv; exact hv
    have hlen : (v ++ [g]).length = v.length + 1 := by simp
    have hpre : ∀ k, k ≤ v.length → (v ++ [g]).take k = v.take k := by
      intro k hk
      exact take_append_of_le_length (by simpa using hk)
    refine ⟨by simp, ?_, ?_⟩
    · by_contra hne
      refine hnot ?_
      intro k hk hkle
      rw [hlen] at hkle
      rcases Nat.lt_or_ge k (v.length + 1) with hlt | hge
      · rw [hpre k (by omega)]
        exact hvav k hk (by omega)
      · have hkeq : k = v.length + 1 := by omega
        subst hkeq
        rw [List.take_of_length_le (by omega)]
        exact hne
    · intro k hk hklt
      rw [hlen] at hklt
      rw [hpre k (by omega)]
      exact hvav k hk (by omega)
  · rintro ⟨hne, hsum, hint⟩
    obtain ⟨v, g, rfl⟩ : ∃ v g, u = v ++ [g] := by
      rcases List.eq_nil_or_concat u with h | ⟨v, g, h⟩
      · exact absurd h hne
      · exact ⟨v, g, by rw [List.concat_eq_append] at h; exact h⟩
    have hlen : (v ++ [g]).length = v.length + 1 := by simp
    have hpre : ∀ k, k ≤ v.length → (v ++ [g]).take k = v.take k := by
      intro k hk
      exact take_append_of_le_length (by simpa using hk)
    have hvav : AvoidPhase q v := by
      intro k hk hkle
      rw [← hpre k hkle]
      exact hint k hk (by rw [hlen]; omega)
    refine ⟨mem_denote_concat.2 ⟨v, [g], rfl, by rw [denote_avoidP hq]; exact hvav,
      mem_denote_anyLetter.2 ⟨g, rfl⟩⟩, ?_⟩
    intro hcontra
    have := hcontra (v.length + 1) (by omega) (by rw [hlen])
    rw [List.take_of_length_le (by omega)] at this
    exact this hsum

/-! ### Landing counts at a nonzero cut phase -/

theorem landingCount_shift (q : Fin 3) : ∀ (w : Word A4) (p : Nat),
    landingCount q w (q.val + p) = landingCount 0 w p
  | [], _ => rfl
  | g :: w, p => by
    rw [landingCount_cons, landingCount_cons]
    have harg : q.val + p + (phase g).val = q.val + (p + (phase g).val) := by omega
    rw [harg, landingCount_shift q w (p + (phase g).val)]
    congr 1
    have hqlt := q.isLt
    have hiff : ((q.val + (p + (phase g).val)) % 3 = q.val)
        ↔ ((p + (phase g).val) % 3 = (0 : Fin 3).val) := by
      simp only [Fin.val_zero]
      omega
    by_cases h : (p + (phase g).val) % 3 = (0 : Fin 3).val
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (fun hh => h (hiff.1 hh)), if_neg h]

theorem landingCount_eq_one_of_isArrival {q : Fin 3} {u : Word A4}
    (h : IsArrival q u) : landingCount q u 0 = 1 := by
  obtain ⟨hne, hsum, hint⟩ := h
  obtain ⟨init, last, hu⟩ : ∃ init last, u = init ++ [last] := by
    rcases List.eq_nil_or_concat u with h | ⟨init, last, h⟩
    · exact absurd h hne
    · exact ⟨init, last, by rw [List.concat_eq_append] at h; exact h⟩
  have hlen : u.length = init.length + 1 := by rw [hu]; simp
  rw [hu, landingCount_append]
  have hinit0 : landingCount q init 0 = 0 := by
    rw [landingCount_eq_zero_iff]
    intro k hk
    have hpr : init.take (k + 1) = u.take (k + 1) := by
      rw [hu, take_append_of_le_length (by omega)]
    rw [Nat.zero_add, hpr]
    exact hint (k + 1) (by omega) (by omega)
  have hcond : (0 + phaseSum init + (phase last).val) % 3 = q.val := by
    rw [hu, phaseSum_append, phaseSum_singleton] at hsum
    simpa using hsum
  rw [hinit0, Nat.zero_add, landingCount_cons, landingCount_nil, Nat.add_zero,
    if_pos hcond]

theorem exists_first_arrival_prefix {q : Fin 3} {w : Word A4}
    (hpos : 0 < landingCount q w 0) :
    ∃ u v : Word A4, w = u ++ v ∧ IsArrival q u ∧
      landingCount 0 v 0 = landingCount q w 0 - 1 := by
  have hex : ∃ k, k < w.length ∧ phaseSum (w.take (k + 1)) % 3 = q.val := by
    by_contra hc
    push Not at hc
    have hz : landingCount q w 0 = 0 := by
      rw [landingCount_eq_zero_iff]
      intro k hk
      simpa using hc k hk
    omega
  obtain ⟨hklt, hk0⟩ := Nat.find_spec hex
  set k := Nat.find hex with hkdef
  have hlen : (w.take (k + 1)).length = k + 1 := by
    rw [List.length_take]; omega
  have harr : IsArrival q (w.take (k + 1)) := by
    refine ⟨?_, hk0, ?_⟩
    · intro hnil
      rw [hnil] at hlen; simp at hlen
    · intro j hj hjlt
      rw [hlen] at hjlt
      rw [List.take_take, show min j (k + 1) = j from by omega]
      cases j with
      | zero => omega
      | succ j' =>
        have hmin := Nat.find_min hex (m := j') (by omega)
        push Not at hmin
        exact hmin (by omega)
  refine ⟨w.take (k + 1), w.drop (k + 1), (List.take_append_drop _ _).symm, harr, ?_⟩
  have h1 : landingCount q (w.take (k + 1)) 0 = 1 := landingCount_eq_one_of_isArrival harr
  have hsplit : landingCount q w 0
      = landingCount q (w.take (k + 1)) 0 + landingCount 0 (w.drop (k + 1)) 0 := by
    conv_lhs => rw [← List.take_append_drop (k + 1) w]
    rw [landingCount_append, Nat.zero_add]
    congr 1
    rw [landingCount_congr q _ (phaseSum (w.take (k + 1))) (q.val + 0) (by omega)]
    exact landingCount_shift q _ 0
  omega

theorem landingCount_append_arrival {q : Fin 3} {u : Word A4} (v : Word A4)
    (h : IsArrival q u) :
    landingCount q (u ++ v) 0 = 1 + landingCount 0 v 0 := by
  rw [landingCount_append, Nat.zero_add, landingCount_eq_one_of_isArrival h]
  congr 1
  rw [landingCount_congr q v (phaseSum u) (q.val + 0) (by have := h.2.1; omega)]
  exact landingCount_shift q v 0

theorem denote_evenLandings_ne_zero {q : Fin 3} (hq : q ≠ 0) :
    denote (union (noLand (opener q)) (oddReturnsAfter (opener q)))
      = {w : Word A4 | landingCount q w 0 % 2 = 0} := by
  have hzero : ∀ w : Word A4,
      w ∉ denote (concat (opener q) univ) ↔ landingCount q w 0 = 0 := by
    intro w
    constructor
    · intro h
      by_contra hne
      obtain ⟨u, v, rfl, hu, _⟩ := exists_first_arrival_prefix (Nat.pos_of_ne_zero hne)
      exact h (mem_denote_concat.2 ⟨u, v, rfl, by rw [denote_opener hq]; exact hu,
        mem_denote_univ v⟩)
    · intro h hmem
      obtain ⟨u, v, rfl, hu, _⟩ := mem_denote_concat.1 hmem
      have hu' : IsArrival q u := by rw [denote_opener hq] at hu; exact hu
      rw [landingCount_append_arrival v hu'] at h
      omega
  ext w
  simp only [noLand, oddReturnsAfter, Set.mem_setOf_eq]
  constructor
  · rintro (h | h)
    · rw [(hzero w).1 h]
    · obtain ⟨u, rest, rfl, hu, hrest⟩ := mem_denote_concat.1 h
      obtain ⟨t, s, rfl, ht, hs⟩ := mem_denote_concat.1 hrest
      have hu' : IsArrival q u := by rw [denote_opener hq] at hu; exact hu
      have ht' : IsReturn0 t := (mem_frToken_iff_isReturn0 t).1 ht
      have hs' : landingCount 0 s 0 % 2 = 0 := by
        rw [denote_evenReturns] at hs; exact hs
      have h1 : landingCount 0 t 0 = 1 := ((isReturn0_iff_landingCount t).1 ht').2.1
      rw [landingCount_append_arrival _ hu',
        landingCount_append_zero 0 s ht'.2.1, h1]
      omega
  · intro hev
    rcases Nat.eq_zero_or_pos (landingCount q w 0) with h0 | hposw
    · exact Or.inl ((hzero w).2 h0)
    · right
      obtain ⟨u, rest, rfl, hu, hcnt⟩ := exists_first_arrival_prefix hposw
      have hodd : landingCount 0 rest 0 % 2 = 1 := by
        rw [landingCount_append_arrival rest hu] at hev
        omega
      obtain ⟨t, s, rfl, ht, hcnt2⟩ :=
        exists_first_return_prefix (w := rest) (by omega)
      refine mem_denote_concat.2 ⟨u, t ++ s, rfl,
        by rw [denote_opener hq]; exact hu, ?_⟩
      refine mem_denote_concat.2 ⟨t, s, rfl, (mem_frToken_iff_isReturn0 t).2 ht, ?_⟩
      rw [denote_evenReturns]
      have h1 : landingCount 0 t 0 = 1 := ((isReturn0_iff_landingCount t).1 ht).2.1
      have := landingCount_append_zero 0 (u := t) s ht.2.1
      show landingCount 0 s 0 % 2 = 0
      omega

-- BLUEPRINT: N-A4-FULL-034
theorem denote_evenLandings (q : Fin 3) :
    denote (evenLandings q) = landingParity q := by
  match q with
  | ⟨0, _⟩ =>
    change denote evenReturns = landingParity 0
    simpa [landingParity] using denote_evenReturns
  | ⟨1, _⟩ =>
    change denote (union (noLand opener1) (oddReturnsAfter opener1)) = landingParity 1
    rw [show opener1 = opener 1 from rfl]
    exact denote_evenLandings_ne_zero (q := 1) (by decide)
  | ⟨2, _⟩ =>
    change denote (union (noLand opener2) (oddReturnsAfter opener2)) = landingParity 2
    rw [show opener2 = opener 2 from rfl]
    exact denote_evenLandings_ne_zero (q := 2) (by decide)

theorem landingParity_hasHeightAtMost_one (q : Fin 3) :
    HasHeightAtMost (landingParity q) 1 :=
  ⟨evenLandings q, denote_evenLandings q, starHeight_evenLandings q⟩

/-! ### The landing cuts as `CutSystem`s

The same data, packaged in the reusable form of `GSH/Regex/CutParity.lean`.
Pattern-conditioned cut features (`N-A4-FULL-033`) differ from these only in
their `token`, so they will be built as further `CutSystem`s rather than by
repeating the factorisation arguments. -/

/-- Cuts at the returns to phase `0`. -/
def returnCut : CutSystem A4 where
  cnt0 := fun w => landingCount 0 w 0
  cnt1 := fun w => landingCount 0 w 0
  opener := frToken
  token := frToken
  opener_append := by
    intro u hu v
    have hru := (mem_frToken_iff_isReturn0 u).1 hu
    have h1 : landingCount 0 u 0 = 1 := ((isReturn0_iff_landingCount _).1 hru).2.1
    rw [landingCount_append_zero 0 v hru.2.1, h1]
  token_append := by
    intro u hu v
    have hru := (mem_frToken_iff_isReturn0 u).1 hu
    have h1 : landingCount 0 u 0 = 1 := ((isReturn0_iff_landingCount _).1 hru).2.1
    rw [landingCount_append_zero 0 v hru.2.1, h1]
  opener_peel := by
    intro w hw
    obtain ⟨u, v, hsplit, hu, _⟩ := exists_first_return_prefix hw
    exact ⟨u, v, hsplit, (mem_frToken_iff_isReturn0 u).2 hu⟩
  token_peel := by
    intro w hw
    obtain ⟨u, v, hsplit, hu, _⟩ := exists_first_return_prefix hw
    exact ⟨u, v, hsplit, (mem_frToken_iff_isReturn0 u).2 hu⟩

/-- Cuts at the landings on a nonzero phase `q`: the opener is the first
arrival at `q`, the token is again the first-return language. -/
def arrivalCut {q : Fin 3} (hq : q ≠ 0) : CutSystem A4 where
  cnt0 := fun w => landingCount q w 0
  cnt1 := fun w => landingCount 0 w 0
  opener := opener q
  token := frToken
  opener_append := by
    intro u hu v
    have hu' : IsArrival q u := by rw [denote_opener hq] at hu; exact hu
    exact landingCount_append_arrival v hu'
  token_append := by
    intro u hu v
    have hru := (mem_frToken_iff_isReturn0 u).1 hu
    have h1 : landingCount 0 u 0 = 1 := ((isReturn0_iff_landingCount _).1 hru).2.1
    rw [landingCount_append_zero 0 v hru.2.1, h1]
  opener_peel := by
    intro w hw
    obtain ⟨u, v, hsplit, hu, _⟩ := exists_first_arrival_prefix hw
    exact ⟨u, v, hsplit, by rw [denote_opener hq]; exact hu⟩
  token_peel := by
    intro w hw
    obtain ⟨u, v, hsplit, hu, _⟩ := exists_first_return_prefix hw
    exact ⟨u, v, hsplit, (mem_frToken_iff_isReturn0 u).2 hu⟩

/-- Cross-check of the generic framework: it re-proves `N-A4-FULL-034`. -/
example (q : Fin 3) : HasHeightAtMost (landingParity q) 1 := by
  by_cases hq : q = 0
  · subst hq
    exact returnCut.hasHeightAtMost_one starHeight_frToken starHeight_frToken
  · exact (arrivalCut hq).hasHeightAtMost_one (starHeight_opener q) starHeight_frToken

theorem landingParity_eq_typedCount_parity (q : Fin 3) :
    landingParity q = {w : Word A4 | typedCount (landingType q) w 0 % 2 = 0} := by
  ext w
  simp only [landingParity, Set.mem_setOf_eq, landingCount_eq_typedCount]

end A4CutFeature
end GSH
