import GSH.Regex.Sugar
import GSH.Regex.HeightClosure
import GSH.Regex.CountHeight
import GSH.Regex.Morphism
import GSH.Groups.A4Structure
import GSH.Results.A4LetterCut
import GSH.Results.A4MoverCut
import GSH.Recognition
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Full-alphabet word problem for `A₄`

Claim `A4-FULL-01` / `RESULTS.md` §5.5:

taking the alphabet to be all twelve elements of `A₄` and evaluating words by
multiplying letters in order, the identity fibre has generalized star height
at most one.

## Proof architecture

1. **Semidirect form** (`A4Structure`): every `g = vpart g · t^(phase g)` with
   `vpart g ∈ V₄`, and `evalList w = vAccum w · t^(phaseSum w)`.
2. **Identity criterion**: `evalList w = 1 ↔ wordPhaseNat w = 0 ∧ vAccum w = 1`.
3. **Phase language**: `{w | wordPhaseNat w = 0}` has height ≤ 1 via weighted
   letter-set counts mod 3 (`N-A4-FULL-030`).
4. **`V₄` accumulator**: `{w | vAccum w = 1}` has height ≤ 1 via the
   pattern-conditioned cut / forward–reverse GF(2) recovery of
   `scripts/research/a4_full12.py` (`N-A4-FULL-031`).
5. Boolean intersection preserves height ≤ 1 (`HeightClosure`).

Steps 1–3 and the closure toolkit are proved.  Step 4 remains as the
analytic content of the Python certificate.
-/

set_option autoImplicit false

open FreeMonoid

namespace GSH

universe u

namespace A4FullAlphabet

open A4Structure CountHeight

/-- Evaluation morphism: multiply the letters of a word in `A₄`. -/
def eval : FreeMonoid A4 →* A4 :=
  FreeMonoid.lift (fun g : A4 => g)

/-- Recognition of the identity by the full-alphabet evaluation map. -/
def recognition : Recognition A4 A4 where
  morphism := eval
  accepting := {1}

/-- Full-alphabet word-problem language `{ w : eval(w) = 1 }`. -/
def wordProblem : Language A4 := recognition.language

@[simp] theorem mem_wordProblem_iff (w : Word A4) :
    w ∈ wordProblem ↔ eval (FreeMonoid.ofList w) = 1 := by
  simp [wordProblem, Recognition.language, recognition]

theorem evalList_eq_prod (w : Word A4) : evalList w = w.prod := by
  induction w with
  | nil => simp [evalList]
  | cons g w ih => simp [evalList, List.prod_cons, ih]

theorem eval_ofList_eq_evalList (w : Word A4) :
    eval (FreeMonoid.ofList w) = evalList w := by
  simpa [eval, FreeMonoid.lift_apply, evalList_eq_prod] using
    (FreeMonoid.lift_ofList (fun g : A4 => g) w).symm

theorem mem_wordProblem_iff_evalList (w : Word A4) :
    w ∈ wordProblem ↔ evalList w = 1 := by
  rw [mem_wordProblem_iff, eval_ofList_eq_evalList]

theorem mem_wordProblem_iff_phase_vAccum (w : Word A4) :
    w ∈ wordProblem ↔ wordPhaseNat w = 0 ∧ vAccum w = 1 := by
  rw [mem_wordProblem_iff_evalList, evalList_eq_one_iff]

/-- Phase-zero language. -/
def phaseZero : Language A4 := {w | wordPhaseNat w = 0}

/-- Trivial `V₄`-accumulator language. -/
def vAccumOne : Language A4 := {w | vAccum w = 1}

theorem wordProblem_eq_phase_inter_vAccum :
    wordProblem = phaseZero ∩ vAccumOne := by
  ext w
  change w ∈ wordProblem ↔ wordPhaseNat w = 0 ∧ vAccum w = 1
  exact mem_wordProblem_iff_phase_vAccum w

/-! ## Phase-zero via mod-3 letter-set counts -/

-- `lettersOfPhase` / `mem_lettersOfPhase_iff` live in `A4Structure`.

theorem phaseSum_eq_weighted_counts (w : Word A4) :
    phaseSum w =
      countSet (lettersOfPhase 1) w + 2 * countSet (lettersOfPhase 2) w := by
  induction w with
  | nil => simp [phaseSum, countSet]
  | cons g gs ih =>
    rw [phaseSum_cons, countSet_cons, countSet_cons, ih]
    -- Case on whether `g` has phase 0, 1, or 2.
    have hp := phase g
    have hmem : ∀ e : Fin 3, g ∈ lettersOfPhase e ↔ phase g = e :=
      fun e => mem_lettersOfPhase_iff g e
    match h : phase g with
    | ⟨0, _⟩ =>
      have h1 : (g ∈ lettersOfPhase 1) = False := by
        simp [hmem 1, h]
      have h2 : (g ∈ lettersOfPhase 2) = False := by
        simp [hmem 2, h]
      -- phase.val = 0
      simp [h, h1, h2]
    | ⟨1, _⟩ =>
      have h1 : g ∈ lettersOfPhase 1 := (hmem 1).2 (by simpa using h)
      have h2 : g ∉ lettersOfPhase 2 := by
        intro hg; have := (hmem 2).1 hg; simp [h] at this
      simp [h, h1, h2]
      ring
    | ⟨2, _⟩ =>
      have h1 : g ∉ lettersOfPhase 1 := by
        intro hg; have := (hmem 1).1 hg; simp [h] at this
      have h2 : g ∈ lettersOfPhase 2 := (hmem 2).2 (by simpa using h)
      simp [h, h1, h2]
      ring

theorem wordPhaseNat_eq_weighted_mod (w : Word A4) :
    wordPhaseNat w =
      (countSet (lettersOfPhase 1) w + 2 * countSet (lettersOfPhase 2) w) % 3 := by
  rw [wordPhaseNat_eq_phaseSum, phaseSum_eq_weighted_counts]

theorem phaseZero_iff_weighted (w : Word A4) :
    w ∈ phaseZero ↔
      (countSet (lettersOfPhase 1) w + 2 * countSet (lettersOfPhase 2) w) % 3 = 0 := by
  simp [phaseZero, wordPhaseNat_eq_weighted_mod]

/--
Residues `(i,j)` with `i + 2j ≡ 0 (mod 3)` are exactly
`(0,0)`, `(1,1)`, `(2,2)`.
-/
theorem phaseZero_eq_diag_union :
    phaseZero =
      ({w | countSet (lettersOfPhase 1) w % 3 = 0} ∩
          {w | countSet (lettersOfPhase 2) w % 3 = 0}) ∪
      ({w | countSet (lettersOfPhase 1) w % 3 = 1} ∩
          {w | countSet (lettersOfPhase 2) w % 3 = 1}) ∪
      ({w | countSet (lettersOfPhase 1) w % 3 = 2} ∩
          {w | countSet (lettersOfPhase 2) w % 3 = 2}) := by
  ext w
  simp only [phaseZero_iff_weighted, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
  generalize hc1 : countSet (lettersOfPhase 1) w % 3 = i
  generalize hc2 : countSet (lettersOfPhase 2) w % 3 = j
  have hi : i < 3 := by omega
  have hj : j < 3 := by omega
  -- `(i + 2*j) % 3 = 0` with `i,j < 3` iff diagonal
  have hsum :
      (countSet (lettersOfPhase 1) w + 2 * countSet (lettersOfPhase 2) w) % 3 =
        (i + 2 * j) % 3 := by
    have h1 : countSet (lettersOfPhase 1) w = 3 * (countSet (lettersOfPhase 1) w / 3) + i := by
      omega
    have h2 : countSet (lettersOfPhase 2) w = 3 * (countSet (lettersOfPhase 2) w / 3) + j := by
      omega
    rw [h1, h2]
    ring_nf
    omega
  rw [hsum]
  clear hsum hc1 hc2
  match i, j with
  | 0, 0 => simp
  | 0, 1 => simp
  | 0, 2 => simp
  | 1, 0 => simp
  | 1, 1 => simp
  | 1, 2 => simp
  | 2, 0 => simp
  | 2, 1 => simp
  | 2, 2 => simp
  | _+3, _ => omega
  | _, _+3 => omega

theorem phaseZero_hasHeightAtMost_one : HasHeightAtMost phaseZero 1 := by
  rw [phaseZero_eq_diag_union]
  refine hasHeightAtMost_union
    (hasHeightAtMost_union
      (hasHeightAtMost_inter
        (countMod3_hasHeightAtMost_one (lettersOfPhase 1) 0)
        (countMod3_hasHeightAtMost_one (lettersOfPhase 2) 0))
      (hasHeightAtMost_inter
        (countMod3_hasHeightAtMost_one (lettersOfPhase 1) 1)
        (countMod3_hasHeightAtMost_one (lettersOfPhase 2) 1)))
    (hasHeightAtMost_inter
      (countMod3_hasHeightAtMost_one (lettersOfPhase 1) 2)
      (countMod3_hasHeightAtMost_one (lettersOfPhase 2) 2))

/-! ## `V₄` accumulator via typed-position parities

`A4Structure.vAccum_eq_one_iff_parity` reduces `vAccum w = 1` to the parities
of two typed position counts (positions classified by letter and entry
phase).  The remaining analytic content is that each typed parity language
has height ≤ 1 — the pattern-conditioned cut / forward–reverse GF(2)
certificate of `scripts/research/a4_full12.py`. -/

/-- Language of words whose `T`-typed position count is even. -/
def typedParity (T : A4 → Fin 3 → Bool) : Language A4 :=
  {w | typedCount T w 0 % 2 = 0}

theorem vAccumOne_eq_typedParity_inter :
    vAccumOne =
      typedParity (coordType bCoord1) ∩ typedParity (coordType bCoord2) := by
  ext w
  change vAccum w = 1 ↔ _
  rw [vAccum_eq_one_iff_parity]
  rfl

/-! ### Reduction of typed parities to single (letter, phase) pairs

Each position of a word carries exactly one `(letter, entry phase)` pair, so
`typedCount T` is the sum over the pairs selected by `T` of the single-pair
counts, and its parity is a GF(2) combination of the single-pair parities.
This matches the basis in which `scripts/research/a4_full12.py` certifies the
`N[g,p] mod 2` recovery. -/

/-- The twelve letters, listed by phase. -/
def allLetters : List A4 :=
  lettersOfPhase 0 ++ lettersOfPhase 1 ++ lettersOfPhase 2

/-- All 36 (letter, phase) pairs. -/
def allPairs : List (A4 × Fin 3) :=
  allLetters.flatMap (fun g => [(g, 0), (g, 1), (g, 2)])

theorem allPairs_nodup : allPairs.Nodup := by decide

theorem mem_allPairs : ∀ gp : A4 × Fin 3, gp ∈ allPairs := by decide

private theorem list_sum_map_add {ι : Type*} (l : List ι) (f g : ι → Nat) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

private theorem sum_indicator_filter {ι : Type*} [DecidableEq ι]
    (Q : ι → Bool) (x : ι) :
    ∀ l : List ι, l.Nodup → x ∈ l →
      ((l.filter Q).map (fun y => if x = y then (1 : Nat) else 0)).sum
        = if Q x then 1 else 0
  | [], _, hx => absurd hx (List.not_mem_nil)
  | a :: l, hnd, hx => by
    have ha : a ∉ l := (List.nodup_cons.mp hnd).1
    have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
    rcases List.mem_cons.mp hx with rfl | hxl
    · -- the unique occurrence is at the head
      have hzero :
          ((l.filter Q).map (fun y => if x = y then (1 : Nat) else 0)).sum = 0 := by
        apply List.sum_eq_zero
        intro n hn
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hn
        have hyl : y ∈ l := List.mem_of_mem_filter hy
        have hxy : x ≠ y := fun h => ha (h ▸ hyl)
        simp [hxy]
      by_cases hQ : Q x = true
      · simp [List.filter_cons, hQ, hzero]
      · simp [List.filter_cons, hQ, hzero]
    · -- the occurrence is in the tail
      have hxa : x ≠ a := fun h => ha (h ▸ hxl)
      have ih := sum_indicator_filter Q x l hnd' hxl
      by_cases hQ : Q a = true
      · simp [List.filter_cons, hQ, hxa, ih]
      · simp [List.filter_cons, hQ, ih]

private theorem indicator_pairType (T : A4 → Fin 3 → Bool) (g : A4) (p : Fin 3) :
    ((allPairs.filter fun gp => T gp.1 gp.2).map
        (fun gp => if pairType gp.1 gp.2 g p then (1 : Nat) else 0)).sum
      = if T g p then 1 else 0 := by
  have hcond : ∀ gp : A4 × Fin 3,
      (if pairType gp.1 gp.2 g p then (1 : Nat) else 0)
        = if (g, p) = gp then 1 else 0 := by
    intro gp
    by_cases h : (g, p) = gp
    · cases h
      simp [pairType]
    · have hne : ¬ (g = gp.1 ∧ p = gp.2) := fun hgp =>
        h (Prod.ext_iff.mpr ⟨hgp.1, hgp.2⟩)
      simp [pairType, hne, h]
  simp only [hcond]
  exact sum_indicator_filter (fun gp => T gp.1 gp.2) (g, p) allPairs
    allPairs_nodup (mem_allPairs _)

/-- Pointwise decomposition of a typed count into single-pair counts. -/
theorem typedCount_eq_pairSum (T : A4 → Fin 3 → Bool) :
    ∀ (w : Word A4) (q : Nat),
      typedCount T w q
        = ((allPairs.filter fun gp => T gp.1 gp.2).map
            (fun gp => typedCount (pairType gp.1 gp.2) w q)).sum
  | [], q => by
    symm
    apply List.sum_eq_zero
    intro n hn
    obtain ⟨gp, _, rfl⟩ := List.mem_map.mp hn
    rfl
  | g :: w, q => by
    have ih := typedCount_eq_pairSum T w (q + (phase g).val)
    simp only [typedCount_cons, ih, list_sum_map_add]
    congr 1
    exact (indicator_pairType T g ⟨q % 3, by omega⟩).symm

private theorem parity_listSum {ι : Type*} (F : ι → Word A4 → Nat)
    (h : ∀ i : ι, HasHeightAtMost {w : Word A4 | F i w % 2 = 0} 1) :
    ∀ l : List ι,
      HasHeightAtMost {w : Word A4 | (l.map fun i => F i w).sum % 2 = 0} 1
  | [] => by
    have hset : {w : Word A4 | (([] : List ι).map fun i => F i w).sum % 2 = 0}
        = Set.univ := by
      ext w
      simp
    rw [hset]
    exact hasHeightAtMost_of_le hasHeightAtMost_univ (by omega)
  | i :: l => by
    have ih := parity_listSum F h l
    have hset : {w : Word A4 | ((i :: l).map fun j => F j w).sum % 2 = 0}
        = {w : Word A4 | (F i w + (l.map fun j => F j w).sum) % 2 = 0} := by
      ext w
      simp
    rw [hset]
    exact hasHeightAtMost_parity_add (f := F i)
      (g := fun w => (l.map fun j => F j w).sum) (h i) ih

/--
Single-pair parity `N[g,p] mod 2` (occurrences of letter `g` at entry phase
`p`) is a height ≤ 1 language: pattern-conditioned cut tokens plus
forward/reverse GF(2) recovery (`RESULTS.md` §5.5, `scripts/research/a4_full12.py`).

Both cases are closed (2026-07-28).  The unconditioned cut layer gives, for
every `q : Fin 3`, that `{w | landingCount q w 0 even}` has height ≤ 1
(`GSH.A4CutFeature.landingParity_hasHeightAtMost_one`).  For `phase g = 0`
the theorem is `GSH.A4LetterCut.fillerPairParity_hasHeightAtMost_one` (cut
core `{g}*`, visibly star-free).  For `phase g ≠ 0` it is
`GSH.A4MoverCut.moverPairParity_hasHeightAtMost_one`, whose recovery is the
*phase-free* GF(2) identity (mod 2, with `ε = phase g`)

    N[g,p] = |w|_g + occL (p+2ε) + occR (p+ε)

— `occL p` counts occurrences of `g` at entry phase `p` not preceded by `g`
and `occR p` those not followed by `g`; the two are exchanged by reversal.
Both parities come from cut systems whose cut core is the aperiodic language
`cutCore g`, and *that* is where Schützenberger's theorem enters: no explicit
star-free expression for `cutCore g` was ever found (see the failed searches
recorded in `N-A4-FULL-033c`), so `GSH.A4MoverCut.starFree_cutCore` instead
exhibits the accepting automaton and proves it counter-free, and
`GSH/StarFree/TransitionMonoid.lean` converts that into star-freeness.
-/
-- BLUEPRINT: N-A4-FULL-033
theorem pairParity_hasHeightAtMost_one (g : A4) (p : Fin 3) :
    HasHeightAtMost (typedParity (pairType g p)) 1 := by
  by_cases hg : phase g = 0
  · -- filler: cut core `{g}*` (`N-A4-FULL-033a`)
    exact A4LetterCut.fillerPairParity_hasHeightAtMost_one hg p
  · -- mover: cut system + phase-free GF(2) recovery (`N-A4-FULL-033d`, `033e`),
    -- on the counter-free cut-core automaton (`N-A4-FULL-033c`)
    exact A4MoverCut.moverPairParity_hasHeightAtMost_one hg p

/--
Every typed-position parity language over `(letter, entry phase)` pairs has
height ≤ 1 (`N-A4-FULL-032`), by GF(2) decomposition into single-pair
parities (`N-A4-FULL-033`).
-/
theorem typedParity_hasHeightAtMost_one (T : A4 → Fin 3 → Bool) :
    HasHeightAtMost (typedParity T) 1 := by
  have hdecomp : typedParity T =
      {w : Word A4 |
        ((allPairs.filter fun gp => T gp.1 gp.2).map
          (fun gp => typedCount (pairType gp.1 gp.2) w 0)).sum % 2 = 0} := by
    ext w
    simp only [typedParity, Set.mem_setOf_eq, typedCount_eq_pairSum T w 0]
  rw [hdecomp]
  exact parity_listSum
    (fun gp : A4 × Fin 3 => fun w => typedCount (pairType gp.1 gp.2) w 0)
    (fun gp => pairParity_hasHeightAtMost_one gp.1 gp.2)
    (allPairs.filter fun gp => T gp.1 gp.2)

/--
`vAccum w = 1` is a height ≤ 1 language, via the typed-parity reduction and
the cut/GF(2) certificate.
-/
-- BLUEPRINT: N-A4-FULL-031
theorem vAccumOne_hasHeightAtMost_one : HasHeightAtMost vAccumOne 1 := by
  rw [vAccumOne_eq_typedParity_inter]
  exact hasHeightAtMost_inter
    (typedParity_hasHeightAtMost_one _) (typedParity_hasHeightAtMost_one _)

/--
`RESULTS.md` §5.5: the full twelve-letter `A₄` word problem has generalized
star height at most one.
-/
-- BLUEPRINT: N-A4-FULL-001
theorem wordProblem_hasHeightAtMost_one :
    HasHeightAtMost wordProblem 1 := by
  rw [wordProblem_eq_phase_inter_vAccum]
  exact hasHeightAtMost_inter phaseZero_hasHeightAtMost_one vAccumOne_hasHeightAtMost_one

/-- A morphism out of a free monoid evaluates a word by multiplying the
images of its letters. -/
theorem morphism_eq_evalList {α : Type*} (φ : FreeMonoid α →* A4) :
    ∀ w : Word α,
      φ (FreeMonoid.ofList w) = evalList (w.map (fun a => φ (FreeMonoid.of a)))
  | [] => by
    have h : FreeMonoid.ofList ([] : Word α) = 1 := rfl
    rw [h, map_one]
    rfl
  | a :: l => by
    have hsplit : FreeMonoid.ofList (a :: l)
        = FreeMonoid.of a * FreeMonoid.ofList l := rfl
    rw [hsplit, map_mul, morphism_eq_evalList φ l]
    rfl

/--
Every monoid morphism from a free monoid on a finite alphabet into `A₄` has
identity fibre of generalized star height ≤ 1.

The morphism factors through the letter-to-letter map `a ↦ φ (of a)`, so the
fibre is the inverse image of the full-alphabet word problem along an
*alphabetic* morphism, and `hasHeightAtMost_comap` transports the bound.
This is the self-contained replacement for the appeal to `PST-CL-01`.
-/
-- N-A4-ANYGEN-001 (closed)
theorem any_morphism_identity_fibre_height_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (φ : FreeMonoid α →* A4) :
    HasHeightAtMost {w : Word α | φ (FreeMonoid.ofList w) = 1} 1 := by
  have hset : {w : Word α | φ (FreeMonoid.ofList w) = 1}
      = Language.comap (fun a => φ (FreeMonoid.of a)) wordProblem := by
    ext w
    rw [Language.mem_comap_iff]
    simp only [Set.mem_setOf_eq, mem_wordProblem_iff_evalList]
    rw [morphism_eq_evalList φ w]
  rw [hset]
  exact hasHeightAtMost_comap _ wordProblem_hasHeightAtMost_one

/-- Package of the full-alphabet statement as a `Recognition` height claim. -/
theorem recognition_hasHeightAtMost_one :
    HasHeightAtMost recognition.language 1 :=
  wordProblem_hasHeightAtMost_one

/-! ## The `A₄` milestone

`GSH/Height/FullAlphabet.lean` proves the reduction *full-alphabet identity
fibre ⇒ every recognized language* (`heightOneForGroup_of_fullIdentityFiber`,
with the exact quantifiers of `HeightOneForGroup`: every finite alphabet,
every morphism, every accepting subset).  Its premise for `A₄` is exactly the
theorem proved above, so the two compose into a Lean proof of the milestone
`A4HeightOneTarget` — previously the `A_4` premise was a human/computational
proof only (obligation `L-A4-001`). -/

theorem wordProblem_eq_fullIdentityFiber :
    wordProblem = fullIdentityFiber A4 := by
  ext w
  rw [mem_wordProblem_iff, mem_fullIdentityFiber_iff, eval_ofList_eq_evalList,
    evalList_eq_prod]

/-- **Every language recognized by `A₄` has generalized star height at most
one**, with the quantifiers of `HeightOneForGroup`. -/
theorem heightOneForGroup_A4 : HeightOneForGroup.{u} A4 :=
  heightOneForGroup_of_fullIdentityFiber
    (wordProblem_eq_fullIdentityFiber ▸ wordProblem_hasHeightAtMost_one)

/-- The named milestone of `GSH/Groups.lean`. -/
theorem a4HeightOneTarget : A4HeightOneTarget.{u} := heightOneForGroup_A4

end A4FullAlphabet
end GSH
