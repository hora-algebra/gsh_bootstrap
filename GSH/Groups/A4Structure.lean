import GSH.Groups
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Semidirect decomposition of `A₄`

Concrete model matching `scripts/a4_full12.py`:

- `t = (0 1 2)` (fixes `3`)
- `V₄ = {1, (0 1)(2 3), (0 2)(1 3), (0 3)(1 2)}`
- every `g ∈ A₄` factors uniquely as `v * t^e` with `v ∈ V₄`, `e ∈ {0,1,2}`
-/

set_option autoImplicit false

open Equiv Equiv.Perm

namespace GSH
namespace A4Structure

/-- The 3-cycle `(0 1 2)` inside `A₄`. -/
def t : A4 := ⟨c[0, 1, 2], mem_alternatingGroup.2 (by decide)⟩

theorem t_pow_three : t ^ 3 = 1 := by
  apply Subtype.ext
  decide

/-- The four Klein-four elements. -/
def v4 : Fin 4 → A4
  | 0 => 1
  | 1 => ⟨c[0, 1] * c[2, 3], mem_alternatingGroup.2 (by decide)⟩
  | 2 => ⟨c[0, 2] * c[1, 3], mem_alternatingGroup.2 (by decide)⟩
  | 3 => ⟨c[0, 3] * c[1, 2], mem_alternatingGroup.2 (by decide)⟩

def IsV4 (g : A4) : Prop := ∃ i : Fin 4, v4 i = g

instance : DecidablePred IsV4 := fun _ =>
  inferInstanceAs (Decidable (∃ i : Fin 4, v4 i = _))

theorem v4_one : IsV4 (1 : A4) := ⟨0, rfl⟩

/-- Exhaustion: every element is some `v4 i * t^e`. -/
theorem exists_normal_form : ∀ g : A4, ∃ i : Fin 4, ∃ e : Fin 3, g = v4 i * t ^ e.val := by
  decide

/-- Computable phase via exhaustive search. -/
def phase (g : A4) : Fin 3 :=
  if ∃ i : Fin 4, g = v4 i then 0
  else if ∃ i : Fin 4, g = v4 i * t then 1
  else 2

/-- `V₄` component in the normal form `g = vpart g * t^(phase g)`. -/
def vpart (g : A4) : A4 :=
  match phase g with
  | 0 => g
  | 1 => g * t ^ 2
  | 2 => g * t

theorem vpart_isV4 : ∀ g : A4, IsV4 (vpart g) := by
  decide

theorem normal_form : ∀ g : A4, g = vpart g * t ^ (phase g).val := by
  decide

theorem phase_of_normal_form :
    ∀ g : A4, ∀ i : Fin 4, ∀ e : Fin 3,
      g = v4 i * t ^ e.val → phase g = e := by
  decide

/-- Left-to-right list evaluation. -/
def evalList : Word A4 → A4
  | [] => 1
  | g :: w => g * evalList w

theorem evalList_nil : evalList ([] : Word A4) = 1 := rfl

theorem evalList_cons (g : A4) (w : Word A4) :
    evalList (g :: w) = g * evalList w := rfl

theorem evalList_append (u v : Word A4) :
    evalList (u ++ v) = evalList u * evalList v := by
  induction u with
  | nil => simp [evalList]
  | cons _ _ ih => simp [evalList, ih, mul_assoc]

theorem evalList_singleton (g : A4) : evalList [g] = g := by
  simp [evalList]

/-- Additive phase of a word (`ℕ`, already reduced mod 3). -/
def wordPhaseNat (w : Word A4) : Nat :=
  (w.map fun g => (phase g).val).sum % 3

theorem wordPhaseNat_nil : wordPhaseNat ([] : Word A4) = 0 := by
  simp [wordPhaseNat]

theorem wordPhaseNat_cons (g : A4) (w : Word A4) :
    wordPhaseNat (g :: w) =
      ((phase g).val + (w.map fun x => (phase x).val).sum) % 3 := by
  simp [wordPhaseNat]

/-- Conjugation by powers of `t` preserves `V₄`. -/
theorem IsV4.mul {a b : A4} (ha : IsV4 a) (hb : IsV4 b) : IsV4 (a * b) := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  revert i j
  decide

theorem IsV4.conj_t {v : A4} (hv : IsV4 v) : IsV4 (t * v * t ^ 2) := by
  obtain ⟨i, rfl⟩ := hv
  revert i
  decide

theorem IsV4.conj_t2 {v : A4} (hv : IsV4 v) : IsV4 (t ^ 2 * v * t) := by
  obtain ⟨i, rfl⟩ := hv
  revert i
  decide

theorem IsV4.conj_t_pow_le2 {v : A4} (hv : IsV4 v) (e : Fin 3) :
    IsV4 (t ^ e.val * v * t ^ ((3 - e.val) % 3)) := by
  fin_cases e
  · simpa [pow_zero] using hv
  · simpa using hv.conj_t
  · simpa using hv.conj_t2

/-- Raw (unreduced) phase sum. -/
def phaseSum (w : Word A4) : Nat :=
  (w.map fun g => (phase g).val).sum

theorem wordPhaseNat_eq_phaseSum (w : Word A4) :
    wordPhaseNat w = phaseSum w % 3 := rfl

theorem phaseSum_cons (g : A4) (w : Word A4) :
    phaseSum (g :: w) = (phase g).val + phaseSum w := by
  simp [phaseSum]

/-- Right inverse of `t^e` for `e < 3`. -/
theorem t_pow_right_inv (e : Fin 3) :
    t ^ ((3 - e.val) % 3) * t ^ e.val = 1 := by
  fin_cases e
  · simp
  · have : t ^ 2 * t = t ^ 3 := by rw [← pow_succ]
    simpa [this] using t_pow_three
  · have : t * t ^ 2 = t ^ 3 := by
      calc
        t * t ^ 2 = t ^ 1 * t ^ 2 := by simp
        _ = t ^ (1 + 2) := by rw [← pow_add]
        _ = t ^ 3 := by norm_num
    simpa [this] using t_pow_three

theorem t_pow_mul_shift (e : Fin 3) (x : A4) (P : Nat) :
    t ^ e.val * x * t ^ P =
      (t ^ e.val * x * t ^ ((3 - e.val) % 3)) * t ^ (e.val + P) := by
  have hinv := t_pow_right_inv e
  calc
    t ^ e.val * x * t ^ P =
        t ^ e.val * x * (t ^ ((3 - e.val) % 3) * t ^ e.val) * t ^ P := by
          simp [hinv]
    _ = t ^ e.val * x * t ^ ((3 - e.val) % 3) * (t ^ e.val * t ^ P) := by
          simp [mul_assoc]
    _ = (t ^ e.val * x * t ^ ((3 - e.val) % 3)) * t ^ (e.val + P) := by
          simp [pow_add, mul_assoc]

theorem t_pow_mod (n : Nat) : t ^ n = t ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3]
  rw [pow_add, pow_mul, t_pow_three]
  simp

theorem t_pow_cancel_mod (n : Nat) :
    t ^ n * t ^ ((3 - n % 3) % 3) = 1 := by
  rw [← pow_add, t_pow_mod (n + ((3 - n % 3) % 3))]
  have : (n + ((3 - n % 3) % 3)) % 3 = 0 := by omega
  simp [this]

/-- Evaluation lands in the coset `V₄ · t^(phaseSum w)`. -/
theorem evalList_eq_v_t_pow :
    ∀ w : Word A4, ∃ v : A4, IsV4 v ∧ evalList w = v * t ^ phaseSum w := by
  intro w
  induction w with
  | nil =>
    exact ⟨1, v4_one, by simp [evalList, phaseSum]⟩
  | cons g w ih =>
    obtain ⟨vw, hvw, hw⟩ := ih
    have hg : g = vpart g * t ^ (phase g).val := normal_form g
    refine ⟨vpart g * (t ^ (phase g).val * vw * t ^ ((3 - (phase g).val) % 3)),
      (vpart_isV4 g).mul (hvw.conj_t_pow_le2 (phase g)), ?_⟩
    have hstep :
        evalList (g :: w) =
          vpart g * (t ^ (phase g).val * vw * t ^ phaseSum w) := by
      conv_lhs => rw [evalList_cons, hg, hw]
      simp [mul_assoc]
    calc
      evalList (g :: w)
          = vpart g * (t ^ (phase g).val * vw * t ^ phaseSum w) := hstep
      _ = vpart g *
            ((t ^ (phase g).val * vw * t ^ ((3 - (phase g).val) % 3)) *
              t ^ ((phase g).val + phaseSum w)) := by
            rw [t_pow_mul_shift]
      _ = (vpart g * (t ^ (phase g).val * vw * t ^ ((3 - (phase g).val) % 3))) *
            t ^ ((phase g).val + phaseSum w) := by
            simp [mul_assoc]
      _ = (vpart g * (t ^ (phase g).val * vw * t ^ ((3 - (phase g).val) % 3))) *
            t ^ phaseSum (g :: w) := by
            simp [phaseSum_cons]

/-- The product lies in the coset `V₄ · t^P` (`P = wordPhaseNat`). -/
theorem evalList_phase_coset (w : Word A4) :
    IsV4 (evalList w * t ^ ((3 - wordPhaseNat w) % 3)) := by
  obtain ⟨v, hv, hw⟩ := evalList_eq_v_t_pow w
  rw [hw, wordPhaseNat_eq_phaseSum, mul_assoc, t_pow_cancel_mod, mul_one]
  exact hv

/-- If the product is `1`, the total phase is `0`. -/
theorem evalList_eq_one_phase_zero (w : Word A4) (h : evalList w = 1) :
    wordPhaseNat w = 0 := by
  obtain ⟨v, hv, hw⟩ := evalList_eq_v_t_pow w
  have hw' : v * t ^ phaseSum w = 1 := hw.symm.trans h
  obtain ⟨i, hi⟩ := hv
  have hS : phaseSum w % 3 < 3 := Nat.mod_lt _ (by decide)
  set e : Fin 3 := ⟨phaseSum w % 3, hS⟩
  have : v4 i * t ^ e.val = 1 := by
    calc
      v4 i * t ^ e.val = v * t ^ (phaseSum w % 3) := by simp [e, hi]
      _ = v * t ^ phaseSum w := by rw [← t_pow_mod]
      _ = 1 := hw'
  have hpow : ∀ e : Fin 3, ∀ i : Fin 4, v4 i * t ^ e.val = 1 → e = 0 := by
    decide
  have he : e = 0 := hpow e i this
  simpa [wordPhaseNat_eq_phaseSum, e] using congrArg Fin.val he

/-- Unique normal-form coefficients: `v * t^e = 1` forces `e = 0` and `v = 1`. -/
theorem v4_t_pow_eq_one :
    ∀ v : A4, ∀ e : Fin 3, IsV4 v → v * t ^ e.val = 1 → e = 0 ∧ v = 1 := by
  decide

/-- Canonical `V₄` accumulator of a word (well-defined by `evalList_eq_v_t_pow`). -/
noncomputable def vAccum (w : Word A4) : A4 :=
  Classical.choose (evalList_eq_v_t_pow w)

theorem vAccum_isV4 (w : Word A4) : IsV4 (vAccum w) :=
  (Classical.choose_spec (evalList_eq_v_t_pow w)).1

theorem evalList_eq_vAccum_t (w : Word A4) :
    evalList w = vAccum w * t ^ phaseSum w :=
  (Classical.choose_spec (evalList_eq_v_t_pow w)).2

/-- Full identity criterion. -/
theorem evalList_eq_one_iff (w : Word A4) :
    evalList w = 1 ↔ wordPhaseNat w = 0 ∧ vAccum w = 1 := by
  constructor
  · intro h
    refine ⟨evalList_eq_one_phase_zero w h, ?_⟩
    have hw := evalList_eq_vAccum_t w
    have : vAccum w * t ^ phaseSum w = 1 := hw.symm.trans h
    have hS : phaseSum w % 3 < 3 := Nat.mod_lt _ (by decide)
    set e : Fin 3 := ⟨phaseSum w % 3, hS⟩
    have ht : t ^ phaseSum w = t ^ e.val := by
      simpa [e] using t_pow_mod (phaseSum w)
    have : vAccum w * t ^ e.val = 1 := by simpa [ht] using this
    exact (v4_t_pow_eq_one (vAccum w) e (vAccum_isV4 w) this).2
  · rintro ⟨hP, hv⟩
    have hw := evalList_eq_vAccum_t w
    have ht : t ^ phaseSum w = (1 : A4) := by
      have : phaseSum w % 3 = 0 := by simpa [wordPhaseNat_eq_phaseSum] using hP
      simpa [t_pow_mod, this] using rfl
    simpa [hw, hv, ht] using rfl

/-! ## Conjugation product formula for the `V₄` accumulator

`evalList w = (Π_j τ^{P_j}(vpart g_j)) · t^{phaseSum w}` where `P_j` is the
entry phase of the `j`-th letter and `τ^p(v) = t^p v t^{-p}`.  Since `V₄` is
elementary abelian of exponent 2, the accumulator only depends on the
parities of typed position counts. -/

/-- Conjugation of `v` by `t^p`, inverse realized as a positive power. -/
def conjT (p : Nat) (v : A4) : A4 :=
  t ^ (p % 3) * v * t ^ ((3 - p % 3) % 3)

theorem conjT_mod (p : Nat) (v : A4) : conjT (p % 3) v = conjT p v := by
  unfold conjT
  rw [Nat.mod_mod_of_dvd p dvd_rfl]

theorem isV4_conjT {v : A4} (hv : IsV4 v) (p : Nat) : IsV4 (conjT p v) := by
  have h := hv.conj_t_pow_le2 ⟨p % 3, by omega⟩
  simpa [conjT] using h

/-- Commutation: `t^p · v = τ^p(v) · t^p`. -/
theorem t_pow_mul_eq_conjT (p : Nat) (v : A4) :
    t ^ p * v = conjT p v * t ^ p := by
  have hexp : ((3 - p % 3) % 3 + p) % 3 = 0 := by omega
  have h1 : t ^ ((3 - p % 3) % 3) * t ^ p = 1 := by
    rw [← pow_add, t_pow_mod, hexp, pow_zero]
  calc t ^ p * v
      = t ^ (p % 3) * v := by rw [← t_pow_mod]
    _ = t ^ (p % 3) * v * (t ^ ((3 - p % 3) % 3) * t ^ p) := by rw [h1, mul_one]
    _ = conjT p v * t ^ p := by simp [conjT, mul_assoc]

/-- Accumulated `V₄` component of a word entered at phase `q`. -/
def vAccumAux : Word A4 → Nat → A4
  | [], _ => 1
  | g :: w, q => conjT q (vpart g) * vAccumAux w (q + (phase g).val)

theorem isV4_vAccumAux : ∀ (w : Word A4) (q : Nat), IsV4 (vAccumAux w q)
  | [], _ => v4_one
  | g :: w, q =>
    (isV4_conjT (vpart_isV4 g) q).mul (isV4_vAccumAux w (q + (phase g).val))

/-- Product formula: shifting by `t^q` and evaluating accumulates conjugated
`V₄` parts. -/
theorem t_pow_mul_evalList : ∀ (w : Word A4) (q : Nat),
    t ^ q * evalList w = vAccumAux w q * t ^ (q + phaseSum w)
  | [], q => by simp [evalList, vAccumAux, phaseSum]
  | g :: w, q => by
    have ih := t_pow_mul_evalList w (q + (phase g).val)
    have hg : g * evalList w = vpart g * t ^ (phase g).val * evalList w := by
      rw [← normal_form g]
    calc t ^ q * evalList (g :: w)
        = t ^ q * (vpart g * t ^ (phase g).val * evalList w) := by
          rw [evalList_cons, hg]
      _ = (t ^ q * vpart g) * (t ^ (phase g).val * evalList w) := by
          simp [mul_assoc]
      _ = (conjT q (vpart g) * t ^ q) * (t ^ (phase g).val * evalList w) := by
          rw [t_pow_mul_eq_conjT]
      _ = conjT q (vpart g) * (t ^ (q + (phase g).val) * evalList w) := by
          simp [pow_add, mul_assoc]
      _ = conjT q (vpart g) *
            (vAccumAux w (q + (phase g).val) * t ^ (q + (phase g).val + phaseSum w)) := by
          rw [ih]
      _ = vAccumAux (g :: w) q * t ^ (q + phaseSum (g :: w)) := by
          rw [phaseSum_cons]
          show conjT q (vpart g) * (vAccumAux w (q + (phase g).val) * _) = _
          simp [vAccumAux, mul_assoc, Nat.add_assoc]

/-- The canonical accumulator agrees with the explicit product. -/
theorem vAccum_eq_vAccumAux (w : Word A4) : vAccum w = vAccumAux w 0 := by
  have h1 : evalList w = vAccumAux w 0 * t ^ phaseSum w := by
    simpa using t_pow_mul_evalList w 0
  have h2 := evalList_eq_vAccum_t w
  exact mul_right_cancel (h2.symm.trans h1)

/-! ### GF(2) coordinates on `V₄` -/

/-- First GF(2) coordinate: detects `v4 1` and `v4 3`. -/
def bCoord1 (v : A4) : Bool := decide (v = v4 1 ∨ v = v4 3)

/-- Second GF(2) coordinate: detects `v4 2` and `v4 3`. -/
def bCoord2 (v : A4) : Bool := decide (v = v4 2 ∨ v = v4 3)

theorem bCoord1_mul_v4 :
    ∀ i j : Fin 4, bCoord1 (v4 i * v4 j) = Bool.xor (bCoord1 (v4 i)) (bCoord1 (v4 j)) := by
  decide

theorem bCoord2_mul_v4 :
    ∀ i j : Fin 4, bCoord2 (v4 i * v4 j) = Bool.xor (bCoord2 (v4 i)) (bCoord2 (v4 j)) := by
  decide

theorem bCoord1_mul {u v : A4} (hu : IsV4 u) (hv : IsV4 v) :
    bCoord1 (u * v) = Bool.xor (bCoord1 u) (bCoord1 v) := by
  obtain ⟨i, rfl⟩ := hu
  obtain ⟨j, rfl⟩ := hv
  exact bCoord1_mul_v4 i j

theorem bCoord2_mul {u v : A4} (hu : IsV4 u) (hv : IsV4 v) :
    bCoord2 (u * v) = Bool.xor (bCoord2 u) (bCoord2 v) := by
  obtain ⟨i, rfl⟩ := hu
  obtain ⟨j, rfl⟩ := hv
  exact bCoord2_mul_v4 i j

/-- On `V₄`, both coordinates vanish exactly at the identity. -/
theorem v4_eq_one_iff_bCoord :
    ∀ i : Fin 4, (v4 i = 1) ↔ (bCoord1 (v4 i) = false ∧ bCoord2 (v4 i) = false) := by
  decide

/-! ### Typed position counts -/

/-- Number of positions of `w` whose (letter, entry-phase) pair satisfies `T`,
starting at entry phase `q`. -/
def typedCount (T : A4 → Fin 3 → Bool) : Word A4 → Nat → Nat
  | [], _ => 0
  | g :: w, q =>
    (if T g ⟨q % 3, by omega⟩ then 1 else 0) + typedCount T w (q + (phase g).val)

theorem typedCount_nil (T : A4 → Fin 3 → Bool) (q : Nat) :
    typedCount T [] q = 0 := rfl

theorem typedCount_cons (T : A4 → Fin 3 → Bool) (g : A4) (w : Word A4) (q : Nat) :
    typedCount T (g :: w) q =
      (if T g ⟨q % 3, by omega⟩ then 1 else 0)
        + typedCount T w (q + (phase g).val) := rfl

theorem typedCount_append (T : A4 → Fin 3 → Bool) :
    ∀ (u v : Word A4) (q : Nat),
      typedCount T (u ++ v) q = typedCount T u q + typedCount T v (q + phaseSum u)
  | [], v, q => by simp [typedCount_nil, phaseSum]
  | g :: u, v, q => by
    have ih := typedCount_append T u v (q + (phase g).val)
    simp only [List.cons_append, typedCount_cons, ih, phaseSum_cons]
    have harg : q + (phase g).val + phaseSum u = q + ((phase g).val + phaseSum u) := by
      omega
    rw [harg]
    omega

theorem typedCount_singleton (T : A4 → Fin 3 → Bool) (g : A4) (q : Nat) :
    typedCount T [g] q = if T g ⟨q % 3, by omega⟩ then 1 else 0 := by
  simp [typedCount_cons, typedCount_nil]

theorem phaseSum_reverse (w : Word A4) : phaseSum w.reverse = phaseSum w := by
  simp [phaseSum]

/-! ### Single-pair types and the reversal identity -/

/-- Single-pair type: positions with letter `g` at entry phase `p`. -/
def pairType (g : A4) (p : Fin 3) : A4 → Fin 3 → Bool :=
  fun h q => decide (h = g ∧ q = p)

/-- Phase subtraction `p - s` on `Fin 3`. -/
def subPhase (p : Fin 3) (s : Nat) : Fin 3 :=
  ⟨(p.val + 3 - s % 3) % 3, by omega⟩

/-- Shifting the start phase shifts the pair phase of a single-pair count. -/
theorem typedCount_pairType_shift (g : A4) (p : Fin 3) (s : Nat) :
    ∀ (w : Word A4) (q : Nat),
      typedCount (pairType g p) w (q + s)
        = typedCount (pairType g (subPhase p s)) w q
  | [], _ => rfl
  | h :: w, q => by
    have ih := typedCount_pairType_shift g p s w (q + (phase h).val)
    simp only [typedCount_cons]
    have harg : q + s + (phase h).val = q + (phase h).val + s := by omega
    rw [harg, ih]
    congr 1
    by_cases hg : h = g
    · have hp := p.isLt
      have hiff : ((⟨(q + s) % 3, by omega⟩ : Fin 3) = p)
          ↔ ((⟨q % 3, by omega⟩ : Fin 3) = subPhase p s) := by
        rw [Fin.ext_iff, Fin.ext_iff]
        simp only [subPhase]
        omega
      simp [pairType, hg, hiff]
    · simp [pairType, hg]

/--
Reversed entry phase: the `r`-entries of the reversed word are the
`(P - ε_g - r)`-entries of the original word, `P` the total phase
(`RESULTS.md` §5.5, key 2).
-/
def revPairPhase (g : A4) (r : Fin 3) (P : Nat) : Fin 3 :=
  ⟨(P % 3 + 6 - ((phase g).val + r.val)) % 3, by omega⟩

/-- Reversal identity for single-pair counts. -/
theorem typedCount_pairType_reverse (g : A4) (r : Fin 3) :
    ∀ w : Word A4,
      typedCount (pairType g r) w.reverse 0
        = typedCount (pairType g (revPairPhase g r (phaseSum w))) w 0
  | [] => rfl
  | h :: w => by
    have ih := typedCount_pairType_reverse g r w
    have hr := r.isLt
    have hh := (phase h).isLt
    have hg' := (phase g).isLt
    rw [List.reverse_cons, typedCount_append, ih, typedCount_singleton,
      Nat.zero_add, phaseSum_reverse, phaseSum_cons, typedCount_cons]
    -- shift the tail count of the RHS back to start phase 0
    have hshift := typedCount_pairType_shift g
      (revPairPhase g r ((phase h).val + phaseSum w)) ((phase h).val) w 0
    rw [hshift]
    -- (a) the shifted pair phase is the reversal phase for the tail
    have hsub : subPhase (revPairPhase g r ((phase h).val + phaseSum w))
        ((phase h).val) = revPairPhase g r (phaseSum w) := by
      apply Fin.ext
      simp only [subPhase, revPairPhase]
      omega
    rw [hsub]
    -- (b) head indicators agree
    have hind : (if pairType g r h ⟨phaseSum w % 3, by omega⟩ then (1 : Nat) else 0)
        = if pairType g (revPairPhase g r ((phase h).val + phaseSum w)) h
            ⟨0 % 3, by omega⟩ then 1 else 0 := by
      by_cases hgh : h = g
      · subst hgh
        have hiff : ((⟨phaseSum w % 3, by omega⟩ : Fin 3) = r)
            ↔ ((⟨0 % 3, by omega⟩ : Fin 3)
                = revPairPhase h r ((phase h).val + phaseSum w)) := by
          rw [Fin.ext_iff, Fin.ext_iff]
          simp only [revPairPhase]
          omega
        simp [pairType, hiff]
      · simp [pairType, hgh]
    rw [hind]
    omega

/-- Typed table extracting coordinate `b` of the conjugated `V₄` part. -/
def coordType (b : A4 → Bool) (g : A4) (p : Fin 3) : Bool :=
  b (conjT p.val (vpart g))

private theorem xor_decide_parity (c : Bool) (n : Nat) :
    Bool.xor c (decide (n % 2 = 1)) = decide (((if c then 1 else 0) + n) % 2 = 1) := by
  cases c
  · simp
  · simp only [Bool.true_xor, if_true, ← decide_not]
    exact decide_eq_decide.2 (by omega)

/-- Coordinates of the accumulator are typed-count parities. -/
theorem bCoord_vAccumAux (b : A4 → Bool)
    (hmul : ∀ {u v : A4}, IsV4 u → IsV4 v → b (u * v) = Bool.xor (b u) (b v))
    (hone : b 1 = false) :
    ∀ (w : Word A4) (q : Nat),
      b (vAccumAux w q) = decide (typedCount (coordType b) w q % 2 = 1)
  | [], q => by simp [vAccumAux, typedCount, hone]
  | g :: w, q => by
    have ih := bCoord_vAccumAux b hmul hone w (q + (phase g).val)
    have hxor : b (vAccumAux (g :: w) q)
        = Bool.xor (b (conjT q (vpart g))) (b (vAccumAux w (q + (phase g).val))) :=
      hmul (isV4_conjT (vpart_isV4 g) q) (isV4_vAccumAux w _)
    have hval : b (conjT q (vpart g)) = coordType b g ⟨q % 3, by omega⟩ := by
      unfold coordType
      rw [conjT_mod]
    rw [hxor, hval, ih]
    exact xor_decide_parity _ _

/-- Identity criterion for the accumulator through typed parities. -/
theorem vAccum_eq_one_iff_parity (w : Word A4) :
    vAccum w = 1 ↔
      typedCount (coordType bCoord1) w 0 % 2 = 0 ∧
      typedCount (coordType bCoord2) w 0 % 2 = 0 := by
  rw [vAccum_eq_vAccumAux]
  obtain ⟨i, hi⟩ := isV4_vAccumAux w 0
  have hone : (vAccumAux w 0 = 1) ↔
      (bCoord1 (vAccumAux w 0) = false ∧ bCoord2 (vAccumAux w 0) = false) := by
    rw [← hi]
    exact v4_eq_one_iff_bCoord i
  have h1 := bCoord_vAccumAux bCoord1 (fun hu hv => bCoord1_mul hu hv) (by decide) w 0
  have h2 := bCoord_vAccumAux bCoord2 (fun hu hv => bCoord2_mul hu hv) (by decide) w 0
  rw [hone, h1, h2]
  simp only [decide_eq_false_iff_not]
  omega

/-! ### Phase classes of letters -/

/-- The four group elements of a fixed phase `e` (unique normal forms). -/
def lettersOfPhase (e : Fin 3) : List A4 :=
  [v4 0 * t ^ e.val, v4 1 * t ^ e.val, v4 2 * t ^ e.val, v4 3 * t ^ e.val]

theorem mem_lettersOfPhase_iff :
    ∀ g : A4, ∀ e : Fin 3, g ∈ lettersOfPhase e ↔ phase g = e := by
  decide

/-- Number of letters of `w` that land on phase `q` (running phase becomes `q`). -/
def landingCount (q : Fin 3) : Word A4 → Nat → Nat
  | [], _ => 0
  | g :: w, p =>
    (if (p + (phase g).val) % 3 = q.val then 1 else 0) +
      landingCount q w (p + (phase g).val)

theorem landingCount_nil (q : Fin 3) (p : Nat) : landingCount q [] p = 0 := rfl

theorem landingCount_cons (q : Fin 3) (g : A4) (w : Word A4) (p : Nat) :
    landingCount q (g :: w) p =
      (if (p + (phase g).val) % 3 = q.val then 1 else 0) +
        landingCount q w (p + (phase g).val) := rfl

/-- Landing count equals the typed sum over pairs `(g,p)` with `p+ε_g ≡ q`. -/
def landingType (q : Fin 3) : A4 → Fin 3 → Bool :=
  fun g p => decide ((p.val + (phase g).val) % 3 = q.val)

theorem landingCount_eq_typedCount (q : Fin 3) :
    ∀ (w : Word A4) (p : Nat),
      landingCount q w p = typedCount (landingType q) w p
  | [], p => rfl
  | g :: w, p => by
    have ih := landingCount_eq_typedCount q w (p + (phase g).val)
    simp only [landingCount_cons, typedCount_cons, landingType, ih]
    -- indicators agree: `(p + ε) % 3 = q` iff `((p%3) + ε) % 3 = q`
    have hp : p % 3 < 3 := Nat.mod_lt p (by decide)
    have hε : (phase g).val < 3 := (phase g).isLt
    have hmod : (p + (phase g).val) % 3 = (p % 3 + (phase g).val) % 3 := by
      have := Nat.add_mod p (phase g).val 3
      -- (p + ε) % 3 = (p % 3 + ε % 3) % 3 and ε % 3 = ε
      simpa [Nat.mod_eq_of_lt hε] using this
    by_cases h : (p + (phase g).val) % 3 = q.val
    · have h' : (p % 3 + (phase g).val) % 3 = q.val := by
        rwa [← hmod]
      simp [h, h', show (⟨p % 3, hp⟩ : Fin 3).val = p % 3 from rfl]
    · have h' : ¬ (p % 3 + (phase g).val) % 3 = q.val := by
        intro h0; exact h (hmod.trans h0)
      simp [h, h', show (⟨p % 3, hp⟩ : Fin 3).val = p % 3 from rfl]

end A4Structure
end GSH
