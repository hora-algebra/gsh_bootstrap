import GSH.Recognition
import Mathlib.Data.Fintype.Card

/-!
# Local divisors

The *local divisor* of a monoid `M` at an element `c` is

    M_c = (cM ∩ Mc, ∘, c),      (x c) ∘ (c y) = x c y.

It is the engine of the Diekert–Kufleitner induction: `M_c` is a divisor of
`M`, it inherits aperiodicity, and it is **strictly smaller** than `M` as soon
as `c` is not a unit.  That is what makes induction on `|M|` possible in the
local-divisor proof of Schützenberger's theorem
(obligation `L-SF-001`).

## Design notes

* The product is defined by `z₁ ∘ z₂ = x * z₂` for *any* `x` with
  `z₁ = x * c`; `mul_indep` shows the value does not depend on the choice, and
  `mul_val_left` / `mul_val_right` are the two working formulas
  (`z₁ ∘ z₂ = x * z₂ = z₁ * y` for `z₁ = x c`, `z₂ = c y`).  Extracting the
  witness needs `Classical.choose`, so the `Mul` instance is `noncomputable`.
  This is mathematically inessential — the operation is a genuine function,
  only the *representative* is chosen — and nothing downstream evaluates it.
* Aperiodicity is inherited by the direct computation `z^(n+1) = z * u^n`
  (in `M`) for `z = c * u`, rather than through the divisor property.

## References

* M. Kufleitner, *Star-free languages and local divisors*, arXiv:1408.2842.
* V. Diekert, M. Kufleitner, *A survey on the local divisor technique*,
  Theoretical Computer Science 610 (2016) 13–23; arXiv:1410.6026.
  Definition and Proposition 2.1 there.

This file contains no `sorry` and no `axiom`.
-/

set_option autoImplicit false

namespace GSH
namespace LocalDivisor

universe v

variable {M : Type v} [Monoid M]

/-- Membership in `cM ∩ Mc`. -/
def IsLocal (c z : M) : Prop := (∃ y, z = c * y) ∧ (∃ x, z = x * c)

theorem isLocal_self (c : M) : IsLocal c c := ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩

/-- The carrier of the local divisor at `c`. -/
def LocalDiv (c : M) : Type v := {z : M // IsLocal c z}

namespace LocalDiv

variable {c : M}

@[ext] theorem ext {z w : LocalDiv c} (h : z.val = w.val) : z = w := Subtype.ext h

instance instDecidableIsLocal [Fintype M] [DecidableEq M] (a z : M) :
    Decidable (IsLocal a z) := by
  unfold IsLocal
  infer_instance

instance instFintype [Fintype M] [DecidableEq M] (a : M) : Fintype (LocalDiv a) :=
  inferInstanceAs (Fintype {z : M // IsLocal a z})

instance instDecidableEq [DecidableEq M] (a : M) : DecidableEq (LocalDiv a) :=
  inferInstanceAs (DecidableEq {z : M // IsLocal a z})

/-- `x * z₂` lands back in `cM ∩ Mc`. -/
theorem isLocal_mul {z₁ z₂ : M} (h₁ : IsLocal c z₁) (h₂ : IsLocal c z₂) {x : M}
    (hx : z₁ = x * c) : IsLocal c (x * z₂) := by
  obtain ⟨u, hu⟩ := h₁.1
  obtain ⟨y, hy⟩ := h₂.1
  obtain ⟨v, hv⟩ := h₂.2
  refine ⟨⟨u * y, ?_⟩, ⟨x * v, ?_⟩⟩
  · rw [hy, ← mul_assoc, ← hx, hu, mul_assoc]
  · rw [hv, mul_assoc]

/-- The product does not depend on the chosen representative of `z₁ ∈ Mc`. -/
theorem mul_indep {z₁ z₂ : M} (h₂ : IsLocal c z₂) {x x' : M}
    (hx : z₁ = x * c) (hx' : z₁ = x' * c) : x * z₂ = x' * z₂ := by
  obtain ⟨y, hy⟩ := h₂.1
  rw [hy, ← mul_assoc, ← mul_assoc, ← hx, ← hx']

noncomputable instance : Mul (LocalDiv c) where
  mul z₁ z₂ :=
    ⟨Classical.choose z₁.2.2 * z₂.val,
      isLocal_mul z₁.2 z₂.2 (Classical.choose_spec z₁.2.2)⟩

/-- Working formula: pick any `x` with `z₁ = x c`. -/
theorem mul_val_left (z₁ z₂ : LocalDiv c) {x : M} (hx : z₁.val = x * c) :
    (z₁ * z₂).val = x * z₂.val :=
  mul_indep z₂.2 (Classical.choose_spec z₁.2.2) hx

/-- Working formula: pick any `y` with `z₂ = c y`. -/
theorem mul_val_right (z₁ z₂ : LocalDiv c) {y : M} (hy : z₂.val = c * y) :
    (z₁ * z₂).val = z₁.val * y := by
  obtain ⟨x, hx⟩ := z₁.2.2
  rw [mul_val_left z₁ z₂ hx, hy, ← mul_assoc, ← hx]

instance : One (LocalDiv c) := ⟨⟨c, isLocal_self c⟩⟩

@[simp] theorem one_val : (1 : LocalDiv c).val = c := rfl

noncomputable instance : Monoid (LocalDiv c) where
  mul_assoc z₁ z₂ z₃ := by
    obtain ⟨x, hx⟩ := z₁.2.2
    obtain ⟨v, hv⟩ := z₂.2.2
    apply ext
    have h12 : (z₁ * z₂).val = x * v * c := by
      rw [mul_val_left z₁ z₂ hx, hv, mul_assoc]
    rw [mul_val_left (z₁ * z₂) z₃ h12, mul_val_left z₁ (z₂ * z₃) hx,
      mul_val_left z₂ z₃ hv, mul_assoc]
  one_mul z := by
    apply ext
    rw [mul_val_left 1 z (show (1 : LocalDiv c).val = 1 * c by simp), one_mul]
  mul_one z := by
    apply ext
    rw [mul_val_right z 1 (show (1 : LocalDiv c).val = c * 1 by simp), mul_one]

/-- Powers in `M_c` are powers in `M` shifted by one factor. -/
theorem pow_succ_val (z : LocalDiv c) {u : M} (hu : z.val = c * u) :
    ∀ n : Nat, (z ^ (n + 1)).val = z.val * u ^ n
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, mul_val_right (z ^ (n + 1)) z hu, pow_succ_val z hu n, pow_succ,
      mul_assoc]

/-- The local divisor inherits aperiodicity. -/
theorem isAperiodic (hM : IsAperiodicMonoid M) (c : M) :
    IsAperiodicMonoid (LocalDiv c) := by
  intro z
  obtain ⟨u, hu⟩ := z.2.1
  obtain ⟨n, hn⟩ := hM u
  refine ⟨n + 1, ?_⟩
  apply ext
  rw [pow_succ_val z hu (n + 1), pow_succ_val z hu n, hn]

/-- If `1` lies in `cM ∩ Mc` then `c` is a unit. -/
theorem isUnit_of_isLocal_one {c : M} (h : IsLocal c (1 : M)) : IsUnit c := by
  obtain ⟨⟨y, hy⟩, ⟨x, hx⟩⟩ := h
  have hcy : c * y = 1 := hy.symm
  have hxc : x * c = 1 := hx.symm
  have hxy : x = y := by
    calc x = x * 1 := by rw [mul_one]
      _ = x * (c * y) := by rw [hcy]
      _ = (x * c) * y := by rw [mul_assoc]
      _ = y := by rw [hxc, one_mul]
  exact ⟨⟨c, y, hcy, by rw [← hxy]; exact hxc⟩, rfl⟩

/-- **The induction measure decreases.**  If `c` is not a unit, the local
divisor at `c` is strictly smaller than `M`. -/
theorem card_lt [Fintype M] [DecidableEq M] {c : M} (hc : ¬ IsUnit c) :
    Fintype.card (LocalDiv c) < Fintype.card M := by
  have hnot : ¬ IsLocal c (1 : M) := fun h => hc (isUnit_of_isLocal_one h)
  exact Fintype.card_subtype_lt (p := IsLocal c) hnot

end LocalDiv
end LocalDivisor
end GSH
