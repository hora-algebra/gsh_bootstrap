import GSH.Height.A4Coordinates

/-!
# The nonmover cut identity for `A₄`

This file formalizes the all-word combinatorial identity from
`notes/a4_full_alphabet_exact.md` §5.1.  For a phase-zero letter `h`, every
arrival at phase `q` is either an occurrence of `h` or a cut not delayed by
`h`.  Hence `N[h,q] = Z_q + F(q,h)` modulo two.

The definitions below count cuts only.  No generalized-star-height claim is
made here; height one for the two cut-parity languages remains the next step.
-/

set_option autoImplicit false

namespace GSH

/-- Base cuts: count every arrival at the selected phase. -/
def a4BaseCutCountFrom : ZMod 3 → ZMod 3 → Word A4 → Nat
  | _, _, [] => 0
  | phase, target, g :: word =>
      (if phase + a4PhaseValue g = target then 1 else 0) +
        a4BaseCutCountFrom (phase + a4PhaseValue g) target word

/-- The §5.1 single-delay cut count.  An arrival at `target` is not cut
precisely when its arriving letter is the selected phase-zero `label`.

This executable definition does not assert that its parity language has
height one. -/
def a4SingleDelayCutCountFrom (label : A4) :
    ZMod 3 → ZMod 3 → Word A4 → Nat
  | _, _, [] => 0
  | phase, target, g :: word =>
      (if phase + a4PhaseValue g = target ∧ g ≠ label then 1 else 0) +
        a4SingleDelayCutCountFrom label
          (phase + a4PhaseValue g) target word

/-- Source-phase labelled-letter count with an arbitrary starting phase. -/
def a4PhaseLabelCountFrom (start target : ZMod 3)
    (label : A4) (word : Word A4) : Nat :=
  @List.count (ZMod 3 × A4) instBEqOfDecidableEq (target, label)
    (a4PhaseLabelsFrom start word)

/-- Exact natural-number partition behind §5.1: for a phase-zero label,
every base arrival is uniquely either that label or a non-delayed single
cut. -/
theorem a4_baseCut_partition_nonmover
    (label : A4) (hlabel : a4PhaseValue label = 0)
    (start target : ZMod 3) (word : Word A4) :
    a4BaseCutCountFrom start target word =
      a4PhaseLabelCountFrom start target label word +
        a4SingleDelayCutCountFrom label start target word := by
  induction word generalizing start with
  | nil => rfl
  | cons g word ih =>
      simp only [a4BaseCutCountFrom, a4SingleDelayCutCountFrom,
        a4PhaseLabelCountFrom, a4PhaseLabelsFrom, List.count_cons]
      rw [ih]
      by_cases hg : g = label
      · subst g
        simp [a4PhaseLabelCountFrom, hlabel, Nat.add_comm,
          Nat.add_left_comm]
      · by_cases harrival : start + a4PhaseValue g = target
        · simp [a4PhaseLabelCountFrom, hg, harrival, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm]
        · simp [a4PhaseLabelCountFrom, hg, harrival]

/-- The original count is the arbitrary-start count specialized to zero. -/
theorem a4PhaseLabelCount_eq_from_zero
    (target : ZMod 3) (label : A4) (word : Word A4) :
    a4PhaseLabelCount target label word =
      a4PhaseLabelCountFrom 0 target label word := rfl

/-- The exact parity identity `N[h,q] = Z_q + F(q,h)` over `ZMod 2`. -/
theorem a4_nonmover_parity_identity
    (label : A4) (hlabel : a4PhaseValue label = 0)
    (target : ZMod 3) (word : Word A4) :
    (a4PhaseLabelCount target label word : ZMod 2) =
      (a4BaseCutCountFrom 0 target word : ZMod 2) +
        (a4SingleDelayCutCountFrom label 0 target word : ZMod 2) := by
  have hpart := a4_baseCut_partition_nonmover label hlabel 0 target word
  rw [a4PhaseLabelCount_eq_from_zero]
  have hcast := congrArg (fun n : Nat => (n : ZMod 2)) hpart
  push_cast at hcast
  rw [hcast]
  ring_nf
  rw [show (2 : ZMod 2) = 0 by decide, mul_zero]
  simp

/-- The same identity in the natural-number residue form consumed directly
by `a4PhaseLabelParityFeature`. -/
theorem a4_nonmover_mod_two_identity
    (label : A4) (hlabel : a4PhaseValue label = 0)
    (target : ZMod 3) (word : Word A4) :
    a4PhaseLabelCount target label word % 2 =
      (a4BaseCutCountFrom 0 target word % 2 +
        a4SingleDelayCutCountFrom label 0 target word % 2) % 2 := by
  rw [a4PhaseLabelCount_eq_from_zero]
  have hpart := a4_baseCut_partition_nonmover label hlabel 0 target word
  omega

end GSH
