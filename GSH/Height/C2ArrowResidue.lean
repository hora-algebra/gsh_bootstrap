import GSH.Groups.Abelian
import GSH.Height.C2ArrowArithmetic
import GSH.Height.FiniteBoolean
import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# Height-one source-zero arrow residues for an arbitrary `C₂` phase

The phase-zero case is the return-code theorem.  For a phase-one label we
assemble ordinary count residues and distinct phase-one pair residues by the
arithmetic identity in `C2ArrowArithmetic`, using modulus `2 * m` to recover
the source-zero count modulo an arbitrary positive `m`.
-/

set_option autoImplicit false

namespace GSH
namespace C2ArrowResidue

open ArrowCounting
open C2PairTransfer

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Words of total phase zero. -/
def evenPhase (phase : α → ZMod 2) : Language α :=
  {word | (word.map phase).sum = 0}

/-- Recognition of the total phase by the multiplicative copy of `ZMod 2`. -/
noncomputable def phaseRecognition (phase : α → ZMod 2) :
    Recognition α (Multiplicative (ZMod 2)) where
  morphism := FreeMonoid.lift fun a => Multiplicative.ofAdd (phase a)
  accepting := {1}

private theorem language_phaseRecognition (phase : α → ZMod 2) :
    (phaseRecognition phase).language = evenPhase phase := by
  ext word
  simp only [Recognition.mem_language_iff, phaseRecognition,
    FreeMonoid.lift_ofList, Set.mem_singleton_iff, evenPhase, Set.mem_setOf_eq]
  change Multiplicative.ofAdd (word.map phase).sum =
      Multiplicative.ofAdd 0 ↔ (word.map phase).sum = 0
  constructor
  · intro h
    simpa [Function.comp_def] using congrArg Multiplicative.toAdd h
  · intro h
    exact congrArg Multiplicative.ofAdd h

/-- The phase-zero language has generalized star height at most one. -/
theorem hasHeightAtMost_evenPhase (phase : α → ZMod 2) :
    HasHeightAtMost (evenPhase phase) 1 := by
  have h := heightOne_of_commGroup.{u, 0} (Multiplicative (ZMod 2))
    α (phaseRecognition phase)
  exact h.congr (language_phaseRecognition phase)

/-! ## Phase-one source-zero residues -/

/-- Feature indices: total phase, ordinary count, and ordered pair count. -/
abbrev MovingIndex (phase : α → ZMod 2) (n : Nat) :=
  Unit ⊕ (Fin n ⊕ ((PhaseOne phase × PhaseOne phase) × Fin n))

/-- The finite family used to reconstruct a moving-arrow residue. -/
def movingFeature (phase : α → ZMod 2) (label : PhaseOne phase)
    (n : Nat) : MovingIndex phase n → Language α
  | .inl _ => evenPhase phase
  | .inr (.inl residue) =>
      {word | word.count label.1 % n = residue.1}
  | .inr (.inr ((x, y), residue)) =>
      if x = y then Set.univ
      else C2PairTransfer.pairResidue phase x y n residue.1

/-- Truth-table predicate for source-zero residue `residue` modulo `m`. -/
def movingAccept (phase : α → ZMod 2) (label : PhaseOne phase)
    (m : Nat) (residue : Fin m)
    (bits : MovingIndex phase (2 * m) → Bool) : Prop :=
  bits (.inl ()) = true ∧
    ∃ total : Fin (2 * m), bits (.inr (.inl total)) = true ∧
    ∃ pairs : (PhaseOne phase × PhaseOne phase) → Fin (2 * m),
      (∀ x y, x ≠ y →
        bits (.inr (.inr ((x, y), pairs (x, y)))) = true) ∧
      (2 : ZMod (2 * m)) * (residue.1 : ZMod (2 * m)) =
        (total.1 : ZMod (2 * m)) +
          ∑ other : PhaseOne phase,
            if other = label then 0
            else
              ((pairs (label, other)).1 : ZMod (2 * m)) -
                ((pairs (other, label)).1 : ZMod (2 * m))

/-- Words of even phase with prescribed source-zero arrow residue. -/
def movingResidue (phase : α → ZMod 2) (label : α)
    (m residue : Nat) : Language α :=
  {word | (word.map phase).sum = 0 ∧
    ArrowCounting.arrowCountFrom (ArrowCounting.c2Step phase)
      0 0 label word % m = residue}

private theorem two_cast_eq_iff_mod (m a r : Nat)
    (hm : 0 < m) (hr : r < m) :
    (2 : ZMod (2 * m)) * (a : ZMod (2 * m)) =
        (2 : ZMod (2 * m)) * (r : ZMod (2 * m)) ↔
      a % m = r := by
  have hcast : ∀ n : Nat,
      (2 : ZMod (2 * m)) * (n : ZMod (2 * m)) =
        ((2 * n : Nat) : ZMod (2 * m)) := by
    intro n
    norm_cast
  rw [hcast a, hcast r, ZMod.natCast_eq_natCast_iff']
  rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
  rw [Nat.mod_eq_of_lt hr]
  omega

private theorem movingFeature_heightOne (phase : α → ZMod 2)
    (label : PhaseOne phase) (m : Nat) (hm : 0 < m)
    (index : MovingIndex phase (2 * m)) :
    HasHeightAtMost (movingFeature phase label (2 * m) index) 1 := by
  rcases index with _ | residue | ⟨⟨x, y⟩, residue⟩
  · exact hasHeightAtMost_evenPhase phase
  · exact Counting.hasHeightAtMost_count label.1 residue.2
  · by_cases hxy : x = y
    · subst y
      simpa [movingFeature] using
        (HasHeightAtMost.univ (α := α) (n := 1))
    · simpa [movingFeature, hxy] using
        C2PairTransfer.hasHeightAtMost_pairResidue phase x y
          (fun h => hxy (Subtype.ext h)) (2 * m) (by omega) residue

private theorem movingAssembly_eq (phase : α → ZMod 2)
    (label : PhaseOne phase) (m : Nat) (hm : 0 < m)
    (residue : Fin m) :
    Language.booleanCombination (movingFeature phase label (2 * m))
        (movingAccept phase label m residue) =
      movingResidue phase label.1 m residue.1 := by
  classical
  letI : BEq (PhaseOne phase) := instBEqOfDecidableEq
  ext word
  simp only [Language.booleanCombination, movingAccept, movingResidue,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hevenBit, total, htotalBit, pairs, hpairsBit, haccept⟩
    have heven : (word.map phase).sum = 0 := by
      have hmem : word ∈
          movingFeature phase label (2 * m) (.inl ()) :=
        of_decide_eq_true hevenBit
      simpa [movingFeature, evenPhase] using hmem
    have htotalMem : word ∈
        movingFeature phase label (2 * m) (.inr (.inl total)) :=
      of_decide_eq_true htotalBit
    change word.count label.1 % (2 * m) = total.1 at htotalMem
    have htotalZ : (word.count label.1 : ZMod (2 * m)) =
        (total.1 : ZMod (2 * m)) := by
      rw [← ZMod.natCast_mod (word.count label.1) (2 * m), htotalMem]
    have hpairsZ : ∀ x y : PhaseOne phase, x ≠ y →
        (C2PairTransfer.pairCountOf x y
            (C2PairTransfer.phaseOneSubword phase word) : ZMod (2 * m)) =
          ((pairs (x, y)).1 : ZMod (2 * m)) := by
      intro x y hxy
      have hmem : word ∈ movingFeature phase label (2 * m)
          (.inr (.inr ((x, y), pairs (x, y)))) :=
        of_decide_eq_true (hpairsBit x y hxy)
      have hpair : word ∈
          C2PairTransfer.pairResidue phase x y (2 * m)
            (pairs (x, y)).1 := by
        simpa [movingFeature, hxy] using hmem
      have hcount := hpair.2
      rw [← ZMod.natCast_mod
        (C2PairTransfer.pairCountOf x y
          (C2PairTransfer.phaseOneSubword phase word)) (2 * m), hcount]
    have hbalance :
        C2ArrowArithmetic.pairBalance (2 * m) label
            (C2PairTransfer.phaseOneSubword phase word) =
          ∑ other : PhaseOne phase,
            if other = label then 0
            else
              ((pairs (label, other)).1 : ZMod (2 * m)) -
                ((pairs (other, label)).1 : ZMod (2 * m)) := by
      unfold C2ArrowArithmetic.pairBalance
      apply Finset.sum_congr rfl
      intro other _
      by_cases ho : other = label
      · simp [ho]
      · simp only [ho, if_false]
        rw [hpairsZ label other (fun h => ho h.symm),
          hpairsZ other label ho]
    have harith := C2ArrowArithmetic.two_mul_evenArrow_eq_count_add_pairBalance
      phase (2 * m) label word heven
    rw [htotalZ, hbalance] at harith
    refine ⟨heven, (two_cast_eq_iff_mod m
      (ArrowCounting.arrowCountFrom (ArrowCounting.c2Step phase)
        0 0 label.1 word) residue.1 hm residue.2).1 ?_⟩
    exact harith.trans haccept.symm
  · rintro ⟨heven, hresidue⟩
    let total : Fin (2 * m) :=
      ⟨word.count label.1 % (2 * m), Nat.mod_lt _ (by omega)⟩
    let pairs : (PhaseOne phase × PhaseOne phase) → Fin (2 * m) :=
      fun pair =>
        ⟨C2PairTransfer.pairCountOf pair.1 pair.2
            (C2PairTransfer.phaseOneSubword phase word) % (2 * m),
          Nat.mod_lt _ (by omega)⟩
    refine ⟨?_, total, ?_, pairs, ?_, ?_⟩
    · simp [Language.truthVector, movingFeature, evenPhase, heven]
    · simp [Language.truthVector, movingFeature, total]
    · intro x y hxy
      simp [Language.truthVector, movingFeature, hxy, pairs,
        C2PairTransfer.pairResidue, heven]
    · have harith :=
        C2ArrowArithmetic.two_mul_evenArrow_eq_count_add_pairBalance
          phase (2 * m) label word heven
      have hleft := (two_cast_eq_iff_mod m
        (ArrowCounting.arrowCountFrom (ArrowCounting.c2Step phase)
          0 0 label.1 word) residue.1 hm residue.2).2 hresidue
      rw [harith] at hleft
      simpa [total, pairs, C2ArrowArithmetic.pairBalance,
        ZMod.natCast_mod] using hleft.symm

/-- Every phase-one source-zero arrow residue has height at most one. -/
theorem hasHeightAtMost_movingResidue (phase : α → ZMod 2)
    (label : PhaseOne phase) (m : Nat) (hm : 0 < m)
    (residue : Fin m) :
    HasHeightAtMost (movingResidue phase label.1 m residue.1) 1 := by
  have hassembly := HasHeightAtMost.booleanCombination
    (movingFeature phase label (2 * m))
    (movingAccept phase label m residue)
    (movingFeature_heightOne phase label m hm)
  exact hassembly.congr (movingAssembly_eq phase label m hm residue)

/-- Uniform source-zero residue theorem, split only by the letter phase. -/
theorem hasHeightAtMost_sourceZeroResidue (phase : α → ZMod 2)
    (label : α) (m : Nat) (hm : 0 < m) (residue : Fin m) :
    HasHeightAtMost
      {word | (word.map phase).sum = 0 ∧
        ArrowCounting.arrowCountFrom (ArrowCounting.c2Step phase)
          0 0 label word % m = residue.1} 1 := by
  by_cases hlabel : phase label = 1
  · exact hasHeightAtMost_movingResidue phase ⟨label, hlabel⟩ m hm residue
  · have hzero : phase label = 0 := by
      have hval : (phase label).val = 0 ∨ (phase label).val = 1 := by
        have := ZMod.val_lt (phase label)
        omega
      rcases hval with hval | hval
      · apply ZMod.val_injective 2
        simpa [hval]
      · exfalso
        apply hlabel
        apply ZMod.val_injective 2
        simpa [hval, ZMod.val_one]
    exact C2SelfLoop.hasHeightAtMost_evenResidue
      phase label hzero m hm residue

end C2ArrowResidue
end GSH
