import GSH.Height.C2ArrowResidue
import GSH.Height.FullAlphabet
import Mathlib.GroupTheory.RegularWreathProduct

/-!
# Height one for a commutative base wreath `C₂`

For a finite commutative group `D`, this file proves

`HeightOneForGroup (D ≀ᵣ Multiplicative (ZMod 2))`.

The proof records, for every letter, its total multiplicity and the number of
times it is read from state zero in the two-state quotient.  The latter
residue languages are supplied by `C2ArrowResidue`.  These finite data recover
both coordinates of the wreath-product value modulo `|D|`.
-/

set_option autoImplicit false

namespace GSH
namespace C2Wreath

open ArrowCounting

universe v

abbrev C2 := Multiplicative (ZMod 2)

variable {D : Type v} [CommGroup D] [Fintype D]

noncomputable section

local instance wreathFintype : Fintype (D ≀ᵣ C2) :=
  Fintype.ofFinite (D ≀ᵣ C2)

local instance wreathDecidableEq : DecidableEq (D ≀ᵣ C2) :=
  Classical.decEq (D ≀ᵣ C2)

local instance wreathBEq : BEq (D ≀ᵣ C2) :=
  instBEqOfDecidableEq

local instance pairBEq : BEq (ZMod 2 × (D ≀ᵣ C2)) :=
  instBEqProd

/-- The additive phase of a wreath-product letter. -/
def phase (letter : D ≀ᵣ C2) : ZMod 2 := letter.right.toAdd

/-- The run annotated by the state immediately before each letter. -/
def traceFrom {α : Type*} (phase : α → ZMod 2) :
    ZMod 2 → Word α → List (ZMod 2 × α)
  | _, [] => []
  | state, letter :: word =>
      (state, letter) :: traceFrom phase (state + phase letter) word

@[simp] theorem traceFrom_nil {α : Type*} (phase : α → ZMod 2)
    (state : ZMod 2) : traceFrom phase state [] = [] := rfl

@[simp] theorem traceFrom_cons {α : Type*} (phase : α → ZMod 2)
    (state : ZMod 2) (letter : α) (word : Word α) :
    traceFrom phase state (letter :: word) =
      (state, letter) :: traceFrom phase (state + phase letter) word := rfl

private theorem zmod2_eq_zero_or_one (state : ZMod 2) :
    state = 0 ∨ state = 1 := by
  revert state
  decide

/-- Counting an annotated pair in `traceFrom` is exactly counting the
corresponding labelled arrow of the run. -/
theorem count_traceFrom {α : Type*} [DecidableEq α]
    (phase : α → ZMod 2) (start source : ZMod 2)
    (label : α) (word : Word α) :
    @List.count (ZMod 2 × α) instBEqOfDecidableEq
        (source, label) (traceFrom phase start word) =
      arrowCountFrom (c2Step phase) start source label word := by
  induction word generalizing start with
  | nil => simp
  | cons letter word ih =>
      simp only [traceFrom_cons, List.count_cons, arrowCountFrom_cons]
      rw [ih]
      by_cases hstate : start = source <;>
        by_cases hletter : letter = label <;>
          simp [c2Step, hstate, hletter, Nat.add_comm]

/-- The two source counts partition the ordinary letter count. -/
theorem sourceCounts_add (phase : (D ≀ᵣ C2) → ZMod 2)
    (start : ZMod 2) (label : D ≀ᵣ C2) (word : Word (D ≀ᵣ C2)) :
    arrowCountFrom (c2Step phase) start 0 label word +
        arrowCountFrom (c2Step phase) start 1 label word =
      word.count label := by
  classical
  induction word generalizing start with
  | nil => simp
  | cons letter word ih =>
      rcases zmod2_eq_zero_or_one start with rfl | rfl
      · by_cases hletter : letter = label <;>
          simp [arrowCountFrom_cons, hletter, ih, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm]
      · by_cases hletter : letter = label <;>
          simp [arrowCountFrom_cons, hletter, ih, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm]

/-- The right coordinate of a word product is the sum of its phases. -/
theorem prod_right (word : Word (D ≀ᵣ C2)) :
    word.prod.right = Multiplicative.ofAdd (word.map phase).sum := by
  induction word with
  | nil => rfl
  | cons letter word ih =>
      simp only [List.prod_cons, RegularWreathProduct.mul_right,
        phase, List.map_cons, List.sum_cons]
      rw [ih]
      rfl

/-- Coordinate evaluation of a word product along its annotated run. -/
theorem prod_left_trace (start q : ZMod 2)
    (word : Word (D ≀ᵣ C2)) :
    word.prod.left (Multiplicative.ofAdd (start + q)) =
      ((traceFrom phase start word).map fun pair =>
        pair.2.left (Multiplicative.ofAdd (pair.1 + q))).prod := by
  induction word generalizing start with
  | nil => simp
  | cons letter word ih =>
      simp only [List.prod_cons, RegularWreathProduct.mul_left,
        traceFrom_cons, List.map_cons, List.prod_cons]
      change letter.left (Multiplicative.ofAdd (start + q)) *
          word.prod.left
            (letter.right⁻¹ * Multiplicative.ofAdd (start + q)) = _
      congr 1
      have hcoord : letter.right⁻¹ * Multiplicative.ofAdd (start + q) =
          Multiplicative.ofAdd ((start + phase letter) + q) := by
        apply Multiplicative.toAdd.injective
        change -(letter.right.toAdd) + (start + q) =
          (start + letter.right.toAdd) + q
        have hinv : -(letter.right.toAdd) = letter.right.toAdd := by
          exact CharTwo.neg_eq (letter.right.toAdd)
        rw [hinv]
        ac_rfl
      rw [hcoord, ih (start + phase letter)]

/-- A wreath coordinate is a commutative product weighted by arrow counts. -/
theorem prod_left_counts (start q : ZMod 2)
    (word : Word (D ≀ᵣ C2)) :
    word.prod.left (Multiplicative.ofAdd (start + q)) =
      ∏ pair : ZMod 2 × (D ≀ᵣ C2),
        (pair.2.left (Multiplicative.ofAdd (pair.1 + q))) ^
          arrowCountFrom (c2Step phase) start pair.1 pair.2 word := by
  classical
  rw [prod_left_trace, Abelian.prod_map_count]
  apply Finset.prod_congr rfl
  rintro ⟨source, label⟩ _
  simp only [Prod.fst, Prod.snd]
  exact congrArg
    (fun n => (label.left (Multiplicative.ofAdd (source + q))) ^ n)
    (count_traceFrom phase start source label word)

/-- The finite signature used for the full-alphabet identity fibre: source-zero
arrow residues and ordinary count residues, both modulo `|D|`. -/
abbrev Signature :=
  ((D ≀ᵣ C2) → Fin (Fintype.card D)) ×
    ((D ≀ᵣ C2) → Fin (Fintype.card D))

/-- Signature of a word. -/
def signature (word : Word (D ≀ᵣ C2)) : Signature (D := D) :=
  (fun label =>
      ⟨arrowCountFrom (c2Step phase) 0 0 label word % Fintype.card D,
        Nat.mod_lt _ Fintype.card_pos⟩,
    fun label =>
      ⟨word.count label % Fintype.card D,
        Nat.mod_lt _ Fintype.card_pos⟩)

/-- Fibre of an even word signature. -/
def signatureFiber (selected : Signature (D := D)) :
    Language (D ≀ᵣ C2) :=
  C2ArrowResidue.evenPhase phase ∩
    (⋂ label : D ≀ᵣ C2,
      {word | (word.map phase).sum = 0 ∧
        arrowCountFrom (c2Step phase) 0 0 label word % Fintype.card D =
          (selected.1 label).1}) ∩
    (⋂ label : D ≀ᵣ C2,
      {word | word.count label % Fintype.card D = (selected.2 label).1})

/-- Every even signature fibre has generalized star height at most one. -/
theorem hasHeightAtMost_signatureFiber (selected : Signature (D := D)) :
    HasHeightAtMost (signatureFiber selected) 1 := by
  classical
  refine HasHeightAtMost.inter
    (HasHeightAtMost.inter
      (C2ArrowResidue.hasHeightAtMost_evenPhase phase)
      (HasHeightAtMost.iInter _ fun label =>
        C2ArrowResidue.hasHeightAtMost_sourceZeroResidue phase label
          (Fintype.card D) Fintype.card_pos (selected.1 label)))
    (HasHeightAtMost.iInter _ fun label =>
      Counting.hasHeightAtMost_count label (selected.2 label).2)

private theorem sourceOne_mod_eq_of_signature_eq
    {word word' : Word (D ≀ᵣ C2)}
    (hsig : signature word = signature word') (label : D ≀ᵣ C2) :
    arrowCountFrom (c2Step phase) 0 1 label word % Fintype.card D =
      arrowCountFrom (c2Step phase) 0 1 label word' % Fintype.card D := by
  have hzero :
      arrowCountFrom (c2Step phase) 0 0 label word ≡
        arrowCountFrom (c2Step phase) 0 0 label word' [MOD Fintype.card D] := by
    exact congrArg Fin.val (congrFun (congrArg Prod.fst hsig) label)
  have htotal : word.count label ≡ word'.count label [MOD Fintype.card D] := by
    exact congrArg Fin.val (congrFun (congrArg Prod.snd hsig) label)
  have hadd :
      arrowCountFrom (c2Step phase) 0 0 label word +
          arrowCountFrom (c2Step phase) 0 1 label word ≡
        arrowCountFrom (c2Step phase) 0 0 label word' +
          arrowCountFrom (c2Step phase) 0 1 label word' [MOD Fintype.card D] := by
    rw [sourceCounts_add, sourceCounts_add]
    exact htotal
  exact hzero.add_left_cancel hadd

/-- On even words, the wreath-product value depends only on the finite
signature above. -/
theorem prod_eq_of_even_signature_eq
    {word word' : Word (D ≀ᵣ C2)}
    (heven : (word.map phase).sum = 0)
    (heven' : (word'.map phase).sum = 0)
    (hsig : signature word = signature word') :
    word.prod = word'.prod := by
  classical
  apply RegularWreathProduct.ext
  · funext coordinate
    let q : ZMod 2 := coordinate.toAdd
    have hcoordinate : Multiplicative.ofAdd (0 + q) = coordinate := by
      simp [q]
    rw [← hcoordinate, prod_left_counts 0 q word,
      prod_left_counts 0 q word']
    apply Finset.prod_congr rfl
    rintro ⟨source, label⟩ _
    have hmod :
        arrowCountFrom (c2Step phase) 0 source label word % Fintype.card D =
          arrowCountFrom (c2Step phase) 0 source label word' % Fintype.card D := by
      rcases zmod2_eq_zero_or_one source with hzero | hone
      · subst source
        exact congrArg Fin.val
          (congrFun (congrArg Prod.fst hsig) label)
      · subst source
        exact sourceOne_mod_eq_of_signature_eq hsig label
    have hpow (x : D) (n : Nat) : x ^ n = x ^ (n % Fintype.card D) := by
      conv_lhs => rw [← Nat.div_add_mod n (Fintype.card D)]
      rw [pow_add, pow_mul, pow_card_eq_one, one_pow, one_mul]
    simp only [Prod.fst, Prod.snd]
    calc
      (label.left (Multiplicative.ofAdd (source + q))) ^
          arrowCountFrom (c2Step phase) 0 source label word =
        (label.left (Multiplicative.ofAdd (source + q))) ^
          (arrowCountFrom (c2Step phase) 0 source label word %
            Fintype.card D) := hpow _ _
      _ = (label.left (Multiplicative.ofAdd (source + q))) ^
          (arrowCountFrom (c2Step phase) 0 source label word' %
            Fintype.card D) := by rw [hmod]
      _ = (label.left (Multiplicative.ofAdd (source + q))) ^
          arrowCountFrom (c2Step phase) 0 source label word' :=
        (hpow _ _).symm
  · rw [prod_right word, prod_right word', heven, heven']

/-- Full-alphabet identity fibre of a finite commutative-base wreath `C₂` has
generalized star height at most one. -/
theorem hasHeightAtMost_fullIdentityFiber :
    HasHeightAtMost (fullIdentityFiber (D ≀ᵣ C2)) 1 := by
  classical
  letI : Fintype (D ≀ᵣ C2) := Fintype.ofFinite (D ≀ᵣ C2)
  let selected : Finset (Signature (D := D)) :=
    Finset.univ.filter fun sig =>
      ∃ word : Word (D ≀ᵣ C2),
        signature word = sig ∧ word.prod = 1
  have hdecomp : fullIdentityFiber (D ≀ᵣ C2) =
      ⋃ sig ∈ selected, signatureFiber sig := by
    ext word
    simp only [Set.mem_iUnion, selected, Finset.mem_filter, Finset.mem_univ,
      true_and, exists_prop, mem_fullIdentityFiber_iff]
    constructor
    · intro hprod
      have heven : (word.map phase).sum = 0 := by
        have hright := congrArg RegularWreathProduct.right hprod
        rw [prod_right] at hright
        exact Multiplicative.ofAdd.injective (by simpa using hright)
      refine ⟨signature word, ⟨word, rfl, hprod⟩, ?_⟩
      simp only [signatureFiber, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_setOf_eq, C2ArrowResidue.evenPhase]
      exact ⟨⟨heven, fun label => ⟨heven, rfl⟩⟩, fun _ => rfl⟩
    · rintro ⟨sig, ⟨witness, hwitnessSig, hwitnessProd⟩, hwordSig⟩
      simp only [signatureFiber, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_setOf_eq, C2ArrowResidue.evenPhase] at hwordSig
      rcases hwordSig with ⟨⟨heven, hzero⟩, htotal⟩
      have hsig : signature word = sig := by
        apply Prod.ext <;> funext label <;> apply Fin.ext
        · exact (hzero label).2
        · exact htotal label
      have hwitnessEven : (witness.map phase).sum = 0 := by
        have hright := congrArg RegularWreathProduct.right hwitnessProd
        rw [prod_right] at hright
        exact Multiplicative.ofAdd.injective (by simpa using hright)
      rw [prod_eq_of_even_signature_eq heven hwitnessEven
        (hsig.trans hwitnessSig.symm), hwitnessProd]
  rw [hdecomp]
  exact HasHeightAtMost.finset_biUnion selected _ fun sig =>
    hasHeightAtMost_signatureFiber sig

/-- Every language recognized by `D ≀ᵣ C₂` has generalized star height at
most one when `D` is finite commutative. -/
theorem heightOneForGroup : HeightOneForGroup (D ≀ᵣ C2) := by
  letI : Fintype (D ≀ᵣ C2) := Fintype.ofFinite (D ≀ᵣ C2)
  exact heightOneForGroup_of_fullIdentityFiber hasHeightAtMost_fullIdentityFiber

end
end C2Wreath
end GSH
