import GSH.StarFree.LocalDivisor
import GSH.StarFree.MarkedCode
import GSH.Regex.CountHeight
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-!
# Towards Schützenberger's theorem: the ingredients of the induction

The local-divisor proof of "recognized by a finite aperiodic monoid ⇒
star-free" (`L-SF-004`) runs a lexicographic induction on
`(|M|, |S|)` where `S` is the set of admissible letters.  This file collects
the ingredients that are independent of the induction itself:

1. `eval`, the evaluation of a word under a letter map, and `lettersIn`, the
   star-free language of words over a finite letter set;
2. `eq_one_of_isUnit`: the units of an aperiodic monoid are trivial, so a
   letter with `f c ≠ 1` is **not** a unit and `LocalDivisor.LocalDiv.card_lt`
   applies;
3. `exists_marker_decomposition`: a word containing the marker `c` splits as
   `u₀ ++ (b ++ [c]) ++ u₁` with `u₀, u₁` marker-free and `b` empty or
   beginning with `c` — that is, `b` is exactly a word in the image of the
   block substitution of `GSH/StarFree/MarkedCode.lean`;
4. `eval_subst`: the evaluation of `b ++ [c]` for a block word `b` is the
   product **in the local divisor** of the block values.  This is the identity
   that converts the middle part of a word into an element of `M_{f c}`.

The remaining step is the induction itself (`L-SF-004`).

This file contains no `sorry` and no `axiom`.
-/

set_option autoImplicit false

namespace GSH
namespace Schutzenberger

universe u

/-! ## 1.  Evaluation and letter sets -/

variable {A M : Type u}

/-- Evaluate a word by multiplying the images of its letters. -/
def eval [Monoid M] (f : A → M) : Word A → M
  | [] => 1
  | a :: w => f a * eval f w

@[simp] theorem eval_nil [Monoid M] (f : A → M) : eval f [] = 1 := rfl

@[simp] theorem eval_cons [Monoid M] (f : A → M) (a : A) (w : Word A) :
    eval f (a :: w) = f a * eval f w := rfl

theorem eval_append [Monoid M] (f : A → M) :
    ∀ u v : Word A, eval f (u ++ v) = eval f u * eval f v
  | [], v => by simp
  | a :: u, v => by
    simp only [List.cons_append, eval_cons, eval_append f u v, mul_assoc]

@[simp] theorem eval_singleton [Monoid M] (f : A → M) (a : A) :
    eval f [a] = f a := by simp

/-- Words all of whose letters lie in `S`. -/
def lettersIn [DecidableEq A] (S : Finset A) : Language A := {w : Word A | ∀ a ∈ w, a ∈ S}

theorem hasHeightAtMost_lettersIn [Fintype A] [DecidableEq A] (S : Finset A) :
    HasHeightAtMost (lettersIn S) 0 := by
  refine ⟨CountHeight.avoidSet (Finset.univ \ S).toList, ?_,
    le_of_eq (CountHeight.starHeight_avoidSet _)⟩
  rw [CountHeight.denote_avoidSet]
  ext w
  simp only [lettersIn, Set.mem_setOf_eq, Finset.mem_toList, Finset.mem_sdiff,
    Finset.mem_univ, true_and]
  constructor
  · intro h a ha
    by_contra hs
    exact h a hs ha
  · intro h a ha hw
    exact ha (h a hw)

/-! ## 2.  Aperiodic monoids have no nontrivial units -/

theorem eq_one_of_isUnit [Monoid M] (hM : IsAperiodicMonoid M) {x : M}
    (hx : IsUnit x) : x = 1 := by
  obtain ⟨U, rfl⟩ := hx
  obtain ⟨n, hn⟩ := hM (U : M)
  have hU : U ^ (n + 1) = U ^ n := by
    apply Units.ext
    simpa using hn
  have : U ^ n * U = U ^ n * 1 := by rw [mul_one, ← pow_succ]; exact hU
  have hU1 : U = 1 := mul_left_cancel this
  rw [hU1]
  rfl

/-! ## 3.  Splitting a word at its first and last marker -/

theorem exists_split_last [DecidableEq A] (c : A) :
    ∀ w : Word A, c ∈ w → ∃ p u, w = p ++ [c] ++ u ∧ c ∉ u
  | [], h => absurd h (by simp)
  | x :: w, h => by
    by_cases hw : c ∈ w
    · obtain ⟨p, u, hpu, hu⟩ := exists_split_last c w hw
      exact ⟨x :: p, u, by rw [hpu]; simp, hu⟩
    · have hx : x = c := by
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact h.symm
        · exact absurd h hw
      exact ⟨[], w, by rw [hx]; simp, hw⟩

/-- A word containing the marker splits as `u₀ ++ (b ++ [c]) ++ u₁` with
`u₀`, `u₁` marker-free and `b` empty or beginning with the marker. -/
theorem exists_marker_decomposition [DecidableEq A] (c : A) (w : Word A) (hc : c ∈ w) :
    ∃ u₀ b u₁, w = u₀ ++ (b ++ [c]) ++ u₁ ∧ c ∉ u₀ ∧ c ∉ u₁ ∧
      (b = [] ∨ ∃ t, b = c :: t) := by
  obtain ⟨u₀, r, hw, hu₀, hr⟩ := MarkedCode.exists_split_first c w
  have hrc : c ∈ r := by
    rcases hr with rfl | ⟨t, rfl⟩
    · exfalso
      rw [hw, List.append_nil] at hc
      exact hu₀ hc
    · simp
  obtain ⟨p, u₁, hpu, hu₁⟩ := exists_split_last c r hrc
  refine ⟨u₀, p, u₁, by rw [hw, hpu]; simp, hu₀, hu₁, ?_⟩
  rcases hr with rfl | ⟨t, hrt⟩
  · exact absurd hrc (by simp)
  · cases p with
    | nil => exact Or.inl rfl
    | cons y p' =>
      refine Or.inr ⟨p', ?_⟩
      have : (y :: p') ++ [c] ++ u₁ = c :: t := by rw [← hpu, hrt]
      simp only [List.cons_append] at this
      rw [(List.cons.inj this).1]

/-! ## 4.  Block words evaluate to local-divisor products -/

open LocalDivisor

/-- If every block of index `γ` has value `val γ` in the local divisor at
`f c`, then a block word followed by one more marker evaluates to the
local-divisor product of the block values. -/
theorem eval_subst [Monoid M] (f : A → M) (c : A) {Γ : Type u}
    (L : Γ → Language A) (val : Γ → LocalDiv (f c)) :
    ∀ (k : Word Γ) (b : Word A),
      (∀ γ ∈ k, ∀ u ∈ L γ, (val γ).val = f c * eval f u * f c) →
      b ∈ MarkedCode.subst c L k →
      eval f (b ++ [c]) = (eval val k).val
  | [], b, _, hb => by
    rw [show b = [] from hb]
    simp [eval, LocalDiv.one_val]
  | γ :: k, b, hval, hb => by
    obtain ⟨u, hu, b', hb', rfl⟩ := hb
    have hrec := eval_subst f c L val k b'
      (fun γ' hγ' => hval γ' (by simp [hγ'])) hb'
    have hx : (val γ).val = (f c * eval f u) * (f c) := by
      rw [hval γ (by simp) u hu, mul_assoc]
    have hleft : eval f (c :: (u ++ b') ++ [c])
        = f c * eval f u * eval f (b' ++ [c]) := by
      simp only [List.cons_append, eval_cons, eval_append, mul_assoc]
    rw [hleft, hrec, eval_cons, LocalDiv.mul_val_left (val γ) (eval val k) hx,
      mul_assoc]

/-! ## 5.  Finite unions -/

theorem hasHeightAtMost_biUnion {ι : Type*} [DecidableEq ι] (F : ι → Language A) :
    ∀ (T : Finset ι), (∀ i ∈ T, HasHeightAtMost (F i) 0) →
      HasHeightAtMost (⋃ i ∈ T, F i) 0 := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    simpa using (hasHeightAtMost_empty : HasHeightAtMost (∅ : Language A) 0)
  | insert a T ha IH =>
    intro hF
    have hins : (⋃ i ∈ insert a T, F i) = F a ∪ ⋃ i ∈ T, F i := by
      ext w
      simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union, exists_prop]
      constructor
      · rintro ⟨i, hi | hi, hw⟩
        · exact Or.inl (by rw [← hi]; exact hw)
        · exact Or.inr ⟨i, hi, hw⟩
      · rintro (hw | ⟨i, hi, hw⟩)
        · exact ⟨a, Or.inl rfl, hw⟩
        · exact ⟨i, Or.inr hi, hw⟩
    rw [hins]
    exact hasHeightAtMost_union (hF a (by simp))
      (IH fun i hi => hF i (by simp [hi]))

/-! ## 6.  Letters and indices of a block word -/

theorem subst_letters [DecidableEq A] {Γ : Type u} (c : A) (L : Γ → Language A)
    (S : Finset A) (hc : c ∈ S) :
    ∀ (k : Word Γ) (b : Word A),
      (∀ γ ∈ k, ∀ u ∈ L γ, ∀ a ∈ u, a ∈ S) → b ∈ MarkedCode.subst c L k →
      ∀ a ∈ b, a ∈ S
  | [], b, _, hb => by
    rw [show b = [] from hb]; simp
  | γ :: k, b, hLS, hb => by
    obtain ⟨u, hu, b', hb', rfl⟩ := hb
    intro a ha
    simp only [List.mem_cons, List.mem_append] at ha
    rcases ha with rfl | ha | ha
    · exact hc
    · exact hLS γ (by simp) u hu a ha
    · exact subst_letters c L S hc k b'
        (fun γ' hγ' => hLS γ' (by simp [hγ'])) hb' a ha

theorem subst_index [DecidableEq A] {Γ : Type u} (c : A) (L : Γ → Language A)
    (S : Finset A) (Q : Γ → Prop)
    (hQ : ∀ γ, ¬ Q γ → ∀ u ∈ L γ, ∃ a ∈ u, a ∉ S) :
    ∀ (k : Word Γ) (b : Word A), b ∈ MarkedCode.subst c L k → (∀ a ∈ b, a ∈ S) →
      ∀ γ ∈ k, Q γ
  | [], _, _, _ => by simp
  | γ :: k, b, hb, hS => by
    obtain ⟨u, hu, b', hb', rfl⟩ := hb
    intro γ' hγ'
    simp only [List.mem_cons] at hγ'
    rcases hγ' with rfl | hγ'
    · by_contra hnq
      obtain ⟨a, ha, haS⟩ := hQ γ' hnq u hu
      exact haS (hS a (by simp [ha]))
    · exact subst_index c L S Q hQ k b' hb'
        (fun a ha => hS a (by simp [ha])) γ' hγ'

/-! ## 7.  The block family of the induction step -/

open LocalDivisor in
/-- The local-divisor value of a marker-free block. -/
def blockVal [Monoid M] (f : A → M) (c : A) (u : Word A) : LocalDiv (f c) :=
  ⟨f c * eval f u * f c,
    ⟨⟨eval f u * f c, by rw [mul_assoc]⟩, ⟨f c * eval f u, rfl⟩⟩⟩

@[simp] theorem blockVal_val [Monoid M] (f : A → M) (c : A) (u : Word A) :
    (blockVal f c u).val = f c * eval f u * f c := rfl

/-- The family of blocks, indexed by their local-divisor value; the extra
index `none` collects the marker-free words that use a letter outside `S`,
which is what makes the family **cover** all marker-free words. -/
def blockFam [DecidableEq A] [Monoid M] (f : A → M) (S : Finset A) (c : A) :
    Option (LocalDivisor.LocalDiv (f c)) → Language A
  | none => {u : Word A | c ∉ u ∧ ¬ (∀ a ∈ u, a ∈ S)}
  | some z => {u : Word A | (∀ a ∈ u, a ∈ S.erase c) ∧ blockVal f c u = z}

variable [DecidableEq A] [Monoid M]

theorem blockFam_markerFree (f : A → M) (S : Finset A) (c : A) :
    ∀ γ, ∀ u ∈ blockFam f S c γ, c ∉ u := by
  rintro (_ | z) u hu
  · exact hu.1
  · intro hc
    exact (Finset.mem_erase.1 (hu.1 c hc)).1 rfl

theorem blockFam_disjoint (f : A → M) (S : Finset A) (c : A) :
    ∀ {γ γ' : Option (LocalDivisor.LocalDiv (f c))} {u : Word A},
      u ∈ blockFam f S c γ → u ∈ blockFam f S c γ' → γ = γ' := by
  rintro (_ | z) (_ | z') u hu hu'
  · rfl
  · exact absurd (fun a ha => Finset.mem_of_mem_erase (hu'.1 a ha)) hu.2
  · exact absurd (fun a ha => Finset.mem_of_mem_erase (hu.1 a ha)) hu'.2
  · rw [← hu.2, ← hu'.2]

theorem blockFam_cover (f : A → M) (S : Finset A) (c : A) :
    ∀ u : Word A, c ∉ u → ∃ γ, u ∈ blockFam f S c γ := by
  intro u hu
  by_cases hS : ∀ a ∈ u, a ∈ S
  · exact ⟨some (blockVal f c u),
      fun a ha => Finset.mem_erase.2 ⟨fun h => hu (h ▸ ha), hS a ha⟩, rfl⟩
  · exact ⟨none, hu, hS⟩

/-- Only the `none` index can carry a block leaving `S`. -/
theorem blockFam_escapes (f : A → M) (S : Finset A) (c : A) :
    ∀ γ : Option (LocalDivisor.LocalDiv (f c)), ¬ (γ ≠ none) →
      ∀ u ∈ blockFam f S c γ, ∃ a ∈ u, a ∉ S := by
  rintro (_ | z) hγ u hu
  · by_contra hcon
    push_neg at hcon
    exact hu.2 hcon
  · exact absurd (by simp) hγ

theorem lettersIn_univ_erase [Fintype A] [DecidableEq A] (c : A) :
    lettersIn (Finset.univ.erase c) = {w : Word A | c ∉ w} := by
  ext w
  simp only [lettersIn, Set.mem_setOf_eq, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · intro h hc; exact (h c hc) rfl
  · intro h a ha hac; exact h (hac ▸ ha)

/-! ## 8.  The inductive step -/

open LocalDivisor MarkedCode in
/-- The step of the local-divisor induction: given the inner induction
hypothesis at `S.erase c` and the outer one at the local divisor of `f c`,
every fibre over `S` is star-free. -/
theorem step_case {A M : Type u} [Fintype A] [DecidableEq A]
    [Monoid M] [Fintype M] [DecidableEq M]
    (f : A → M) (S : Finset A) (c : A) (hcS : c ∈ S)
    (IHk : ∀ m' : M,
      HasHeightAtMost (lettersIn (S.erase c) ∩ {w : Word A | eval f w = m'}) 0)
    (IHn : ∀ z : LocalDiv (f c),
      HasHeightAtMost
        {k : Word (Option (LocalDiv (f c))) | eval (fun γ => γ.getD 1) k = z} 0)
    (m : M) :
    HasHeightAtMost (lettersIn S ∩ {w : Word A | eval f w = m}) 0 := by
  classical
  set L : Option (LocalDiv (f c)) → Language A := blockFam f S c with hLdef
  set val : Option (LocalDiv (f c)) → LocalDiv (f c) := fun γ => γ.getD 1 with hvaldef
  -- the index language of a target value
  set Kz : LocalDiv (f c) → Language (Option (LocalDiv (f c))) := fun z =>
    lettersIn (Finset.univ.erase (none : Option (LocalDiv (f c))))
      ∩ {k | eval val k = z} with hKzdef
  -- the value hypothesis of `eval_subst`, available on `none`-free indices
  have hval : ∀ k : Word (Option (LocalDiv (f c))),
      (∀ γ ∈ k, γ ≠ none) →
      ∀ γ ∈ k, ∀ u ∈ L γ, (val γ).val = f c * eval f u * f c := by
    intro k hk γ hγ u hu
    rcases hne : γ with _ | z
    · exact absurd hne (hk γ hγ)
    · subst hne
      have : blockVal f c u = z := hu.2
      rw [hvaldef]
      simp only [Option.getD_some]
      rw [← this, blockVal_val]
  -- each block language is star-free
  have hsf : ∀ γ, HasHeightAtMost (L γ) 0 := by
    rintro (_ | z)
    · have hset : L none
          = lettersIn (Finset.univ.erase c) ∩ Language.compl (lettersIn S) := by
        rw [hLdef, lettersIn_univ_erase]
        rfl
      rw [hset]
      exact hasHeightAtMost_inter (hasHeightAtMost_lettersIn _)
        (hasHeightAtMost_compl (hasHeightAtMost_lettersIn S))
    · have hset : L (some z)
          = ⋃ m' ∈ Finset.univ.filter (fun m' : M => f c * m' * f c = z.val),
              (lettersIn (S.erase c) ∩ {w : Word A | eval f w = m'}) := by
        ext u
        simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
        constructor
        · intro hu
          refine ⟨eval f u, ?_, hu.1, rfl⟩
          have : blockVal f c u = z := hu.2
          rw [← this, blockVal_val]
        · rintro ⟨m', hm', hlet, rfl⟩
          exact ⟨hlet, Subtype.ext (by rw [blockVal_val, hm'])⟩
      rw [hset]
      exact hasHeightAtMost_biUnion _ _ (fun m' _ => IHk m')
  -- the middle factor
  have hmid : ∀ z : LocalDiv (f c),
      HasHeightAtMost
        (Language.concat (substLang c L (Kz z)) (Language.letter c)) 0 := by
    intro z
    refine hasHeightAtMost_concat ?_ ⟨GRegex.atom c, rfl, by simp⟩
    refine hasHeightAtMost_substLang (blockFam_markerFree f S c)
      (blockFam_disjoint f S c) (blockFam_cover f S c) hsf ?_
    exact hasHeightAtMost_inter (hasHeightAtMost_lettersIn _) (IHn z)
  -- the decomposition
  set Tri : Finset (M × LocalDiv (f c) × M) :=
    Finset.univ.filter (fun t => t.1 * (t.2.1).val * t.2.2 = m) with hTri
  have hdecomp : lettersIn S ∩ {w : Word A | eval f w = m}
      = (lettersIn (S.erase c) ∩ {w : Word A | eval f w = m})
        ∪ ⋃ t ∈ Tri,
            Language.concat (lettersIn (S.erase c) ∩ {w : Word A | eval f w = t.1})
              (Language.concat
                (Language.concat (substLang c L (Kz t.2.1)) (Language.letter c))
                (lettersIn (S.erase c) ∩ {w : Word A | eval f w = t.2.2})) := by
    ext w
    constructor
    · rintro ⟨hlet, hev⟩
      by_cases hc : c ∈ w
      · right
        obtain ⟨u₀, b, u₁, rfl, hu₀, hu₁, hb⟩ := exists_marker_decomposition c w hc
        have hlet₀ : ∀ a ∈ u₀, a ∈ S.erase c := fun a ha =>
          Finset.mem_erase.2 ⟨fun h => hu₀ (h ▸ ha), hlet a (by simp [ha])⟩
        have hlet₁ : ∀ a ∈ u₁, a ∈ S.erase c := fun a ha =>
          Finset.mem_erase.2 ⟨fun h => hu₁ (h ▸ ha), hlet a (by simp [ha])⟩
        have hbmark : b = [] ∨ ∃ v, b = c :: v := hb
        obtain ⟨k, hk⟩ :=
          exists_code (blockFam_cover f S c) b.length b (le_refl _) hbmark
        have hbS : ∀ a ∈ b, a ∈ S := fun a ha => hlet a (by simp [ha])
        have hknone : ∀ γ ∈ k, γ ≠ none :=
          subst_index c L S (fun γ => γ ≠ none) (blockFam_escapes f S c) k b hk hbS
        have hbc : eval f (b ++ [c]) = (eval val k).val :=
          eval_subst f c L val k b (hval k hknone) hk
        simp only [Set.mem_iUnion, exists_prop]
        refine ⟨(eval f u₀, eval val k, eval f u₁), ?_, ?_⟩
        · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
          rw [← hbc]
          simpa [eval_append, mul_assoc] using hev
        · refine ⟨u₀, ⟨hlet₀, rfl⟩, (b ++ [c]) ++ u₁,
            ⟨b ++ [c], ?_, u₁, ⟨hlet₁, rfl⟩, rfl⟩, by simp⟩
          exact ⟨b, ⟨k, ⟨fun γ hγ => Finset.mem_erase.2 ⟨hknone γ hγ, Finset.mem_univ _⟩,
            rfl⟩, hk⟩, [c], rfl, rfl⟩
      · left
        exact ⟨fun a ha => Finset.mem_erase.2 ⟨fun h => hc (h ▸ ha), hlet a ha⟩, hev⟩
    · rintro (⟨hlet, hev⟩ | hw)
      · exact ⟨fun a ha => Finset.mem_of_mem_erase (hlet a ha), hev⟩
      · simp only [Set.mem_iUnion, exists_prop] at hw
        obtain ⟨t, htT, u₀, ⟨hlet₀, hev₀⟩, rest, ⟨bc, hbc, u₁, ⟨hlet₁, hev₁⟩, rfl⟩, rfl⟩ := hw
        obtain ⟨b, ⟨k, hkK, hkb⟩, cw, hcw, rfl⟩ := hbc
        have hcw' : cw = [c] := hcw
        subst hcw'
        have hknone : ∀ γ ∈ k, γ ≠ none := fun γ hγ =>
          (Finset.mem_erase.1 (hkK.1 γ hγ)).1
        have hbcv : eval f (b ++ [c]) = (eval val k).val :=
          eval_subst f c L val k b (hval k hknone) hkb
        have hkz : eval val k = t.2.1 := hkK.2
        have htm : t.1 * (t.2.1).val * t.2.2 = m :=
          (Finset.mem_filter.1 (Finset.mem_coe.1 htT)).2
        have hbS : ∀ a ∈ b, a ∈ S := by
          refine subst_letters c L S hcS k b ?_ hkb
          intro γ hγ u hu
          rcases hne : γ with _ | z
          · exact absurd hne (hknone γ hγ)
          · subst hne
            exact fun a ha => Finset.mem_of_mem_erase (hu.1 a ha)
        constructor
        · intro a ha
          rcases List.mem_append.1 ha with h | h
          · exact Finset.mem_of_mem_erase (hlet₀ a h)
          · rcases List.mem_append.1 h with h | h
            · rcases List.mem_append.1 h with h | h
              · exact hbS a h
              · rw [List.mem_singleton.1 h]; exact hcS
            · exact Finset.mem_of_mem_erase (hlet₁ a h)
        · show eval f (u₀ ++ (b ++ [c] ++ u₁)) = m
          rw [eval_append, eval_append, hev₀, hev₁, hbcv, hkz, ← htm, mul_assoc]
  rw [hdecomp]
  refine hasHeightAtMost_union (IHk m) (hasHeightAtMost_biUnion _ Tri ?_)
  intro t _
  exact hasHeightAtMost_concat (IHk t.1)
    (hasHeightAtMost_concat (hmid t.2.1) (IHk t.2.2))

/-! ## 9.  The induction -/

open LocalDivisor in
/-- Lexicographic induction on `(|M|, |S|)`. -/
theorem fiber_aux : ∀ (n : Nat) (A M : Type u) [Fintype A] [DecidableEq A]
    [Monoid M] [Fintype M] [DecidableEq M],
    Fintype.card M ≤ n → IsAperiodicMonoid M →
    ∀ (kb : Nat) (f : A → M) (S : Finset A), S.card ≤ kb → ∀ m : M,
      HasHeightAtMost (lettersIn S ∩ {w : Word A | eval f w = m}) 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHn =>
  intro A M _ _ _ _ _ hcardM hM kb
  induction kb using Nat.strong_induction_on with
  | _ kb IHk =>
  intro f S hS m
  classical
  by_cases hall : ∀ a ∈ S, f a = 1
  · -- every admissible letter is neutral
    have hev : ∀ w : Word A, (∀ a ∈ w, a ∈ S) → eval f w = 1 := by
      intro w
      induction w with
      | nil => intro _; rfl
      | cons a w ih =>
        intro h
        rw [eval_cons, hall a (h a (by simp)), one_mul,
          ih fun x hx => h x (by simp [hx])]
    by_cases hm : m = 1
    · have hset : lettersIn S ∩ {w : Word A | eval f w = m} = lettersIn S := by
        ext w
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_iff_left_iff_imp]
        intro hw
        rw [hev w hw, hm]
      rw [hset]
      exact hasHeightAtMost_lettersIn S
    · have hset : lettersIn S ∩ {w : Word A | eval f w = m} = ∅ := by
        ext w
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro hw he
        exact hm (by rw [← he, hev w hw])
      rw [hset]
      exact hasHeightAtMost_empty
  · -- some admissible letter is not neutral
    push_neg at hall
    obtain ⟨c, hcS, hc1⟩ := hall
    refine step_case f S c hcS ?_ ?_ m
    · intro m'
      refine IHk (S.erase c).card ?_ f (S.erase c) (le_refl _) m'
      have hlt : (S.erase c).card < S.card := Finset.card_erase_lt_of_mem hcS
      omega
    · intro z
      have hnu : ¬ IsUnit (f c) := fun h => hc1 (eq_one_of_isUnit hM h)
      have hlt : Fintype.card (LocalDiv (f c)) < Fintype.card M :=
        LocalDiv.card_lt hnu
      have hres := IHn (Fintype.card (LocalDiv (f c))) (by omega)
        (Option (LocalDiv (f c))) (LocalDiv (f c)) (le_refl _)
        (LocalDiv.isAperiodic hM (f c))
        (Finset.univ : Finset (Option (LocalDiv (f c)))).card
        (fun γ => γ.getD 1) Finset.univ (le_refl _) z
      have huniv : lettersIn (Finset.univ : Finset (Option (LocalDiv (f c))))
          = Set.univ := by
        ext k; simp [lettersIn]
      rwa [huniv, Set.univ_inter] at hres

/-- **Schützenberger's theorem, hard direction** (`L-SF-004`): every fibre of a
letter map into a finite aperiodic monoid is star-free. -/
theorem fiber_isStarFree {A M : Type u} [Fintype A] [DecidableEq A]
    [Monoid M] [Fintype M] [DecidableEq M]
    (hM : IsAperiodicMonoid M) (f : A → M) (m : M) :
    HasHeightAtMost {w : Word A | eval f w = m} 0 := by
  have h := fiber_aux (Fintype.card M) A M (le_refl _) hM
    (Finset.univ : Finset A).card f Finset.univ (le_refl _) m
  have huniv : lettersIn (Finset.univ : Finset A) = Set.univ := by
    ext w; simp [lettersIn]
  rwa [huniv, Set.univ_inter] at h

/-- Every language recognized by a finite aperiodic monoid is star-free. -/
theorem recognized_isStarFree {A M : Type u} [Fintype A] [DecidableEq A]
    [Monoid M] [Fintype M] [DecidableEq M]
    (hM : IsAperiodicMonoid M) (f : A → M) (P : Set M) :
    HasHeightAtMost {w : Word A | eval f w ∈ P} 0 := by
  classical
  have hset : {w : Word A | eval f w ∈ P}
      = ⋃ m ∈ Finset.univ.filter (fun m : M => m ∈ P), {w : Word A | eval f w = m} := by
    ext w
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hw; exact ⟨eval f w, hw, rfl⟩
    · rintro ⟨m, hm, rfl⟩; exact hm
  rw [hset]
  exact hasHeightAtMost_biUnion _ _ (fun m _ => fiber_isStarFree hM f m)

end Schutzenberger
end GSH
