import GSH.Regex.HeightClosure

/-!
# Transfer along a marked code

Fix a letter `c` of the alphabet `A` and a family `L : Γ → Language A` of
languages of words **avoiding** `c`, which partitions the `c`-free words.  Each
index word `γ₁⋯γ_k ∈ Γ*` then denotes the set of words

    c u₁ c u₂ ⋯ c u_k ,      u_i ∈ L γ_i ,

and this *block substitution* is a bijection between `Γ*` and the words that
are empty or begin with `c`.  The main theorem of this file,
`hasHeightAtMost_substLang`, says that the substitution turns star-free
languages of index words into star-free languages of words.

This is the technical heart of the local-divisor proof of Schützenberger's
theorem (obligation `L-SF-003`).  Two features make it work:

* `c B*` is a prefix code of synchronization delay 1: the blocks are cut right
  before each `c`, so the decomposition is unique (`subst_inj`) and total on
  its image (`exists_code`);
* the image is `{ε} ∪ c A*`, which is itself **star-free** — this is what lets
  the complement case of the structural induction go through, complement being
  taken inside the image rather than inside `A*`.

This file contains no `sorry` and no `axiom`.
-/

set_option autoImplicit false

namespace GSH
namespace MarkedCode

universe u v

variable {A : Type u} {Γ : Type v}

/-! ## 1.  The block substitution -/

/-- `subst c L (γ₁ ⋯ γ_k)` is the set of words `c u₁ ⋯ c u_k` with
`u_i ∈ L γ_i`. -/
def subst (c : A) (L : Γ → Language A) : Word Γ → Language A
  | [] => {[]}
  | γ :: k => {w | ∃ u ∈ L γ, ∃ v ∈ subst c L k, w = c :: (u ++ v)}

@[simp] theorem subst_nil (c : A) (L : Γ → Language A) :
    subst c L [] = {([] : Word A)} := rfl

theorem mem_subst_cons {c : A} {L : Γ → Language A} {γ : Γ} {k : Word Γ}
    {w : Word A} :
    w ∈ subst c L (γ :: k) ↔ ∃ u ∈ L γ, ∃ v ∈ subst c L k, w = c :: (u ++ v) :=
  Iff.rfl

/-- The substitution of a whole language of index words. -/
def substLang (c : A) (L : Γ → Language A) (K : Language Γ) : Language A :=
  {w | ∃ k ∈ K, w ∈ subst c L k}

theorem mem_substLang {c : A} {L : Γ → Language A} {K : Language Γ}
    {w : Word A} : w ∈ substLang c L K ↔ ∃ k ∈ K, w ∈ subst c L k := Iff.rfl

/-- The substitution is a morphism for concatenation. -/
theorem subst_append (c : A) (L : Γ → Language A) :
    ∀ k₁ k₂ : Word Γ,
      subst c L (k₁ ++ k₂) = Language.concat (subst c L k₁) (subst c L k₂)
  | [], k₂ => by
    rw [List.nil_append, subst_nil]
    ext w
    simp only [Language.mem_concat_iff, Set.mem_singleton_iff]
    constructor
    · intro h; exact ⟨[], rfl, w, h, by simp⟩
    · rintro ⟨x, hx, y, hy, rfl⟩
      rw [show x = [] from hx, List.nil_append]; exact hy
  | γ :: k₁, k₂ => by
    ext w
    simp only [List.cons_append, mem_subst_cons, Language.mem_concat_iff]
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      rw [subst_append c L k₁ k₂] at hv
      obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := hv
      exact ⟨c :: (u ++ v₁), ⟨u, hu, v₁, hv₁, rfl⟩, v₂, hv₂, by simp⟩
    · rintro ⟨x, hx, y, hy, rfl⟩
      obtain ⟨u, hu, v, hv, rfl⟩ := hx
      refine ⟨u, hu, v ++ y, ?_, by simp⟩
      rw [subst_append c L k₁ k₂]
      exact ⟨v, hv, y, hy, rfl⟩

/-! ## 2.  Unique decoding -/

/-- Every substituted word is empty or begins with the marker. -/
theorem subst_shape (c : A) (L : Γ → Language A) :
    ∀ (k : Word Γ) (w : Word A), w ∈ subst c L k → w = [] ∨ ∃ v, w = c :: v
  | [], w, h => Or.inl h
  | _ :: _, _, ⟨u, _, v, _, rfl⟩ => Or.inr ⟨u ++ v, rfl⟩

/-- Splitting a marker-free prefix off a concatenation. -/
theorem eq_of_append_eq {c : A} :
    ∀ {u u' v v' : Word A}, c ∉ u → c ∉ u' →
      (v = [] ∨ ∃ t, v = c :: t) → (v' = [] ∨ ∃ t, v' = c :: t) →
      u ++ v = u' ++ v' → u = u' ∧ v = v'
  | [], u', v, v', _, hu', hv, _, h => by
    cases u' with
    | nil => exact ⟨rfl, by simpa using h⟩
    | cons x u'' =>
      exfalso
      simp only [List.nil_append, List.cons_append] at h
      rcases hv with rfl | ⟨t, rfl⟩
      · exact absurd h (by simp)
      · have hx : c = x := (List.cons.inj h).1
        exact hu' (by rw [← hx]; simp)
  | x :: u₁, u', v, v', hu, hu', hv, hv', h => by
    cases u' with
    | nil =>
      exfalso
      simp only [List.nil_append, List.cons_append] at h
      rcases hv' with rfl | ⟨t, rfl⟩
      · exact absurd h.symm (by simp)
      · have hx : x = c := (List.cons.inj h).1
        exact hu (by rw [hx]; simp)
    | cons x' u₁' =>
      simp only [List.cons_append] at h
      obtain ⟨hxx, htail⟩ := List.cons.inj h
      subst hxx
      obtain ⟨h1, h2⟩ :=
        eq_of_append_eq (u := u₁) (u' := u₁')
          (fun hc => hu (by simp [hc])) (fun hc => hu' (by simp [hc])) hv hv' htail
      exact ⟨by rw [h1], h2⟩

/-- Decoding is unique. -/
theorem subst_inj {c : A} {L : Γ → Language A}
    (hL : ∀ γ, ∀ u ∈ L γ, c ∉ u)
    (hdisj : ∀ {γ γ' : Γ} {u : Word A}, u ∈ L γ → u ∈ L γ' → γ = γ') :
    ∀ (k k' : Word Γ) (w : Word A),
      w ∈ subst c L k → w ∈ subst c L k' → k = k'
  | [], [], _, _, _ => rfl
  | [], γ' :: k', w, h, h' => by
    obtain ⟨u, _, v, _, hw⟩ := h'
    rw [show w = [] from h] at hw
    exact absurd hw (by simp)
  | γ :: k, [], w, h, h' => by
    obtain ⟨u, _, v, _, hw⟩ := h
    rw [show w = [] from h'] at hw
    exact absurd hw (by simp)
  | γ :: k, γ' :: k', w, h, h' => by
    obtain ⟨u, hu, v, hv, rfl⟩ := h
    obtain ⟨u', hu', v', hv', heq⟩ := h'
    have hcat : u ++ v = u' ++ v' := (List.cons.inj heq).2
    obtain ⟨hus, hvs⟩ :=
      eq_of_append_eq (hL γ u hu) (hL γ' u' hu')
        (subst_shape c L k v hv) (subst_shape c L k' v' hv') hcat
    subst hus
    subst hvs
    rw [hdisj hu hu', subst_inj hL hdisj k k' v hv hv']

/-- Splitting a word at its first marker. -/
theorem exists_split_first [DecidableEq A] (c : A) :
    ∀ v : Word A, ∃ u r, v = u ++ r ∧ c ∉ u ∧ (r = [] ∨ ∃ t, r = c :: t)
  | [] => ⟨[], [], rfl, by simp, Or.inl rfl⟩
  | x :: v => by
    by_cases hx : x = c
    · exact ⟨[], x :: v, rfl, by simp, Or.inr ⟨v, by rw [hx]⟩⟩
    · obtain ⟨u, r, hv, hu, hr⟩ := exists_split_first c v
      exact ⟨x :: u, r, by rw [hv]; simp, by simp [Ne.symm hx, hu], hr⟩

/-- Decoding is total on words that are empty or begin with the marker. -/
theorem exists_code [DecidableEq A] {c : A} {L : Γ → Language A}
    (hcover : ∀ u : Word A, c ∉ u → ∃ γ, u ∈ L γ) :
    ∀ (n : Nat) (w : Word A), w.length ≤ n → (w = [] ∨ ∃ v, w = c :: v) →
      ∃ k, w ∈ subst c L k
  | _, [], _, _ => ⟨[], rfl⟩
  | 0, x :: w, hlen, _ => by simp at hlen
  | n + 1, x :: w, hlen, hshape => by
    have hx : x = c := by
      rcases hshape with h | ⟨v, h⟩
      · exact absurd h (by simp)
      · exact (List.cons.inj h).1
    subst hx
    obtain ⟨u, r, hw, hu, hr⟩ := exists_split_first x w
    obtain ⟨γ, hγ⟩ := hcover u hu
    have hrlen : r.length ≤ n := by
      have : w.length = u.length + r.length := by rw [hw]; simp
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨k, hk⟩ := exists_code hcover n r hrlen hr
    exact ⟨γ :: k, ⟨u, hγ, r, hk, by rw [hw]⟩⟩

/-! ## 3.  The image of the substitution -/

/-- Words that are empty or begin with the marker. -/
def marked (c : A) : Language A := {w : Word A | w = [] ∨ ∃ v, w = c :: v}

theorem marked_eq_denote (c : A) :
    marked c
      = GRegex.denote (GRegex.union GRegex.epsilon
          (GRegex.concat (GRegex.atom c) GRegex.univ)) := by
  ext w
  simp only [marked, Set.mem_setOf_eq, GRegex.denote, Set.mem_union,
    Language.mem_epsilon_iff, Language.mem_concat_iff, Language.mem_letter_iff,
    GRegex.denote_univ, Set.mem_univ, and_true]
  constructor
  · rintro (rfl | ⟨v, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨[c], rfl, v, trivial, rfl⟩
  · rintro (rfl | ⟨x, rfl, v, _, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨v, rfl⟩

theorem hasHeightAtMost_marked (c : A) : HasHeightAtMost (marked c) 0 := by
  refine ⟨GRegex.union GRegex.epsilon (GRegex.concat (GRegex.atom c) GRegex.univ),
    (marked_eq_denote c).symm, ?_⟩
  change max (GRegex.starHeight GRegex.epsilon)
    (max (GRegex.starHeight (GRegex.atom c))
      (GRegex.starHeight (GRegex.univ : GRegex A))) ≤ 0
  simp

/-! ## 4.  The transfer theorem -/

theorem substLang_univ [DecidableEq A] {c : A} {L : Γ → Language A}
    (hcover : ∀ u : Word A, c ∉ u → ∃ γ, u ∈ L γ) :
    substLang c L Set.univ = marked c := by
  ext w
  constructor
  · rintro ⟨k, -, hk⟩
    exact subst_shape c L k w hk
  · intro hw
    obtain ⟨k, hk⟩ := exists_code hcover w.length w (le_refl _) hw
    exact ⟨k, trivial, hk⟩

theorem substLang_union (c : A) (L : Γ → Language A) (K₁ K₂ : Language Γ) :
    substLang c L (K₁ ∪ K₂) = substLang c L K₁ ∪ substLang c L K₂ := by
  ext w
  constructor
  · rintro ⟨k, hk | hk, hw⟩
    · exact Or.inl ⟨k, hk, hw⟩
    · exact Or.inr ⟨k, hk, hw⟩
  · rintro (⟨k, hk, hw⟩ | ⟨k, hk, hw⟩)
    · exact ⟨k, Or.inl hk, hw⟩
    · exact ⟨k, Or.inr hk, hw⟩

theorem substLang_concat (c : A) (L : Γ → Language A) (K₁ K₂ : Language Γ) :
    substLang c L (Language.concat K₁ K₂)
      = Language.concat (substLang c L K₁) (substLang c L K₂) := by
  ext w
  constructor
  · rintro ⟨k, ⟨k₁, hk₁, k₂, hk₂, rfl⟩, hw⟩
    rw [subst_append] at hw
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hw
    exact ⟨w₁, ⟨k₁, hk₁, hw₁⟩, w₂, ⟨k₂, hk₂, hw₂⟩, rfl⟩
  · rintro ⟨w₁, ⟨k₁, hk₁, hw₁⟩, w₂, ⟨k₂, hk₂, hw₂⟩, rfl⟩
    refine ⟨k₁ ++ k₂, ⟨k₁, hk₁, k₂, hk₂, rfl⟩, ?_⟩
    rw [subst_append]
    exact ⟨w₁, hw₁, w₂, hw₂, rfl⟩

/-- Complement is taken **inside the image** of the substitution; this is
where unique decoding is used. -/
theorem substLang_compl [DecidableEq A] {c : A} {L : Γ → Language A}
    (hL : ∀ γ, ∀ u ∈ L γ, c ∉ u)
    (hdisj : ∀ {γ γ' : Γ} {u : Word A}, u ∈ L γ → u ∈ L γ' → γ = γ')
    (hcover : ∀ u : Word A, c ∉ u → ∃ γ, u ∈ L γ) (K : Language Γ) :
    substLang c L (Language.compl K) = marked c ∩ Language.compl (substLang c L K) := by
  ext w
  constructor
  · rintro ⟨k, hk, hw⟩
    refine ⟨subst_shape c L k w hw, ?_⟩
    rintro ⟨k', hk', hw'⟩
    exact hk (by rw [subst_inj hL hdisj k k' w hw hw']; exact hk')
  · rintro ⟨hm, hn⟩
    obtain ⟨k, hk⟩ := exists_code hcover w.length w (le_refl _) hm
    exact ⟨k, fun hkK => hn ⟨k, hkK, hk⟩, hk⟩

theorem substLang_denote_atom (c : A) (L : Γ → Language A) (γ : Γ) :
    substLang c L (GRegex.denote (GRegex.atom γ))
      = Language.concat (Language.letter c) (L γ) := by
  ext w
  simp only [substLang, Set.mem_setOf_eq, GRegex.denote, Language.mem_letter_iff,
    Language.mem_concat_iff]
  constructor
  · rintro ⟨k, rfl, hw⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := hw
    rw [show v = [] from hv]
    exact ⟨[c], rfl, u, hu, by simp⟩
  · rintro ⟨x, rfl, u, hu, rfl⟩
    exact ⟨[γ], rfl, ⟨u, hu, [], rfl, by simp⟩⟩

/-- **Transfer along the marked code** (`L-SF-003`), by structural induction on
a star-free expression for the index language. -/
theorem hasHeightAtMost_substLang_denote [DecidableEq A] {c : A} {L : Γ → Language A}
    (hL : ∀ γ, ∀ u ∈ L γ, c ∉ u)
    (hdisj : ∀ {γ γ' : Γ} {u : Word A}, u ∈ L γ → u ∈ L γ' → γ = γ')
    (hcover : ∀ u : Word A, c ∉ u → ∃ γ, u ∈ L γ)
    (hsf : ∀ γ, HasHeightAtMost (L γ) 0) :
    ∀ r : GRegex Γ, GRegex.starHeight r = 0 →
      HasHeightAtMost (substLang c L (GRegex.denote r)) 0
  | GRegex.zero, _ => by
    have hz : substLang c L (GRegex.denote (GRegex.zero : GRegex Γ)) = ∅ := by
      ext w
      simp [substLang, GRegex.denote, Language.empty]
    rw [hz]
    exact hasHeightAtMost_empty
  | GRegex.epsilon, _ => by
    have he : substLang c L (GRegex.denote (GRegex.epsilon : GRegex Γ))
        = ({[]} : Language A) := by
      ext w
      simp only [substLang, Set.mem_setOf_eq, GRegex.denote,
        Language.mem_epsilon_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨k, rfl, hw⟩; exact hw
      · intro hw; exact ⟨[], rfl, hw⟩
    rw [he]
    exact ⟨GRegex.epsilon, rfl, by simp⟩
  | GRegex.atom γ, _ => by
    rw [substLang_denote_atom]
    exact hasHeightAtMost_concat ⟨GRegex.atom c, rfl, by simp⟩ (hsf γ)
  | GRegex.union r s, h => by
    have hr : GRegex.starHeight r = 0 := by
      simp only [GRegex.starHeight] at h; omega
    have hs : GRegex.starHeight s = 0 := by
      simp only [GRegex.starHeight] at h; omega
    show HasHeightAtMost (substLang c L (GRegex.denote r ∪ GRegex.denote s)) 0
    rw [substLang_union]
    exact hasHeightAtMost_union
      (hasHeightAtMost_substLang_denote hL hdisj hcover hsf r hr)
      (hasHeightAtMost_substLang_denote hL hdisj hcover hsf s hs)
  | GRegex.concat r s, h => by
    have hr : GRegex.starHeight r = 0 := by
      simp only [GRegex.starHeight] at h; omega
    have hs : GRegex.starHeight s = 0 := by
      simp only [GRegex.starHeight] at h; omega
    show HasHeightAtMost
      (substLang c L (Language.concat (GRegex.denote r) (GRegex.denote s))) 0
    rw [substLang_concat]
    exact hasHeightAtMost_concat
      (hasHeightAtMost_substLang_denote hL hdisj hcover hsf r hr)
      (hasHeightAtMost_substLang_denote hL hdisj hcover hsf s hs)
  | GRegex.compl r, h => by
    have hr : GRegex.starHeight r = 0 := by
      simp only [GRegex.starHeight] at h; omega
    show HasHeightAtMost (substLang c L (Language.compl (GRegex.denote r))) 0
    rw [substLang_compl hL hdisj hcover]
    exact hasHeightAtMost_inter (hasHeightAtMost_marked c)
      (hasHeightAtMost_compl
        (hasHeightAtMost_substLang_denote hL hdisj hcover hsf r hr))
  | GRegex.star r, h => by
    exfalso
    simp only [GRegex.starHeight] at h
    omega

/-- Star-free index languages substitute to star-free languages. -/
theorem hasHeightAtMost_substLang [DecidableEq A] {c : A} {L : Γ → Language A}
    (hL : ∀ γ, ∀ u ∈ L γ, c ∉ u)
    (hdisj : ∀ {γ γ' : Γ} {u : Word A}, u ∈ L γ → u ∈ L γ' → γ = γ')
    (hcover : ∀ u : Word A, c ∉ u → ∃ γ, u ∈ L γ)
    (hsf : ∀ γ, HasHeightAtMost (L γ) 0)
    {K : Language Γ} (hK : HasHeightAtMost K 0) :
    HasHeightAtMost (substLang c L K) 0 := by
  obtain ⟨r, hr, hh⟩ := hK
  have hres :=
    hasHeightAtMost_substLang_denote hL hdisj hcover hsf r (Nat.le_zero.mp hh)
  rwa [hr] at hres

end MarkedCode
end GSH
