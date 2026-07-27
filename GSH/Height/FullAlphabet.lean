import GSH.Height.Closure
import GSH.Recognition

/-!
# Full-alphabet reduction

This file formalizes the two elementary closure lemmas used by the
full-alphabet reduction:

* inverse images under a non-erasing letter-to-letter map do not increase
  generalized star height;
* a one-letter left quotient, implemented by a Brzozowski derivative, does
  not increase generalized star height.

For a finite group `G`, these lemmas reduce `HeightOneForGroup G` to the
single language `fullIdentityFiber G` over the alphabet whose letters are all
elements of `G`.
-/

set_option autoImplicit false

namespace GSH

universe u v w

namespace Language

variable {α : Type u} {β : Type v}

/-- Inverse image of a language under the word map induced letter-by-letter
by `f`.  Since each input letter maps to exactly one output letter, this word
map preserves length. -/
def inverseLetterMap (f : α → β) (L : Language β) : Language α :=
  {word | word.map f ∈ L}

@[simp] theorem mem_inverseLetterMap_iff (f : α → β) (L : Language β) (word : Word α) :
    word ∈ inverseLetterMap f L ↔ word.map f ∈ L := by
  rfl

/-- Left quotient by the one-letter word `[a]`. -/
def leftQuotient (a : α) (L : Language α) : Language α :=
  {word | a :: word ∈ L}

@[simp] theorem mem_leftQuotient_iff (a : α) (L : Language α) (word : Word α) :
    word ∈ leftQuotient a L ↔ a :: word ∈ L := by
  rfl

theorem inverseLetterMap_concat (f : α → β) (L K : Language β) :
    inverseLetterMap f (concat L K) =
      concat (inverseLetterMap f L) (inverseLetterMap f K) := by
  ext word
  constructor
  · rintro ⟨left, hleft, right, hright, hsplit⟩
    let inputLeft := word.take left.length
    let inputRight := word.drop left.length
    have hmapLeft : inputLeft.map f = left := by
      have h := congrArg (List.take left.length) hsplit
      simpa [inputLeft] using h.symm
    have hmapRight : inputRight.map f = right := by
      have h := congrArg (List.drop left.length) hsplit
      simpa [inputRight] using h.symm
    refine ⟨inputLeft, ?_, inputRight, ?_, List.take_append_drop left.length word⟩
    · show inputLeft.map f ∈ L
      rw [hmapLeft]
      exact hleft
    · show inputRight.map f ∈ K
      rw [hmapRight]
      exact hright
  · rintro ⟨left, hleft, right, hright, rfl⟩
    exact ⟨left.map f, hleft, right.map f, hright, by simp⟩

theorem inverseLetterMap_power (f : α → β) (L : Language β) (n : Nat) :
    inverseLetterMap f (power L n) = power (inverseLetterMap f L) n := by
  induction n with
  | zero =>
      ext word
      simp [inverseLetterMap, power, epsilon]
  | succ n ih =>
      rw [power_succ, inverseLetterMap_concat, ih, power_succ]

theorem inverseLetterMap_star (f : α → β) (L : Language β) :
    inverseLetterMap f (star L) = star (inverseLetterMap f L) := by
  ext word
  simp only [mem_inverseLetterMap_iff, mem_star_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by
      have := Set.ext_iff.mp (inverseLetterMap_power f L n) word
      exact this.mp hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by
      have := Set.ext_iff.mp (inverseLetterMap_power f L n) word
      exact this.mpr hn⟩

theorem concat_assoc (L K H : Language α) :
    concat (concat L K) H = concat L (concat K H) := by
  ext word
  constructor
  · rintro ⟨leftMiddle, ⟨left, hleft, middle, hmiddle, rfl⟩,
      right, hright, rfl⟩
    exact ⟨left, hleft, middle ++ right,
      ⟨middle, hmiddle, right, hright, rfl⟩, (List.append_assoc ..).symm⟩
  · rintro ⟨left, hleft, middleRight,
      ⟨middle, hmiddle, right, hright, rfl⟩, rfl⟩
    exact ⟨left ++ middle, ⟨left, hleft, middle, hmiddle, rfl⟩,
      right, hright, List.append_assoc ..⟩

theorem power_succ_left (L : Language α) (n : Nat) :
    power L (n + 1) = concat L (power L n) := by
  induction n with
  | zero =>
      ext word
      simp [power, concat, epsilon]
  | succ n ih =>
      calc
        power L (Nat.succ n + 1) = concat (power L (n + 1)) L := by
          rw [power_succ]
        _ = concat (concat L (power L n)) L := congrArg (fun K => concat K L) ih
        _ = concat L (concat (power L n) L) := concat_assoc L (power L n) L
        _ = concat L (power L (Nat.succ n)) :=
          congrArg (concat L) (power_succ L n).symm

theorem mem_leftQuotient_concat_iff (a : α) (L K : Language α) (word : Word α) :
    word ∈ leftQuotient a (concat L K) ↔
      word ∈ concat (leftQuotient a L) K ∨
        ([] ∈ L ∧ word ∈ leftQuotient a K) := by
  constructor
  · rintro ⟨left, hleft, right, hright, hsplit⟩
    cases left with
    | nil =>
        right
        constructor
        · exact hleft
        · simpa using hsplit ▸ hright
    | cons b left =>
        left
        have hhead : b = a := by
          simpa using congrArg List.head? hsplit
        subst b
        have htail : left ++ right = word := by
          simpa using congrArg List.tail hsplit
        exact ⟨left, hleft, right, hright, htail⟩
  · rintro (h | ⟨hempty, hright⟩)
    · obtain ⟨left, hleft, right, hright, rfl⟩ := h
      exact ⟨a :: left, hleft, right, hright, rfl⟩
    · exact ⟨[], hempty, a :: word, hright, rfl⟩

theorem mem_leftQuotient_star_iff (a : α) (L : Language α) (word : Word α) :
    word ∈ leftQuotient a (star L) ↔
      word ∈ concat (leftQuotient a L) (star L) := by
  constructor
  · rintro ⟨n, hn⟩
    induction n generalizing word with
    | zero =>
        simp [power, epsilon] at hn
    | succ n ih =>
        rw [power_succ_left] at hn
        obtain ⟨first, hfirst, rest, hrest, hsplit⟩ := hn
        cases first with
        | nil =>
            apply ih
            simpa using hsplit ▸ hrest
        | cons b first =>
            have hhead : b = a := by
              simpa using congrArg List.head? hsplit
            subst b
            have htail : first ++ rest = word := by
              simpa using congrArg List.tail hsplit
            exact ⟨first, hfirst, rest, ⟨n, hrest⟩, htail⟩
  · rintro ⟨first, hfirst, rest, ⟨n, hrest⟩, rfl⟩
    exact ⟨n + 1, by
      rw [power_succ_left]
      exact ⟨a :: first, hfirst, rest, hrest, rfl⟩⟩

end Language

namespace GRegex

variable {α : Type u} {β : Type v}

/-- A finite union of one-letter atoms. -/
def atomUnion : List α → GRegex α
  | [] => zero
  | a :: letters => union (atom a) (atomUnion letters)

@[simp] theorem mem_denote_atomUnion_iff (letters : List α) (word : Word α) :
    word ∈ denote (atomUnion letters) ↔ ∃ a ∈ letters, word = [a] := by
  induction letters with
  | nil => simp [atomUnion, denote, Language.empty]
  | cons a letters ih =>
      simp [atomUnion, denote, Language.letter, ih]

@[simp] theorem starHeight_atomUnion (letters : List α) :
    starHeight (atomUnion letters) = 0 := by
  induction letters with
  | nil => rfl
  | cons _ letters ih => simp [atomUnion, starHeight, ih]

/-- The union of all input letters that `f` sends to `b`.

This is marked `noncomputable` only because `Finset.toList` chooses an order
for the finite union; the denoted language is independent of that order. -/
noncomputable def atomPreimage [Fintype α] [DecidableEq β]
    (f : α → β) (b : β) : GRegex α :=
  atomUnion ((Finset.univ.filter fun a => f a = b).toList)

@[simp] theorem mem_denote_atomPreimage_iff [Fintype α] [DecidableEq β]
    (f : α → β) (b : β) (word : Word α) :
    word ∈ denote (atomPreimage f b) ↔ word.map f = [b] := by
  simp only [atomPreimage, mem_denote_atomUnion_iff, Finset.mem_toList,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, hfa, rfl⟩
    simp [hfa]
  · intro h
    cases word with
    | nil => simp at h
    | cons a tail =>
        have htail : tail = [] := by
          simpa using congrArg List.tail h
        subst tail
        have hfa : f a = b := by
          simpa using congrArg List.head? h
        exact ⟨a, hfa, rfl⟩

/-- Pull a generalized expression back along a non-erasing letter-to-letter
map.  An output atom is replaced by the finite union of its input preimage. -/
noncomputable def inverseLetterMap [Fintype α] [DecidableEq β]
    (f : α → β) : GRegex β → GRegex α
  | zero => zero
  | epsilon => epsilon
  | atom b => atomPreimage f b
  | union r s => union (inverseLetterMap f r) (inverseLetterMap f s)
  | concat r s => concat (inverseLetterMap f r) (inverseLetterMap f s)
  | compl r => compl (inverseLetterMap f r)
  | star r => star (inverseLetterMap f r)

theorem denote_inverseLetterMap [Fintype α] [DecidableEq β]
    (f : α → β) (r : GRegex β) :
    denote (inverseLetterMap f r) = Language.inverseLetterMap f (denote r) := by
  induction r with
  | zero =>
      ext word
      simp [inverseLetterMap, denote, Language.inverseLetterMap, Language.empty]
  | epsilon =>
      ext word
      simp [inverseLetterMap, denote, Language.inverseLetterMap, Language.epsilon]
  | atom b =>
      ext word
      simp [inverseLetterMap, denote, Language.inverseLetterMap, Language.letter]
  | union r s ihr ihs =>
      ext word
      simp [inverseLetterMap, denote, Language.inverseLetterMap, ihr, ihs]
  | concat r s ihr ihs =>
      simp only [inverseLetterMap, denote]
      rw [ihr, ihs]
      exact (Language.inverseLetterMap_concat f (denote r) (denote s)).symm
  | compl r ihr =>
      ext word
      simp [inverseLetterMap, denote, Language.inverseLetterMap, Language.compl, ihr]
  | star r ihr =>
      simp only [inverseLetterMap, denote]
      rw [ihr]
      exact (Language.inverseLetterMap_star f (denote r)).symm

/-- Pullback along a letter-to-letter map does not increase syntactic star
height. -/
theorem starHeight_inverseLetterMap_le [Fintype α] [DecidableEq β]
    (f : α → β) (r : GRegex β) :
    starHeight (inverseLetterMap f r) ≤ starHeight r := by
  induction r with
  | zero => exact le_rfl
  | epsilon => exact le_rfl
  | atom b => simp [inverseLetterMap, atomPreimage]
  | union r s ihr ihs =>
      exact max_le
        (ihr.trans (Nat.le_max_left _ _))
        (ihs.trans (Nat.le_max_right _ _))
  | concat r s ihr ihs =>
      exact max_le
        (ihr.trans (Nat.le_max_left _ _))
        (ihs.trans (Nat.le_max_right _ _))
  | compl r ihr => exact ihr
  | star r ihr => exact Nat.add_le_add_right ihr 1

/-- Whether the empty word belongs to the denotation of an expression. -/
def nullable : GRegex α → Bool
  | zero => false
  | epsilon => true
  | atom _ => false
  | union r s => nullable r || nullable s
  | concat r s => nullable r && nullable s
  | compl r => !nullable r
  | star _ => true

@[simp] theorem nullable_eq_true_iff (r : GRegex α) :
    nullable r = true ↔ [] ∈ denote r := by
  induction r with
  | zero => simp [nullable, denote, Language.empty]
  | epsilon => simp [nullable, denote, Language.epsilon]
  | atom a => simp [nullable, denote, Language.letter]
  | union r s ihr ihs => simp [nullable, denote, ihr, ihs]
  | concat r s ihr ihs =>
      simp only [nullable, Bool.and_eq_true, ihr, ihs, denote,
        Language.mem_concat_iff]
      constructor
      · rintro ⟨hr, hs⟩
        exact ⟨[], hr, [], hs, rfl⟩
      · rintro ⟨left, hleft, right, hright, hsplit⟩
        have : left = [] ∧ right = [] := List.append_eq_nil_iff.mp hsplit
        simpa [this.1, this.2] using And.intro hleft hright
  | compl r ihr =>
      simpa [nullable, denote, Language.compl] using not_congr ihr
  | star r ihr =>
      constructor
      · intro _
        exact ⟨0, rfl⟩
      · intro _
        rfl

/-- Brzozowski derivative by one letter. -/
def derivative [DecidableEq α] (a : α) : GRegex α → GRegex α
  | zero => zero
  | epsilon => zero
  | atom b => if a = b then epsilon else zero
  | union r s => union (derivative a r) (derivative a s)
  | concat r s =>
      union (concat (derivative a r) s)
        (if nullable r then derivative a s else zero)
  | compl r => compl (derivative a r)
  | star r => concat (derivative a r) (star r)

theorem denote_derivative [DecidableEq α] (a : α) (r : GRegex α) :
    denote (derivative a r) = Language.leftQuotient a (denote r) := by
  induction r with
  | zero =>
      ext word
      simp [derivative, denote, Language.leftQuotient, Language.empty]
  | epsilon =>
      ext word
      simp [derivative, denote, Language.leftQuotient, Language.epsilon]
  | atom b =>
      by_cases hab : a = b
      · subst b
        ext word
        simp [derivative, denote, Language.leftQuotient, Language.epsilon,
          Language.letter]
      · ext word
        simp [derivative, hab, denote, Language.leftQuotient, Language.empty,
          Language.letter]
  | union r s ihr ihs =>
      ext word
      simp [derivative, denote, Language.leftQuotient, ihr, ihs]
  | concat r s ihr ihs =>
      by_cases hnull : nullable r = true
      · have hempty : [] ∈ denote r := (nullable_eq_true_iff r).mp hnull
        ext word
        simp only [derivative, hnull, if_true, denote, Set.mem_union,
          ihr, ihs, Language.mem_leftQuotient_concat_iff]
        simp [hempty]
      · have hempty : [] ∉ denote r := by
          intro h
          exact hnull ((nullable_eq_true_iff r).mpr h)
        ext word
        simp only [derivative, hnull, Bool.false_eq, denote, Set.mem_union,
          ihr, Language.mem_leftQuotient_concat_iff]
        simp [hempty, denote, Language.empty]
  | compl r ihr =>
      ext word
      simp [derivative, denote, Language.leftQuotient, Language.compl, ihr]
  | star r ihr =>
      ext word
      simp only [derivative, denote, ihr, Language.mem_leftQuotient_star_iff]

/-- A one-letter derivative does not increase syntactic star height. -/
theorem starHeight_derivative_le [DecidableEq α] (a : α) (r : GRegex α) :
    starHeight (derivative a r) ≤ starHeight r := by
  induction r with
  | zero => exact le_rfl
  | epsilon => exact le_rfl
  | atom b =>
      by_cases hab : a = b <;> simp [derivative, hab]
  | union r s ihr ihs =>
      exact max_le
        (ihr.trans (Nat.le_max_left _ _))
        (ihs.trans (Nat.le_max_right _ _))
  | concat r s ihr ihs =>
      by_cases hnull : nullable r = true
      · simp only [derivative, hnull, if_true, starHeight]
        exact max_le
          (max_le
            (ihr.trans (Nat.le_max_left _ _))
            (Nat.le_max_right _ _))
          (ihs.trans (Nat.le_max_right _ _))
      · simp only [derivative, hnull, Bool.false_eq, starHeight]
        exact max_le
          (max_le
            (ihr.trans (Nat.le_max_left _ _))
            (Nat.le_max_right _ _))
          (Nat.zero_le _)
  | compl r ihr => exact ihr
  | star r ihr =>
      simp only [derivative, starHeight]
      exact max_le
        (ihr.trans (Nat.le_succ _))
        le_rfl

end GRegex

namespace HasHeightAtMost

variable {α : Type u} {β : Type v}

/-- Generalized star height is preserved under inverse images of non-erasing
letter-to-letter maps. -/
theorem inverseLetterMap [Fintype α] [DecidableEq β]
    {L : Language β} {n : Nat} (hL : HasHeightAtMost L n) (f : α → β) :
    HasHeightAtMost (Language.inverseLetterMap f L) n := by
  obtain ⟨r, hr, hh⟩ := hL
  exact ⟨GRegex.inverseLetterMap f r,
    (GRegex.denote_inverseLetterMap f r).trans (congrArg (Language.inverseLetterMap f) hr),
    (GRegex.starHeight_inverseLetterMap_le f r).trans hh⟩

/-- Generalized star height is preserved under a one-letter left quotient. -/
theorem leftQuotient [DecidableEq α]
    {L : Language α} {n : Nat} (hL : HasHeightAtMost L n) (a : α) :
    HasHeightAtMost (Language.leftQuotient a L) n := by
  obtain ⟨r, hr, hh⟩ := hL
  exact ⟨GRegex.derivative a r,
    (GRegex.denote_derivative a r).trans (congrArg (Language.leftQuotient a) hr),
    (GRegex.starHeight_derivative_le a r).trans hh⟩

end HasHeightAtMost

/-- The identity fibre of the canonical evaluation map from words whose
alphabet is the whole group. -/
def fullIdentityFiber (G : Type v) [Group G] : Language G :=
  {word | word.prod = 1}

@[simp] theorem mem_fullIdentityFiber_iff {G : Type v} [Group G] (word : Word G) :
    word ∈ fullIdentityFiber G ↔ word.prod = 1 := by
  rfl

/-- `fullIdentityFiber` is exactly the language recognized by the canonical
evaluation morphism that sends each group element, viewed as a letter, to
itself. -/
theorem fullIdentityFiber_eq_recognitionLanguage {G : Type v} [Group G] :
    fullIdentityFiber G =
      (Recognition.mk (FreeMonoid.lift (fun g : G => g)) ({1} : Set G)).language := by
  ext word
  simp [fullIdentityFiber, Recognition.language, FreeMonoid.lift_ofList]

/-- If the identity fibre over the full-element alphabet of a finite group has
generalized star height at most one, then every language recognized by that
group does.

The quantifiers in the conclusion are those of `HeightOneForGroup`: every
finite alphabet, every morphism from its free monoid, and every accepting
subset of `G`. -/
theorem heightOneForGroup_of_fullIdentityFiber
    {G : Type v} [Group G] [Fintype G]
    (hIdentity : HasHeightAtMost (fullIdentityFiber G) 1) :
    HeightOneForGroup.{u, v} G := by
  intro α _ _ R
  classical
  let f : α → G := fun a => R.morphism (FreeMonoid.of a)
  have hmorphism : R.morphism = FreeMonoid.lift f := by
    apply FreeMonoid.hom_eq
    intro a
    rfl
  have hword (word : Word α) :
      R.morphism (FreeMonoid.ofList word) = (word.map f).prod := by
    rw [hmorphism, FreeMonoid.lift_ofList]
  have hfiber (g : G) :
      Language.inverseLetterMap f
          (Language.leftQuotient g⁻¹ (fullIdentityFiber G)) =
        {word : Word α | R.morphism (FreeMonoid.ofList word) = g} := by
    ext word
    change (g⁻¹ :: word.map f).prod = 1 ↔
      R.morphism (FreeMonoid.ofList word) = g
    rw [List.prod_cons, ← hword]
    constructor
    · intro h
      exact (eq_of_inv_mul_eq_one h).symm
    · intro h
      rw [h]
      exact inv_mul_cancel g
  let accepting : Finset G := Finset.univ.filter fun g => g ∈ R.accepting
  have hdecomp :
      R.language =
        ⋃ g ∈ accepting,
          Language.inverseLetterMap f
            (Language.leftQuotient g⁻¹ (fullIdentityFiber G)) := by
    ext word
    simp_rw [hfiber]
    simp [accepting, Recognition.mem_language_iff]
  rw [hdecomp]
  exact HasHeightAtMost.finset_biUnion accepting _ fun g =>
    (hIdentity.leftQuotient g⁻¹).inverseLetterMap f

end GSH
