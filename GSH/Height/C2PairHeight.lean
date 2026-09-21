import GSH.Height.C2SelfLoopHeight

/-!
# Star-free fixed flip-pair blocks for the the `C₂` route

For phase-one letters `x` and `y`, a fixed pair block has the form
`Z* · x · Z* · y`, where `Z*` consists of phase-zero words.  The
block itself is star-free.  A height-zero local-pattern expression is proved
to denote the star of the block when `x` and `y` are distinct phase-one
letters.
-/

set_option autoImplicit false

namespace GSH

namespace C2PairHeight

universe u

open C2SelfLoopHeight

variable {α : Type u} [Fintype α] [DecidableEq α]
variable (phase : α → ZMod 2)

/-- Semantic fixed pair block `Z* · x · Z* · y`. -/
def pairBlock (x y : α) : Language α :=
  Language.concat
    (GRegex.denote (neutralWordsR phase))
    (Language.concat (Language.letter x)
      (Language.concat (GRegex.denote (neutralWordsR phase)) (Language.letter y)))

/-- Height-zero expression for one fixed pair block. -/
noncomputable def pairBlockR (x y : α) : GRegex α :=
  GRegex.concat (neutralWordsR phase)
    (GRegex.concat (GRegex.atom x)
      (GRegex.concat (neutralWordsR phase) (GRegex.atom y)))

@[simp]
theorem denote_pairBlockR (x y : α) :
    GRegex.denote (pairBlockR phase x y) = pairBlock phase x y := rfl

@[simp]
theorem starHeight_pairBlockR (x y : α) :
    GRegex.starHeight (pairBlockR phase x y) = 0 := by
  simp [pairBlockR, neutralWordsR, GRegex.starHeight]

/-- A fixed phase-one pair block is generalized star-free. -/
theorem isStarFree_pairBlock (x y : α) :
    IsStarFree (pairBlock phase x y) :=
  ⟨pairBlockR phase x y, denote_pairBlockR phase x y, by simp⟩

/-! ### The filtered phase-one word -/

/-- Delete all phase-zero letters. -/
def phaseOneFilter (word : Word α) : Word α :=
  word.filter fun a => phase a = 1

private theorem phase_eq_zero_or_one (a : α) :
    phase a = 0 ∨ phase a = 1 := by
  have hval : (phase a).val = 0 ∨ (phase a).val = 1 := by
    have := ZMod.val_lt (phase a)
    omega
  rcases hval with hval | hval
  · left
    apply ZMod.val_injective 2
    simpa [hval]
  · right
    apply ZMod.val_injective 2
    simpa [hval, ZMod.val_one]

private theorem filter_neutral (word : Word α)
    (hword : ∀ a ∈ word, phase a = 0) : phaseOneFilter phase word = [] := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      have ha := hword a (by simp)
      have hane : ¬ phase a = 1 := by rw [ha]; decide
      have hw : ∀ b ∈ word, phase b = 0 := by
        intro b hb
        exact hword b (by simp [hb])
      unfold phaseOneFilter
      simp only [List.filter_cons, hane]
      exact ih hw

/-- Lift the first retained letter of `phaseOneFilter phase` back to the original
word, leaving a phase-zero prefix. -/
private theorem exists_first_phaseOne (word : Word α)
    (a : α) (tail : Word α)
    (hfilter : phaseOneFilter phase word = a :: tail) :
    ∃ neutral suffix, word = neutral ++ a :: suffix ∧
      (∀ b ∈ neutral, phase b = 0) ∧ phaseOneFilter phase suffix = tail := by
  induction word with
  | nil => simp [phaseOneFilter] at hfilter
  | cons b word ih =>
      by_cases hb : phase b = 1
      · simp [phaseOneFilter, hb] at hfilter
        rcases hfilter with ⟨rfl, htail⟩
        exact ⟨[], word, by simp, by simp, htail⟩
      · have hb0 := (phase_eq_zero_or_one phase b).resolve_right hb
        have htail : phaseOneFilter phase word = a :: tail := by
          simpa [phaseOneFilter, hb] using hfilter
        obtain ⟨neutral, suffix, hsplit, hneutral, hsuffix⟩ := ih htail
        exact ⟨b :: neutral, suffix, by simp [hsplit],
          (by intro c hc; simp only [List.mem_cons] at hc
              rcases hc with rfl | hc
              · exact hb0
              · exact hneutral c hc), hsuffix⟩

/-- Pure list language `(xy)*`. -/
def XYStar (x y : α) (word : Word α) : Prop :=
  ∃ n : Nat, word = (List.replicate n [x, y]).flatten

/-- Recursive parser for `(xy)*`. -/
def XYBlocks (x y : α) : Word α → Prop
  | [] => True
  | [_] => False
  | a :: b :: rest => a = x ∧ b = y ∧ XYBlocks x y rest

private theorem xyBlocks_to_star (x y : α) :
    ∀ word, XYBlocks x y word → XYStar x y word
  | [], _ => ⟨0, rfl⟩
  | [_], h => False.elim h
  | a :: b :: rest, h => by
      rcases h with ⟨ha, hb, hrest⟩
      obtain ⟨n, hn⟩ := xyBlocks_to_star x y rest hrest
      subst a
      subst b
      exact ⟨n + 1, by rw [List.replicate_succ, List.flatten_cons, ← hn]; rfl⟩

theorem xyStar_iff_blocks (x y : α) (word : Word α) :
    XYStar x y word ↔ XYBlocks x y word := by
  constructor
  · rintro ⟨n, rfl⟩
    induction n with
    | zero => simp [XYBlocks]
    | succ n ih =>
        rw [List.replicate_succ, List.flatten_cons]
        exact ⟨rfl, rfl, ih⟩
  · exact xyBlocks_to_star x y word

/-! The candidate below describes `pairBlock phase*` without a Kleene star.
For distinct phase-one `x,y`, a nonempty accepted word:

* ends in `y`;
* has no phase-one letter other than `x` or `y`;
* does not begin, after a neutral prefix, with `y`;
* has no two consecutive `x`'s or two consecutive `y`'s after neutral gaps.

Together these conditions say that `phaseOneSubword` is a positive alternating
`xy` sequence and that no trailing neutral suffix remains.
-/

/-- Height-zero intersection of generalized expressions. -/
def interR (r s : GRegex α) : GRegex α :=
  GRegex.compl (GRegex.union (GRegex.compl r) (GRegex.compl s))

/-- Words whose final actual letter is `y`. -/
def endsWithR (y : α) : GRegex α :=
  GRegex.concat Counting.univR (GRegex.atom y)

/-- Words whose first phase-one letter is `y`. -/
noncomputable def startsWithAfterNeutralR (y : α) :
    GRegex α :=
  GRegex.concat (neutralWordsR phase)
    (GRegex.concat (GRegex.atom y) Counting.univR)

/-- Words containing two occurrences of `a` separated only by neutral
letters. -/
noncomputable def repeatedAfterNeutralR (a : α) :
    GRegex α :=
  GRegex.concat Counting.univR
    (GRegex.concat (GRegex.atom a)
      (GRegex.concat (neutralWordsR phase)
        (GRegex.concat (GRegex.atom a) Counting.univR)))

/-- Words containing a phase-one letter other than `x` and `y`. -/
noncomputable def containsOtherFlipR (x y : α) :
    GRegex α :=
  FiniteAlphabet.containsWhere fun a =>
    phase a = 1 ∧ a ≠ x ∧ a ≠ y

def EndsWith (y : α) (word : Word α) : Prop :=
  ∃ before, word = before ++ [y]

def StartsWithAfterNeutral (y : α) (word : Word α) : Prop :=
  ∃ neutral suffix, (∀ a ∈ neutral, phase a = 0) ∧
    word = neutral ++ y :: suffix

def RepeatedAfterNeutral (a : α) (word : Word α) : Prop :=
  ∃ before neutral after, (∀ b ∈ neutral, phase b = 0) ∧
    word = before ++ a :: neutral ++ a :: after

def ContainsOtherFlip (x y : α) (word : Word α) : Prop :=
  ∃ a ∈ word, phase a = 1 ∧ a ≠ x ∧ a ≠ y

@[simp] theorem mem_denote_endsWithR_iff (y : α) (word : Word α) :
    word ∈ GRegex.denote (endsWithR y) ↔ EndsWith y word := by
  simp only [endsWithR, EndsWith, GRegex.denote, Counting.denote_univR,
    Language.mem_concat_iff, Set.mem_univ, true_and]
  constructor
  · rintro ⟨before, last, hlast, hword⟩
    have : last = [y] := hlast
    subst last
    exact ⟨before, hword.symm⟩
  · rintro ⟨before, rfl⟩
    exact ⟨before, [y], rfl, rfl⟩

@[simp] theorem mem_denote_startsWithAfterNeutralR_iff
    (y : α) (word : Word α) :
    word ∈ GRegex.denote (startsWithAfterNeutralR phase y) ↔
      StartsWithAfterNeutral phase y word := by
  classical
  simp only [startsWithAfterNeutralR, neutralWordsR, GRegex.denote,
    Language.mem_concat_iff, FiniteAlphabet.mem_denote_onlyWhere_iff,
    Counting.denote_univR, Set.mem_univ]
  constructor
  · rintro ⟨neutral, hneutral, rest, ⟨letter, hletter, suffix, -, rfl⟩, rfl⟩
    have : letter = [y] := hletter
    subst letter
    exact ⟨neutral, suffix, hneutral, by simp⟩
  · rintro ⟨neutral, suffix, hneutral, rfl⟩
    exact ⟨neutral, hneutral, y :: suffix,
      ⟨[y], rfl, suffix, by simp, rfl⟩, rfl⟩

@[simp] theorem mem_denote_repeatedAfterNeutralR_iff
    (a : α) (word : Word α) :
    word ∈ GRegex.denote (repeatedAfterNeutralR phase a) ↔
      RepeatedAfterNeutral phase a word := by
  classical
  simp only [repeatedAfterNeutralR, neutralWordsR, GRegex.denote,
    Language.mem_concat_iff, FiniteAlphabet.mem_denote_onlyWhere_iff,
    Counting.denote_univR, Set.mem_univ]
  constructor
  · rintro ⟨before, -, rest₁,
      ⟨letter₁, hletter₁, rest₂,
        ⟨neutral, hneutral, rest₃,
          ⟨letter₂, hletter₂, after, -, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    have h₁ : letter₁ = [a] := hletter₁
    have h₂ : letter₂ = [a] := hletter₂
    subst letter₁
    subst letter₂
    exact ⟨before, neutral, after, hneutral, by simp⟩
  · rintro ⟨before, neutral, after, hneutral, rfl⟩
    exact ⟨before, by simp, a :: neutral ++ a :: after,
      ⟨[a], rfl, neutral ++ a :: after,
        ⟨neutral, hneutral, a :: after,
          ⟨[a], rfl, after, by simp, rfl⟩, rfl⟩, rfl⟩,
      by simp [List.append_assoc]⟩

@[simp] theorem mem_denote_containsOtherFlipR_iff
    (x y : α) (word : Word α) :
    word ∈ GRegex.denote (containsOtherFlipR phase x y) ↔
      ContainsOtherFlip phase x y word := by
  classical
  simp [containsOtherFlipR, ContainsOtherFlip]

@[simp] theorem phaseOneFilter_append (left right : Word α) :
    phaseOneFilter phase (left ++ right) = phaseOneFilter phase left ++ phaseOneFilter phase right := by
  simp [phaseOneFilter, List.filter_append]

private theorem starts_iff_filter_cons (a : α) (ha : phase a = 1)
    (word : Word α) :
    StartsWithAfterNeutral phase a word ↔ ∃ tail, phaseOneFilter phase word = a :: tail := by
  constructor
  · rintro ⟨neutral, suffix, hneutral, rfl⟩
    refine ⟨phaseOneFilter phase suffix, ?_⟩
    rw [phaseOneFilter_append phase, filter_neutral phase neutral hneutral]
    simp [phaseOneFilter, ha]
  · rintro ⟨tail, hfilter⟩
    obtain ⟨neutral, suffix, rfl, hneutral, hsuffix⟩ :=
      exists_first_phaseOne phase word a tail hfilter
    exact ⟨neutral, suffix, hneutral, rfl⟩

private theorem repeated_of_filter_pattern (a : α) (ha : phase a = 1) :
    ∀ before word after,
      phaseOneFilter phase word = before ++ a :: a :: after →
        RepeatedAfterNeutral phase a word
  | [], word, after, hfilter => by
      obtain ⟨neutral₁, suffix₁, hsplit₁, hneutral₁, hsuffix₁⟩ :=
        exists_first_phaseOne phase word a (a :: after) (by simpa using hfilter)
      obtain ⟨neutral₂, suffix₂, hsplit₂, hneutral₂, -⟩ :=
        exists_first_phaseOne phase suffix₁ a after hsuffix₁
      exact ⟨neutral₁, neutral₂, suffix₂, hneutral₂, by
        rw [hsplit₁, hsplit₂]
        simp [List.append_assoc]⟩
  | b :: before, word, after, hfilter => by
      obtain ⟨neutral, suffix, hsplit, -, hsuffix⟩ :=
        exists_first_phaseOne phase word b (before ++ a :: a :: after) (by
          simpa [List.append_assoc] using hfilter)
      obtain ⟨pre, middle, post, hmiddle, hrepeat⟩ :=
        repeated_of_filter_pattern a ha before suffix after hsuffix
      exact ⟨neutral ++ b :: pre, middle, post, hmiddle, by
        rw [hsplit, hrepeat]
        simp [List.append_assoc]⟩

private theorem repeated_iff_filter_pattern (a : α) (ha : phase a = 1)
    (word : Word α) :
    RepeatedAfterNeutral phase a word ↔
      ∃ before after, phaseOneFilter phase word = before ++ a :: a :: after := by
  constructor
  · rintro ⟨before, neutral, after, hneutral, rfl⟩
    refine ⟨phaseOneFilter phase before, phaseOneFilter phase after, ?_⟩
    simp only [phaseOneFilter_append phase]
    have hfirst : phaseOneFilter phase (a :: neutral) = [a] := by
      have hcons : phaseOneFilter phase (a :: neutral) = a :: phaseOneFilter phase neutral := by
        simp [phaseOneFilter, ha]
      rw [hcons, filter_neutral phase neutral hneutral]
    have hsecond : phaseOneFilter phase (a :: after) = a :: phaseOneFilter phase after := by
      simp [phaseOneFilter, ha]
    rw [hfirst, hsecond]
    simp [List.append_assoc]
  · rintro ⟨before, after, hfilter⟩
    exact repeated_of_filter_pattern phase a ha before word after hfilter

private theorem containsOther_iff_filter (x y : α) (word : Word α) :
    ContainsOtherFlip phase x y word ↔
      ∃ a ∈ phaseOneFilter phase word, a ≠ x ∧ a ≠ y := by
  simp only [ContainsOtherFlip, phaseOneFilter, List.mem_filter]
  aesop

private theorem ends_filter_last (y : α) (hy : phase y = 1)
    (word : Word α) (hends : EndsWith y word) :
    (phaseOneFilter phase word).getLast? = some y := by
  rcases hends with ⟨before, rfl⟩
  simp [phaseOneFilter, hy]

private theorem xyBlocks_of_local (x y : α) (hne : x ≠ y) :
    ∀ word : Word α,
      (∀ a ∈ word, a = x ∨ a = y) →
      (word = [] ∨ word.head? = some x) →
      (word = [] ∨ word.getLast? = some y) →
      List.IsChain (· ≠ ·) word → XYBlocks x y word
  | [], _, _, _, _ => trivial
  | [a], hmem, hhead, hlast, _ => by
      have haX : a = x := by rcases hhead with h | h <;> simp_all
      have haY : a = y := by rcases hlast with h | h <;> simp_all
      exact False.elim (hne (haX.symm.trans haY))
  | a :: b :: rest, hmem, hhead, hlast, hchain => by
      have haX : a = x := by rcases hhead with h | h <;> simp_all
      have hbMem := hmem b (by simp)
      have hab : a ≠ b := (List.isChain_cons_cons.mp hchain).1
      have hbY : b = y := by
        rcases hbMem with hbX | hbY
        · exact False.elim (hab (haX.trans hbX.symm))
        · exact hbY
      have hchainTail : List.IsChain (· ≠ ·) rest := hchain.drop 2
      have hheadTail : rest = [] ∨ rest.head? = some x := by
        cases rest with
        | nil => exact Or.inl rfl
        | cons c rest =>
            right
            have hbc : b ≠ c := (List.isChain_cons_cons.mp
              (List.isChain_cons_cons.mp hchain).2).1
            rcases hmem c (by simp) with hcX | hcY
            · simp [hcX]
            · exact False.elim (hbc (hbY.trans hcY.symm))
      have hlastTail : rest = [] ∨ rest.getLast? = some y := by
        cases rest with
        | nil => exact Or.inl rfl
        | cons c rest =>
            right
            rcases hlast with h | h
            · simp at h
            · simpa using h
      exact ⟨haX, hbY, xyBlocks_of_local x y hne rest
        (by intro c hc; exact hmem c (by simp [hc]))
        hheadTail hlastTail hchainTail⟩

private theorem chain_of_allowed_no_patterns (x y : α) :
    ∀ word : Word α,
      (∀ a ∈ word, a = x ∨ a = y) →
      (¬ ∃ before after, word = before ++ x :: x :: after) →
      (¬ ∃ before after, word = before ++ y :: y :: after) →
      List.IsChain (· ≠ ·) word
  | [], _, _, _ => by simp
  | [_], _, _, _ => by simp
  | a :: b :: rest, hmem, hnoX, hnoY => by
      have hab : a ≠ b := by
        intro heq
        subst b
        rcases hmem a (by simp) with ha | ha
        · apply hnoX
          exact ⟨[], rest, by simp [ha]⟩
        · apply hnoY
          exact ⟨[], rest, by simp [ha]⟩
      apply List.isChain_cons_cons.2
      refine ⟨hab, chain_of_allowed_no_patterns x y (b :: rest)
        (by intro c hc; exact hmem c (by simp [hc])) ?_ ?_⟩
      · rintro ⟨before, after, hbad⟩
        apply hnoX
        exact ⟨a :: before, after, by simp [hbad]⟩
      · rintro ⟨before, after, hbad⟩
        apply hnoY
        exact ⟨a :: before, after, by simp [hbad]⟩

private theorem local_of_xyBlocks (x y : α) (hne : x ≠ y) :
    ∀ word : Word α, XYBlocks x y word →
      (∀ a ∈ word, a = x ∨ a = y) ∧
      (word = [] ∨ word.head? = some x) ∧
      (word = [] ∨ word.getLast? = some y) ∧
      List.IsChain (· ≠ ·) word
  | [], _ => by simp
  | [_], h => False.elim h
  | a :: b :: rest, h => by
      rcases h with ⟨ha, hb, hrest⟩
      have hlocal := local_of_xyBlocks x y hne rest hrest
      rcases hlocal with ⟨hmem, hhead, hlast, hchain⟩
      subst a
      subst b
      refine ⟨?_, by simp, ?_, ?_⟩
      · intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | rfl | hc
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact hmem c hc
      · cases rest with
        | nil => simp
        | cons c rest =>
            right
            rcases hlast with h | h
            · simp at h
            · simpa using h
      · apply List.isChain_cons_cons.2
        refine ⟨hne, ?_⟩
        cases rest with
        | nil => simp
        | cons c rest =>
            have hcX : c = x := by
              rcases hhead with h | h
              · simp at h
              · simpa using h
            apply List.isChain_cons_cons.2
            exact ⟨by simpa [hcX] using hne.symm, hchain⟩

/-- Star-free candidate for `(Z* x Z* y)*`. -/
noncomputable def pairBlockStarR (x y : α) : GRegex α :=
  GRegex.union GRegex.epsilon
    (interR (endsWithR y)
      (interR (GRegex.compl (startsWithAfterNeutralR phase y))
        (interR (GRegex.compl (repeatedAfterNeutralR phase x))
          (interR (GRegex.compl (repeatedAfterNeutralR phase y))
            (GRegex.compl (containsOtherFlipR phase x y))))))

def PairLocal (x y : α) (word : Word α) : Prop :=
  word = [] ∨ (EndsWith y word ∧ XYBlocks x y (phaseOneFilter phase word))

private theorem mem_pairBlock_iff (x y : α) (word : Word α) :
    word ∈ pairBlock phase x y ↔
      ∃ neutral₁ neutral₂,
        (∀ a ∈ neutral₁, phase a = 0) ∧
        (∀ a ∈ neutral₂, phase a = 0) ∧
        word = neutral₁ ++ x :: neutral₂ ++ [y] := by
  classical
  simp only [pairBlock, neutralWordsR,
    Language.mem_concat_iff, FiniteAlphabet.mem_denote_onlyWhere_iff]
  constructor
  · rintro ⟨neutral₁, hneutral₁, rest₁,
      ⟨letter₁, hletter₁, rest₂,
        ⟨neutral₂, hneutral₂, letter₂, hletter₂, rfl⟩, rfl⟩, rfl⟩
    have hx : letter₁ = [x] := hletter₁
    have hy : letter₂ = [y] := hletter₂
    subst letter₁
    subst letter₂
    exact ⟨neutral₁, neutral₂, hneutral₁, hneutral₂, by simp⟩
  · rintro ⟨neutral₁, neutral₂, hneutral₁, hneutral₂, rfl⟩
    exact ⟨neutral₁, hneutral₁, x :: neutral₂ ++ [y],
      ⟨[x], rfl, neutral₂ ++ [y],
        ⟨neutral₂, hneutral₂, [y], rfl, rfl⟩, rfl⟩, by simp⟩

private theorem filter_pairBlock (x y : α)
    (hx : phase x = 1) (hy : phase y = 1)
    (word : Word α) (hword : word ∈ pairBlock phase x y) :
    phaseOneFilter phase word = [x, y] := by
  obtain ⟨neutral₁, neutral₂, hneutral₁, hneutral₂, rfl⟩ :=
    (mem_pairBlock_iff phase x y word).1 hword
  rw [phaseOneFilter_append phase, phaseOneFilter_append phase,
    filter_neutral phase neutral₁ hneutral₁]
  have hneutral₂' := filter_neutral phase neutral₂ hneutral₂
  unfold phaseOneFilter at hneutral₂' ⊢
  simp [hx, hy, hneutral₂']

private theorem ends_pairBlock (x y : α) (word : Word α)
    (hword : word ∈ pairBlock phase x y) : EndsWith y word := by
  obtain ⟨neutral₁, neutral₂, -, -, rfl⟩ :=
    (mem_pairBlock_iff phase x y word).1 hword
  exact ⟨neutral₁ ++ x :: neutral₂, by simp [List.append_assoc]⟩

private theorem ends_append_right (y : α)
    (pre suffix : Word α) (hsuffix : suffix ≠ [])
    (hends : EndsWith y (pre ++ suffix)) : EndsWith y suffix := by
  have hlast : (pre ++ suffix).getLast? = some y :=
    List.getLast?_eq_some_iff.2 hends
  rw [List.getLast?_append_of_ne_nil pre hsuffix] at hlast
  exact List.getLast?_eq_some_iff.1 hlast

private theorem mem_power_pairBlock_of_filter (x y : α)
    (_hx : phase x = 1) (hy : phase y = 1) :
    ∀ n word,
      phaseOneFilter phase word = (List.replicate (n + 1) [x, y]).flatten →
      EndsWith y word →
      word ∈ Language.power (pairBlock phase x y) (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro word hfilter hends
      have hfilter' : phaseOneFilter phase word = x :: y :: [] := by
        simpa using hfilter
      obtain ⟨neutral₁, suffix₁, hsplit₁, hneutral₁, hsuffix₁⟩ :=
        exists_first_phaseOne phase word x (y :: []) hfilter'
      obtain ⟨neutral₂, suffix₂, hsplit₂, hneutral₂, hsuffix₂⟩ :=
        exists_first_phaseOne phase suffix₁ y [] hsuffix₁
      have hsuffix₂_nil : suffix₂ = [] := by
        by_contra hsuffix₂_ne
        have hends₂ : EndsWith y suffix₂ := by
          apply ends_append_right y (neutral₁ ++ x :: neutral₂ ++ [y]) suffix₂
            hsuffix₂_ne
          simpa [hsplit₁, hsplit₂, List.append_assoc] using hends
        have hlast := ends_filter_last phase y hy suffix₂ hends₂
        rw [hsuffix₂] at hlast
        simp at hlast
      subst suffix₂
      rw [Language.power_succ_left]
      refine ⟨word, ?_, [], ?_, by simp⟩
      · apply (mem_pairBlock_iff phase x y word).2
        exact ⟨neutral₁, neutral₂, hneutral₁, hneutral₂, by
          rw [hsplit₁, hsplit₂]
          simp [List.append_assoc]⟩
      · simp [Language.power, Language.epsilon]
  | succ n ih =>
      intro word hfilter hends
      have hfilter' : phaseOneFilter phase word =
          x :: y :: (List.replicate (n + 1) [x, y]).flatten := by
        simpa [List.replicate_succ, List.flatten_cons] using hfilter
      obtain ⟨neutral₁, suffix₁, hsplit₁, hneutral₁, hsuffix₁⟩ :=
        exists_first_phaseOne phase word x
          (y :: (List.replicate (n + 1) [x, y]).flatten) hfilter'
      obtain ⟨neutral₂, suffix₂, hsplit₂, hneutral₂, hsuffix₂⟩ :=
        exists_first_phaseOne phase suffix₁ y
          ((List.replicate (n + 1) [x, y]).flatten) hsuffix₁
      have hsuffix₂_ne : suffix₂ ≠ [] := by
        intro hsuffix₂_nil
        subst suffix₂
        simp [phaseOneFilter, List.replicate_succ] at hsuffix₂
      have hends₂ : EndsWith y suffix₂ := by
        apply ends_append_right y (neutral₁ ++ x :: neutral₂ ++ [y]) suffix₂
          hsuffix₂_ne
        simpa [hsplit₁, hsplit₂, List.append_assoc] using hends
      have hrest : suffix₂ ∈ Language.power (pairBlock phase x y) (n + 1) :=
        ih suffix₂ hsuffix₂ hends₂
      rw [Language.power_succ_left]
      refine ⟨neutral₁ ++ x :: neutral₂ ++ [y], ?_, suffix₂, hrest, ?_⟩
      · apply (mem_pairBlock_iff phase x y _).2
        exact ⟨neutral₁, neutral₂, hneutral₁, hneutral₂, rfl⟩
      · rw [hsplit₁, hsplit₂]
        simp [List.append_assoc]

private theorem mem_star_pairBlock_iff_local (x y : α)
    (hx : phase x = 1) (hy : phase y = 1)
    (word : Word α) :
    word ∈ Language.star (pairBlock phase x y) ↔ PairLocal phase x y word := by
  constructor
  · rintro ⟨n, hn⟩
    induction n generalizing word with
    | zero =>
        left
        simpa [Language.power, Language.epsilon] using hn
    | succ n ih =>
        rw [Language.power_succ_left] at hn
        obtain ⟨piece, hpiece, rest, hrest, hword⟩ := hn
        have hlocalRest := ih rest hrest
        have hfilterPiece := filter_pairBlock phase x y hx hy piece hpiece
        have hendsPiece := ends_pairBlock phase x y piece hpiece
        subst word
        right
        rcases hlocalRest with rfl | ⟨hendsRest, hblocksRest⟩
        · simpa [phaseOneFilter_append phase, hfilterPiece, XYBlocks] using
            And.intro hendsPiece (show XYBlocks x y [x, y] from ⟨rfl, rfl, trivial⟩)
        · refine ⟨?_, ?_⟩
          · rcases hendsRest with ⟨before, rfl⟩
            exact ⟨piece ++ before, by simp [List.append_assoc]⟩
          · rw [phaseOneFilter_append phase, hfilterPiece]
            exact ⟨rfl, rfl, hblocksRest⟩
  · rintro (rfl | ⟨hends, hblocks⟩)
    · exact ⟨0, by simp [Language.power, Language.epsilon]⟩
    · obtain ⟨n, hfilter⟩ := xyBlocks_to_star x y (phaseOneFilter phase word) hblocks
      cases n with
      | zero =>
          have hlast := ends_filter_last phase y hy word hends
          rw [hfilter] at hlast
          simp at hlast
      | succ n =>
          exact ⟨n + 1, mem_power_pairBlock_of_filter phase x y hx hy n word
            (by simpa using hfilter) hends⟩

theorem mem_pairBlockStarR_iff_local (x y : α)
    (hx : phase x = 1) (hy : phase y = 1) (hne : x ≠ y)
    (word : Word α) :
    word ∈ GRegex.denote (pairBlockStarR phase x y) ↔ PairLocal phase x y word := by
  classical
  rw [pairBlockStarR]
  simp only [GRegex.denote, Set.mem_union, Language.mem_epsilon_iff,
    interR, Language.mem_compl_iff,
    mem_denote_endsWithR_iff, mem_denote_startsWithAfterNeutralR_iff phase,
    mem_denote_repeatedAfterNeutralR_iff phase, mem_denote_containsOtherFlipR_iff phase,
    not_or, not_not]
  constructor
  · rintro (rfl | ⟨hends, hnoStart, hnoRepeatX, hnoRepeatY, hnoOther⟩)
    · exact Or.inl rfl
    · apply Or.inr
      refine ⟨hends, ?_⟩
      apply xyBlocks_of_local x y hne (phaseOneFilter phase word)
      · intro a ha
        by_contra hallowed
        push Not at hallowed
        exact hnoOther ((containsOther_iff_filter phase x y word).2
          ⟨a, ha, hallowed.1, hallowed.2⟩)
      · cases hfilter : phaseOneFilter phase word with
        | nil => exact Or.inl rfl
        | cons a rest =>
            right
            have haAllowed : a = x ∨ a = y := by
              have haMem : a ∈ phaseOneFilter phase word := by rw [hfilter]; simp
              by_contra hallowed
              push Not at hallowed
              exact hnoOther ((containsOther_iff_filter phase x y word).2
                ⟨a, haMem, hallowed.1, hallowed.2⟩)
            rcases haAllowed with haX | haY
            · simp [haX]
            · exact False.elim (hnoStart ((starts_iff_filter_cons phase y hy word).2
                ⟨rest, by simpa [haY] using hfilter⟩))
      · right
        exact ends_filter_last phase y hy word hends
      · apply chain_of_allowed_no_patterns x y (phaseOneFilter phase word)
        · intro a ha
          by_contra hallowed
          push Not at hallowed
          exact hnoOther ((containsOther_iff_filter phase x y word).2
            ⟨a, ha, hallowed.1, hallowed.2⟩)
        · intro hbad
          exact hnoRepeatX ((repeated_iff_filter_pattern phase x hx word).2 hbad)
        · intro hbad
          exact hnoRepeatY ((repeated_iff_filter_pattern phase y hy word).2 hbad)
  · rintro (rfl | ⟨hends, hblocks⟩)
    · exact Or.inl rfl
    · apply Or.inr
      have hlocal := local_of_xyBlocks x y hne (phaseOneFilter phase word) hblocks
      rcases hlocal with ⟨hallowed, hhead, -, hchain⟩
      refine ⟨hends, ?_, ?_, ?_, ?_⟩
      · intro hstart
        obtain ⟨tail, hfilter⟩ := (starts_iff_filter_cons phase y hy word).1 hstart
        rcases hhead with hnil | hhead
        · rw [hfilter] at hnil; simp at hnil
        · rw [hfilter] at hhead
          simp at hhead
          exact hne hhead.symm
      · intro hrepeat
        obtain ⟨before, after, hfilter⟩ :=
          (repeated_iff_filter_pattern phase x hx word).1 hrepeat
        have := hchain.drop before.length
        rw [hfilter] at this
        simp at this
      · intro hrepeat
        obtain ⟨before, after, hfilter⟩ :=
          (repeated_iff_filter_pattern phase y hy word).1 hrepeat
        have := hchain.drop before.length
        rw [hfilter] at this
        simp at this
      · intro hother
        obtain ⟨a, ha, hax, hay⟩ := (containsOther_iff_filter phase x y word).1 hother
        rcases hallowed a ha with rfl | rfl
        · exact hax rfl
        · exact hay rfl

@[simp]
theorem starHeight_pairBlockStarR (x y : α) :
    GRegex.starHeight (pairBlockStarR phase x y) = 0 := by
  simp [pairBlockStarR, interR, endsWithR, startsWithAfterNeutralR,
    repeatedAfterNeutralR, containsOtherFlipR, neutralWordsR,
    Counting.univR, GRegex.starHeight]

/-- The height-zero local-pattern expression denotes exactly the star of a
fixed distinct phase-one pair block. -/
theorem denote_pairBlockStarR (x y : α)
    (hx : phase x = 1) (hy : phase y = 1) (hne : x ≠ y) :
    GRegex.denote (pairBlockStarR phase x y) = Language.star (pairBlock phase x y) := by
  ext word
  exact (mem_pairBlockStarR_iff_local phase x y hx hy hne word).trans
    (mem_star_pairBlock_iff_local phase x y hx hy word).symm

/-- The star of a fixed distinct phase-one pair block is generalized
star-free. -/
theorem isStarFree_pairBlockStar (x y : α)
    (hx : phase x = 1) (hy : phase y = 1) (hne : x ≠ y) :
    IsStarFree (Language.star (pairBlock phase x y)) :=
  ⟨pairBlockStarR phase x y, denote_pairBlockStarR phase x y hx hy hne, by simp⟩

/-- Once the local-pattern characterization is proved semantically, the
desired star-freeness conclusion follows without any further height work. -/
theorem isStarFree_pairBlockStar_of_denote (x y : α)
    (hdenote : GRegex.denote (pairBlockStarR phase x y) =
      Language.star (pairBlock phase x y)) :
    IsStarFree (Language.star (pairBlock phase x y)) :=
  ⟨pairBlockStarR phase x y, hdenote, by simp⟩

end C2PairHeight

end GSH
