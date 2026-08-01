import GSH.Height.S3ArrowArithmetic
import GSH.Height.S3SelfLoopHeight

/-!
# Star-free fixed flip-pair blocks for the `S₃` route

For phase-one letters `x` and `y`, a fixed pair block has the form
`Z* · x · Z* · y`, where `Z*` consists of phase-zero words.  The
block itself is star-free.  A height-zero local-pattern expression is proved
to denote the star of the block when `x` and `y` are distinct phase-one
letters.
-/

set_option autoImplicit false

namespace GSH

namespace S3FlipPairHeight

open S3SelfLoopHeight

/-- Semantic fixed pair block `Z* · x · Z* · y`. -/
def pairBlock (x y : S3Alphabet) : Language S3Alphabet :=
  Language.concat
    (GRegex.denote neutralWordsR)
    (Language.concat (Language.letter x)
      (Language.concat (GRegex.denote neutralWordsR) (Language.letter y)))

/-- Height-zero expression for one fixed pair block. -/
noncomputable def pairBlockR (x y : S3Alphabet) : GRegex S3Alphabet :=
  GRegex.concat neutralWordsR
    (GRegex.concat (GRegex.atom x)
      (GRegex.concat neutralWordsR (GRegex.atom y)))

@[simp]
theorem denote_pairBlockR (x y : S3Alphabet) :
    GRegex.denote (pairBlockR x y) = pairBlock x y := rfl

@[simp]
theorem starHeight_pairBlockR (x y : S3Alphabet) :
    GRegex.starHeight (pairBlockR x y) = 0 := by
  simp [pairBlockR, neutralWordsR, GRegex.starHeight]

/-- A fixed phase-one pair block is generalized star-free. -/
theorem isStarFree_pairBlock (x y : S3Alphabet) :
    IsStarFree (pairBlock x y) :=
  ⟨pairBlockR x y, denote_pairBlockR x y, by simp⟩

/-! ### The filtered phase-one word -/

/-- Delete all phase-zero letters. -/
def phaseOneFilter (word : Word S3Alphabet) : Word S3Alphabet :=
  word.filter fun a => s3Phase a = 1

private theorem phase_eq_zero_or_one (a : S3Alphabet) :
    s3Phase a = 0 ∨ s3Phase a = 1 := by
  revert a
  decide

private theorem filter_neutral (word : Word S3Alphabet)
    (hword : ∀ a ∈ word, s3Phase a = 0) : phaseOneFilter word = [] := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      have ha := hword a (by simp)
      have hane : ¬ s3Phase a = 1 := by rw [ha]; decide
      have hw : ∀ b ∈ word, s3Phase b = 0 := by
        intro b hb
        exact hword b (by simp [hb])
      unfold phaseOneFilter
      simp only [List.filter_cons, hane]
      exact ih hw

/-- Lift the first retained letter of `phaseOneFilter` back to the original
word, leaving a phase-zero prefix. -/
private theorem exists_first_phaseOne (word : Word S3Alphabet)
    (a : S3Alphabet) (tail : Word S3Alphabet)
    (hfilter : phaseOneFilter word = a :: tail) :
    ∃ neutral suffix, word = neutral ++ a :: suffix ∧
      (∀ b ∈ neutral, s3Phase b = 0) ∧ phaseOneFilter suffix = tail := by
  induction word with
  | nil => simp [phaseOneFilter] at hfilter
  | cons b word ih =>
      by_cases hb : s3Phase b = 1
      · simp [phaseOneFilter, hb] at hfilter
        rcases hfilter with ⟨rfl, htail⟩
        exact ⟨[], word, by simp, by simp, htail⟩
      · have hb0 := (phase_eq_zero_or_one b).resolve_right hb
        have htail : phaseOneFilter word = a :: tail := by
          simpa [phaseOneFilter, hb] using hfilter
        obtain ⟨neutral, suffix, hsplit, hneutral, hsuffix⟩ := ih htail
        exact ⟨b :: neutral, suffix, by simp [hsplit],
          (by intro c hc; simp only [List.mem_cons] at hc
              rcases hc with rfl | hc
              · exact hb0
              · exact hneutral c hc), hsuffix⟩

/-- Pure list language `(xy)*`. -/
def XYStar (x y : S3Alphabet) (word : Word S3Alphabet) : Prop :=
  ∃ n : Nat, word = (List.replicate n [x, y]).flatten

/-- Recursive parser for `(xy)*`. -/
def XYBlocks (x y : S3Alphabet) : Word S3Alphabet → Prop
  | [] => True
  | [_] => False
  | a :: b :: rest => a = x ∧ b = y ∧ XYBlocks x y rest

private theorem xyBlocks_to_star (x y : S3Alphabet) :
    ∀ word, XYBlocks x y word → XYStar x y word
  | [], _ => ⟨0, rfl⟩
  | [_], h => False.elim h
  | a :: b :: rest, h => by
      rcases h with ⟨ha, hb, hrest⟩
      obtain ⟨n, hn⟩ := xyBlocks_to_star x y rest hrest
      subst a
      subst b
      exact ⟨n + 1, by rw [List.replicate_succ, List.flatten_cons, ← hn]; rfl⟩

theorem xyStar_iff_blocks (x y : S3Alphabet) (word : Word S3Alphabet) :
    XYStar x y word ↔ XYBlocks x y word := by
  constructor
  · rintro ⟨n, rfl⟩
    induction n with
    | zero => simp [XYBlocks]
    | succ n ih =>
        rw [List.replicate_succ, List.flatten_cons]
        exact ⟨rfl, rfl, ih⟩
  · exact xyBlocks_to_star x y word

/-! The candidate below describes `pairBlock*` without a Kleene star.
For distinct phase-one `x,y`, a nonempty accepted word:

* ends in `y`;
* has no phase-one letter other than `x` or `y`;
* does not begin, after a neutral prefix, with `y`;
* has no two consecutive `x`'s or two consecutive `y`'s after neutral gaps.

Together these conditions say that `phaseOneSubword` is a positive alternating
`xy` sequence and that no trailing neutral suffix remains.
-/

/-- Height-zero intersection of generalized expressions. -/
def interR (r s : GRegex S3Alphabet) : GRegex S3Alphabet :=
  GRegex.compl (GRegex.union (GRegex.compl r) (GRegex.compl s))

/-- Words whose final actual letter is `y`. -/
def endsWithR (y : S3Alphabet) : GRegex S3Alphabet :=
  GRegex.concat Counting.univR (GRegex.atom y)

/-- Words whose first phase-one letter is `y`. -/
noncomputable def startsWithAfterNeutralR (y : S3Alphabet) :
    GRegex S3Alphabet :=
  GRegex.concat neutralWordsR
    (GRegex.concat (GRegex.atom y) Counting.univR)

/-- Words containing two occurrences of `a` separated only by neutral
letters. -/
noncomputable def repeatedAfterNeutralR (a : S3Alphabet) :
    GRegex S3Alphabet :=
  GRegex.concat Counting.univR
    (GRegex.concat (GRegex.atom a)
      (GRegex.concat neutralWordsR
        (GRegex.concat (GRegex.atom a) Counting.univR)))

/-- Words containing a phase-one letter other than `x` and `y`. -/
noncomputable def containsOtherFlipR (x y : S3Alphabet) :
    GRegex S3Alphabet :=
  FiniteAlphabet.containsWhere fun a =>
    s3Phase a = 1 ∧ a ≠ x ∧ a ≠ y

def EndsWith (y : S3Alphabet) (word : Word S3Alphabet) : Prop :=
  ∃ before, word = before ++ [y]

def StartsWithAfterNeutral (y : S3Alphabet) (word : Word S3Alphabet) : Prop :=
  ∃ neutral suffix, (∀ a ∈ neutral, s3Phase a = 0) ∧
    word = neutral ++ y :: suffix

def RepeatedAfterNeutral (a : S3Alphabet) (word : Word S3Alphabet) : Prop :=
  ∃ before neutral after, (∀ b ∈ neutral, s3Phase b = 0) ∧
    word = before ++ a :: neutral ++ a :: after

def ContainsOtherFlip (x y : S3Alphabet) (word : Word S3Alphabet) : Prop :=
  ∃ a ∈ word, s3Phase a = 1 ∧ a ≠ x ∧ a ≠ y

@[simp] theorem mem_denote_endsWithR_iff (y : S3Alphabet) (word : Word S3Alphabet) :
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
    (y : S3Alphabet) (word : Word S3Alphabet) :
    word ∈ GRegex.denote (startsWithAfterNeutralR y) ↔
      StartsWithAfterNeutral y word := by
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
    (a : S3Alphabet) (word : Word S3Alphabet) :
    word ∈ GRegex.denote (repeatedAfterNeutralR a) ↔
      RepeatedAfterNeutral a word := by
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
    (x y : S3Alphabet) (word : Word S3Alphabet) :
    word ∈ GRegex.denote (containsOtherFlipR x y) ↔
      ContainsOtherFlip x y word := by
  classical
  simp [containsOtherFlipR, ContainsOtherFlip]

@[simp] theorem phaseOneFilter_append (left right : Word S3Alphabet) :
    phaseOneFilter (left ++ right) = phaseOneFilter left ++ phaseOneFilter right := by
  simp [phaseOneFilter, List.filter_append]

private theorem starts_iff_filter_cons (a : S3Alphabet) (ha : s3Phase a = 1)
    (word : Word S3Alphabet) :
    StartsWithAfterNeutral a word ↔ ∃ tail, phaseOneFilter word = a :: tail := by
  constructor
  · rintro ⟨neutral, suffix, hneutral, rfl⟩
    refine ⟨phaseOneFilter suffix, ?_⟩
    rw [phaseOneFilter_append, filter_neutral neutral hneutral]
    simp [phaseOneFilter, ha]
  · rintro ⟨tail, hfilter⟩
    obtain ⟨neutral, suffix, rfl, hneutral, hsuffix⟩ :=
      exists_first_phaseOne word a tail hfilter
    exact ⟨neutral, suffix, hneutral, rfl⟩

private theorem repeated_of_filter_pattern (a : S3Alphabet) (ha : s3Phase a = 1) :
    ∀ before word after,
      phaseOneFilter word = before ++ a :: a :: after →
        RepeatedAfterNeutral a word
  | [], word, after, hfilter => by
      obtain ⟨neutral₁, suffix₁, hsplit₁, hneutral₁, hsuffix₁⟩ :=
        exists_first_phaseOne word a (a :: after) (by simpa using hfilter)
      obtain ⟨neutral₂, suffix₂, hsplit₂, hneutral₂, -⟩ :=
        exists_first_phaseOne suffix₁ a after hsuffix₁
      exact ⟨neutral₁, neutral₂, suffix₂, hneutral₂, by
        rw [hsplit₁, hsplit₂]
        simp [List.append_assoc]⟩
  | b :: before, word, after, hfilter => by
      obtain ⟨neutral, suffix, hsplit, -, hsuffix⟩ :=
        exists_first_phaseOne word b (before ++ a :: a :: after) (by
          simpa [List.append_assoc] using hfilter)
      obtain ⟨pre, middle, post, hmiddle, hrepeat⟩ :=
        repeated_of_filter_pattern a ha before suffix after hsuffix
      exact ⟨neutral ++ b :: pre, middle, post, hmiddle, by
        rw [hsplit, hrepeat]
        simp [List.append_assoc]⟩

private theorem repeated_iff_filter_pattern (a : S3Alphabet) (ha : s3Phase a = 1)
    (word : Word S3Alphabet) :
    RepeatedAfterNeutral a word ↔
      ∃ before after, phaseOneFilter word = before ++ a :: a :: after := by
  constructor
  · rintro ⟨before, neutral, after, hneutral, rfl⟩
    refine ⟨phaseOneFilter before, phaseOneFilter after, ?_⟩
    simp only [phaseOneFilter_append]
    have hfirst : phaseOneFilter (a :: neutral) = [a] := by
      have hcons : phaseOneFilter (a :: neutral) = a :: phaseOneFilter neutral := by
        simp [phaseOneFilter, ha]
      rw [hcons, filter_neutral neutral hneutral]
    have hsecond : phaseOneFilter (a :: after) = a :: phaseOneFilter after := by
      simp [phaseOneFilter, ha]
    rw [hfirst, hsecond]
    simp [List.append_assoc]
  · rintro ⟨before, after, hfilter⟩
    exact repeated_of_filter_pattern a ha before word after hfilter

private theorem containsOther_iff_filter (x y : S3Alphabet) (word : Word S3Alphabet) :
    ContainsOtherFlip x y word ↔
      ∃ a ∈ phaseOneFilter word, a ≠ x ∧ a ≠ y := by
  simp only [ContainsOtherFlip, phaseOneFilter, List.mem_filter]
  aesop

private theorem ends_filter_last (y : S3Alphabet) (hy : s3Phase y = 1)
    (word : Word S3Alphabet) (hends : EndsWith y word) :
    (phaseOneFilter word).getLast? = some y := by
  rcases hends with ⟨before, rfl⟩
  simp [phaseOneFilter, hy]

private theorem xyBlocks_of_local (x y : S3Alphabet) (hne : x ≠ y) :
    ∀ word : Word S3Alphabet,
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

private theorem chain_of_allowed_no_patterns (x y : S3Alphabet) :
    ∀ word : Word S3Alphabet,
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

private theorem local_of_xyBlocks (x y : S3Alphabet) (hne : x ≠ y) :
    ∀ word : Word S3Alphabet, XYBlocks x y word →
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
noncomputable def pairBlockStarR (x y : S3Alphabet) : GRegex S3Alphabet :=
  GRegex.union GRegex.epsilon
    (interR (endsWithR y)
      (interR (GRegex.compl (startsWithAfterNeutralR y))
        (interR (GRegex.compl (repeatedAfterNeutralR x))
          (interR (GRegex.compl (repeatedAfterNeutralR y))
            (GRegex.compl (containsOtherFlipR x y))))))

def PairLocal (x y : S3Alphabet) (word : Word S3Alphabet) : Prop :=
  word = [] ∨ (EndsWith y word ∧ XYBlocks x y (phaseOneFilter word))

private theorem mem_pairBlock_iff (x y : S3Alphabet) (word : Word S3Alphabet) :
    word ∈ pairBlock x y ↔
      ∃ neutral₁ neutral₂,
        (∀ a ∈ neutral₁, s3Phase a = 0) ∧
        (∀ a ∈ neutral₂, s3Phase a = 0) ∧
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

private theorem filter_pairBlock (x y : S3Alphabet)
    (hx : s3Phase x = 1) (hy : s3Phase y = 1)
    (word : Word S3Alphabet) (hword : word ∈ pairBlock x y) :
    phaseOneFilter word = [x, y] := by
  obtain ⟨neutral₁, neutral₂, hneutral₁, hneutral₂, rfl⟩ :=
    (mem_pairBlock_iff x y word).1 hword
  rw [phaseOneFilter_append, phaseOneFilter_append,
    filter_neutral neutral₁ hneutral₁]
  have hneutral₂' := filter_neutral neutral₂ hneutral₂
  unfold phaseOneFilter at hneutral₂' ⊢
  simp [hx, hy, hneutral₂']

private theorem ends_pairBlock (x y : S3Alphabet) (word : Word S3Alphabet)
    (hword : word ∈ pairBlock x y) : EndsWith y word := by
  obtain ⟨neutral₁, neutral₂, -, -, rfl⟩ :=
    (mem_pairBlock_iff x y word).1 hword
  exact ⟨neutral₁ ++ x :: neutral₂, by simp [List.append_assoc]⟩

private theorem ends_append_right (y : S3Alphabet)
    (pre suffix : Word S3Alphabet) (hsuffix : suffix ≠ [])
    (hends : EndsWith y (pre ++ suffix)) : EndsWith y suffix := by
  have hlast : (pre ++ suffix).getLast? = some y :=
    List.getLast?_eq_some_iff.2 hends
  rw [List.getLast?_append_of_ne_nil pre hsuffix] at hlast
  exact List.getLast?_eq_some_iff.1 hlast

private theorem mem_power_pairBlock_of_filter (x y : S3Alphabet)
    (_hx : s3Phase x = 1) (hy : s3Phase y = 1) :
    ∀ n word,
      phaseOneFilter word = (List.replicate (n + 1) [x, y]).flatten →
      EndsWith y word →
      word ∈ Language.power (pairBlock x y) (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro word hfilter hends
      have hfilter' : phaseOneFilter word = x :: y :: [] := by
        simpa using hfilter
      obtain ⟨neutral₁, suffix₁, hsplit₁, hneutral₁, hsuffix₁⟩ :=
        exists_first_phaseOne word x (y :: []) hfilter'
      obtain ⟨neutral₂, suffix₂, hsplit₂, hneutral₂, hsuffix₂⟩ :=
        exists_first_phaseOne suffix₁ y [] hsuffix₁
      have hsuffix₂_nil : suffix₂ = [] := by
        by_contra hsuffix₂_ne
        have hends₂ : EndsWith y suffix₂ := by
          apply ends_append_right y (neutral₁ ++ x :: neutral₂ ++ [y]) suffix₂
            hsuffix₂_ne
          simpa [hsplit₁, hsplit₂, List.append_assoc] using hends
        have hlast := ends_filter_last y hy suffix₂ hends₂
        rw [hsuffix₂] at hlast
        simp at hlast
      subst suffix₂
      rw [Language.power_succ_left]
      refine ⟨word, ?_, [], ?_, by simp⟩
      · apply (mem_pairBlock_iff x y word).2
        exact ⟨neutral₁, neutral₂, hneutral₁, hneutral₂, by
          rw [hsplit₁, hsplit₂]
          simp [List.append_assoc]⟩
      · simp [Language.power, Language.epsilon]
  | succ n ih =>
      intro word hfilter hends
      have hfilter' : phaseOneFilter word =
          x :: y :: (List.replicate (n + 1) [x, y]).flatten := by
        simpa [List.replicate_succ, List.flatten_cons] using hfilter
      obtain ⟨neutral₁, suffix₁, hsplit₁, hneutral₁, hsuffix₁⟩ :=
        exists_first_phaseOne word x
          (y :: (List.replicate (n + 1) [x, y]).flatten) hfilter'
      obtain ⟨neutral₂, suffix₂, hsplit₂, hneutral₂, hsuffix₂⟩ :=
        exists_first_phaseOne suffix₁ y
          ((List.replicate (n + 1) [x, y]).flatten) hsuffix₁
      have hsuffix₂_ne : suffix₂ ≠ [] := by
        intro hsuffix₂_nil
        subst suffix₂
        simp [phaseOneFilter, List.replicate_succ] at hsuffix₂
      have hends₂ : EndsWith y suffix₂ := by
        apply ends_append_right y (neutral₁ ++ x :: neutral₂ ++ [y]) suffix₂
          hsuffix₂_ne
        simpa [hsplit₁, hsplit₂, List.append_assoc] using hends
      have hrest : suffix₂ ∈ Language.power (pairBlock x y) (n + 1) :=
        ih suffix₂ hsuffix₂ hends₂
      rw [Language.power_succ_left]
      refine ⟨neutral₁ ++ x :: neutral₂ ++ [y], ?_, suffix₂, hrest, ?_⟩
      · apply (mem_pairBlock_iff x y _).2
        exact ⟨neutral₁, neutral₂, hneutral₁, hneutral₂, rfl⟩
      · rw [hsplit₁, hsplit₂]
        simp [List.append_assoc]

private theorem mem_star_pairBlock_iff_local (x y : S3Alphabet)
    (hx : s3Phase x = 1) (hy : s3Phase y = 1)
    (word : Word S3Alphabet) :
    word ∈ Language.star (pairBlock x y) ↔ PairLocal x y word := by
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
        have hfilterPiece := filter_pairBlock x y hx hy piece hpiece
        have hendsPiece := ends_pairBlock x y piece hpiece
        subst word
        right
        rcases hlocalRest with rfl | ⟨hendsRest, hblocksRest⟩
        · simpa [phaseOneFilter_append, hfilterPiece, XYBlocks] using
            And.intro hendsPiece (show XYBlocks x y [x, y] from ⟨rfl, rfl, trivial⟩)
        · refine ⟨?_, ?_⟩
          · rcases hendsRest with ⟨before, rfl⟩
            exact ⟨piece ++ before, by simp [List.append_assoc]⟩
          · rw [phaseOneFilter_append, hfilterPiece]
            exact ⟨rfl, rfl, hblocksRest⟩
  · rintro (rfl | ⟨hends, hblocks⟩)
    · exact ⟨0, by simp [Language.power, Language.epsilon]⟩
    · obtain ⟨n, hfilter⟩ := xyBlocks_to_star x y (phaseOneFilter word) hblocks
      cases n with
      | zero =>
          have hlast := ends_filter_last y hy word hends
          rw [hfilter] at hlast
          simp at hlast
      | succ n =>
          exact ⟨n + 1, mem_power_pairBlock_of_filter x y hx hy n word
            (by simpa using hfilter) hends⟩

theorem mem_pairBlockStarR_iff_local (x y : S3Alphabet)
    (hx : s3Phase x = 1) (hy : s3Phase y = 1) (hne : x ≠ y)
    (word : Word S3Alphabet) :
    word ∈ GRegex.denote (pairBlockStarR x y) ↔ PairLocal x y word := by
  classical
  rw [pairBlockStarR]
  simp only [GRegex.denote, Set.mem_union, Language.mem_epsilon_iff,
    interR, Language.mem_compl_iff,
    mem_denote_endsWithR_iff, mem_denote_startsWithAfterNeutralR_iff,
    mem_denote_repeatedAfterNeutralR_iff, mem_denote_containsOtherFlipR_iff,
    not_or, not_not]
  constructor
  · rintro (rfl | ⟨hends, hnoStart, hnoRepeatX, hnoRepeatY, hnoOther⟩)
    · exact Or.inl rfl
    · apply Or.inr
      refine ⟨hends, ?_⟩
      apply xyBlocks_of_local x y hne (phaseOneFilter word)
      · intro a ha
        by_contra hallowed
        push Not at hallowed
        exact hnoOther ((containsOther_iff_filter x y word).2
          ⟨a, ha, hallowed.1, hallowed.2⟩)
      · cases hfilter : phaseOneFilter word with
        | nil => exact Or.inl rfl
        | cons a rest =>
            right
            have haAllowed : a = x ∨ a = y := by
              have haMem : a ∈ phaseOneFilter word := by rw [hfilter]; simp
              by_contra hallowed
              push Not at hallowed
              exact hnoOther ((containsOther_iff_filter x y word).2
                ⟨a, haMem, hallowed.1, hallowed.2⟩)
            rcases haAllowed with haX | haY
            · simp [haX]
            · exact False.elim (hnoStart ((starts_iff_filter_cons y hy word).2
                ⟨rest, by simpa [haY] using hfilter⟩))
      · right
        exact ends_filter_last y hy word hends
      · apply chain_of_allowed_no_patterns x y (phaseOneFilter word)
        · intro a ha
          by_contra hallowed
          push Not at hallowed
          exact hnoOther ((containsOther_iff_filter x y word).2
            ⟨a, ha, hallowed.1, hallowed.2⟩)
        · intro hbad
          exact hnoRepeatX ((repeated_iff_filter_pattern x hx word).2 hbad)
        · intro hbad
          exact hnoRepeatY ((repeated_iff_filter_pattern y hy word).2 hbad)
  · rintro (rfl | ⟨hends, hblocks⟩)
    · exact Or.inl rfl
    · apply Or.inr
      have hlocal := local_of_xyBlocks x y hne (phaseOneFilter word) hblocks
      rcases hlocal with ⟨hallowed, hhead, -, hchain⟩
      refine ⟨hends, ?_, ?_, ?_, ?_⟩
      · intro hstart
        obtain ⟨tail, hfilter⟩ := (starts_iff_filter_cons y hy word).1 hstart
        rcases hhead with hnil | hhead
        · rw [hfilter] at hnil; simp at hnil
        · rw [hfilter] at hhead
          simp at hhead
          exact hne hhead.symm
      · intro hrepeat
        obtain ⟨before, after, hfilter⟩ :=
          (repeated_iff_filter_pattern x hx word).1 hrepeat
        have := hchain.drop before.length
        rw [hfilter] at this
        simp at this
      · intro hrepeat
        obtain ⟨before, after, hfilter⟩ :=
          (repeated_iff_filter_pattern y hy word).1 hrepeat
        have := hchain.drop before.length
        rw [hfilter] at this
        simp at this
      · intro hother
        obtain ⟨a, ha, hax, hay⟩ := (containsOther_iff_filter x y word).1 hother
        rcases hallowed a ha with rfl | rfl
        · exact hax rfl
        · exact hay rfl

@[simp]
theorem starHeight_pairBlockStarR (x y : S3Alphabet) :
    GRegex.starHeight (pairBlockStarR x y) = 0 := by
  simp [pairBlockStarR, interR, endsWithR, startsWithAfterNeutralR,
    repeatedAfterNeutralR, containsOtherFlipR, neutralWordsR,
    Counting.univR, GRegex.starHeight]

/-- The height-zero local-pattern expression denotes exactly the star of a
fixed distinct phase-one pair block. -/
theorem denote_pairBlockStarR (x y : S3Alphabet)
    (hx : s3Phase x = 1) (hy : s3Phase y = 1) (hne : x ≠ y) :
    GRegex.denote (pairBlockStarR x y) = Language.star (pairBlock x y) := by
  ext word
  exact (mem_pairBlockStarR_iff_local x y hx hy hne word).trans
    (mem_star_pairBlock_iff_local x y hx hy word).symm

/-- The star of a fixed distinct phase-one pair block is generalized
star-free. -/
theorem isStarFree_pairBlockStar (x y : S3Alphabet)
    (hx : s3Phase x = 1) (hy : s3Phase y = 1) (hne : x ≠ y) :
    IsStarFree (Language.star (pairBlock x y)) :=
  ⟨pairBlockStarR x y, denote_pairBlockStarR x y hx hy hne, by simp⟩

/-- Once the local-pattern characterization is proved semantically, the
desired star-freeness conclusion follows without any further height work. -/
theorem isStarFree_pairBlockStar_of_denote (x y : S3Alphabet)
    (hdenote : GRegex.denote (pairBlockStarR x y) =
      Language.star (pairBlock x y)) :
    IsStarFree (Language.star (pairBlock x y)) :=
  ⟨pairBlockStarR x y, hdenote, by simp⟩

end S3FlipPairHeight

end GSH
