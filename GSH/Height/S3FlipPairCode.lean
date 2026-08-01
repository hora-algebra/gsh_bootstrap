import GSH.Height.S3ArrowArithmetic
import GSH.Height.S3ArrowResidue

/-!
# Canonical phase-one pair blocks for `S₃`

This file begins the word-level code used by the moving-edge branch.  A block
contains a neutral prefix, one phase-one letter, a neutral gap, and a second
phase-one letter.  An even-phase word decomposes into such blocks followed by
a neutral suffix.
-/

set_option autoImplicit false

namespace GSH

namespace S3FlipPairCode

open ArrowCounting
open S3ArrowArithmetic

/-- A word with no phase-one letters. -/
abbrev IsNeutralWord (word : Word S3Alphabet) : Prop :=
  S3ArrowResidue.IsPhaseZeroWord s3Phase word

/-- One canonical ordered phase-one pair block `Z* x Z* y`. -/
def IsPairBlock (word : Word S3Alphabet) : Prop :=
  ∃ leading x middle y,
    IsNeutralWord leading ∧ s3Phase x = 1 ∧
      IsNeutralWord middle ∧ s3Phase y = 1 ∧
        word = leading ++ x :: middle ++ [y]

/-- A factorization into pair blocks and a final neutral suffix. -/
def IsPairFactorization (pieces : List (Word S3Alphabet))
    (suffix word : Word S3Alphabet) : Prop :=
  (∀ piece ∈ pieces, IsPairBlock piece) ∧ IsNeutralWord suffix ∧
    pieces.flatten ++ suffix = word

private theorem phase_eq_zero_or_one (p : S3Alphabet) :
    s3Phase p = 0 ∨ s3Phase p = 1 := by
  unfold s3Phase
  split <;> simp

private theorem run_neutral (start : ZMod 2) (word : Word S3Alphabet)
    (hword : IsNeutralWord word) :
    runFrom (c2Step s3Phase) start word = start := by
  induction word generalizing start with
  | nil => rfl
  | cons a word ih =>
      have ha : s3Phase a = 0 := hword a (by simp)
      have hw : IsNeutralWord word := by
        intro b hb
        exact hword b (by simp [hb])
      simp [runFrom_cons, c2Step, ha, ih start hw]

private theorem exists_first_flip (word : Word S3Alphabet)
    (h : ∃ a ∈ word, s3Phase a = 1) :
    ∃ leading x tail, word = leading ++ x :: tail ∧
      IsNeutralWord leading ∧ s3Phase x = 1 := by
  induction word with
  | nil => simp at h
  | cons a word ih =>
      by_cases ha : s3Phase a = 1
      · exact ⟨[], a, word, rfl, (by intro b hb; simp at hb), ha⟩
      · have ha0 : s3Phase a = 0 :=
          (phase_eq_zero_or_one a).resolve_right ha
        have htail : ∃ b ∈ word, s3Phase b = 1 := by
          rcases h with ⟨b, hb, hb1⟩
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact absurd hb1 ha
          · exact ⟨b, hb, hb1⟩
        obtain ⟨leading, x, tail, hsplit, hleading, hx⟩ := ih htail
        refine ⟨a :: leading, x, tail, ?_, ?_, hx⟩
        · simp [hsplit]
        · intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact ha0
          · exact hleading b hb

private theorem exists_pairFactorization_of_length :
    ∀ n : Nat, ∀ word : Word S3Alphabet, word.length = n →
      runFrom (c2Step s3Phase) 0 word = 0 →
      ∃ pieces suffix, IsPairFactorization pieces suffix word := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih word hlength hrun
  by_cases hcontains : ∃ a ∈ word, s3Phase a = 1
  · obtain ⟨leading, x, rest, rfl, hleading, hx⟩ :=
      exists_first_flip word hcontains
    have hrunRest : runFrom (c2Step s3Phase) 1 rest = 0 := by
      rw [runFrom_append] at hrun
      simp [run_neutral 0 leading hleading, runFrom_cons, c2Step, hx] at hrun
      exact hrun
    have hcontainsRest : ∃ a ∈ rest, s3Phase a = 1 := by
      by_contra hnone
      have hneutral : IsNeutralWord rest := by
        intro a ha
        rcases phase_eq_zero_or_one a with ha0 | ha1
        · exact ha0
        · exact False.elim (hnone ⟨a, ha, ha1⟩)
      have hone := run_neutral 1 rest hneutral
      rw [hrunRest] at hone
      exact zero_ne_one hone
    obtain ⟨middle, y, tail, rfl, hmiddle, hy⟩ :=
      exists_first_flip rest hcontainsRest
    have hrunTail : runFrom (c2Step s3Phase) 0 tail = 0 := by
      rw [runFrom_append] at hrunRest
      simp [run_neutral 1 middle hmiddle, runFrom_cons, c2Step, hy] at hrunRest
      exact hrunRest
    have htailLength : tail.length < n := by
      rw [← hlength]
      simp only [List.length_append, List.length_cons]
      omega
    obtain ⟨pieces, suffix, hfactor⟩ :=
      ih tail.length htailLength tail rfl hrunTail
    refine ⟨(leading ++ x :: middle ++ [y]) :: pieces, suffix, ?_,
      hfactor.2.1, ?_⟩
    · intro piece hpiece
      simp only [List.mem_cons] at hpiece
      rcases hpiece with rfl | hpiece
      · exact ⟨leading, x, middle, y, hleading, hx, hmiddle, hy, rfl⟩
      · exact hfactor.1 piece hpiece
    · simp only [List.flatten_cons]
      rw [List.append_assoc, hfactor.2.2]
      simp
  · have hneutral : IsNeutralWord word := by
      intro a ha
      rcases phase_eq_zero_or_one a with ha0 | ha1
      · exact ha0
      · exact False.elim (hcontains ⟨a, ha, ha1⟩)
    exact ⟨[], word, by simp, hneutral, rfl⟩

/-- Every phase-zero-total `S₃` word decomposes into ordered phase-one
pair blocks and a final neutral suffix. -/
theorem exists_pairFactorization (word : Word S3Alphabet)
    (hphase : (word.map s3Phase).sum = 0) :
    ∃ pieces suffix, IsPairFactorization pieces suffix word := by
  have hrun : runFrom (c2Step s3Phase) 0 word = 0 := by
    simpa [c2RunFrom, c2Step] using
      (c2RunFrom_eq s3Phase 0 word).trans (by simp [hphase])
  exact exists_pairFactorization_of_length word.length word rfl hrun

local instance : BEq S3PhaseOne := instBEqOfDecidableEq

/-- Filtering phase-one letters commutes with word concatenation. -/
theorem phaseOneSubword_append (left right : Word S3Alphabet) :
    phaseOneSubword (left ++ right) =
      phaseOneSubword left ++ phaseOneSubword right := by
  induction left with
  | nil => rfl
  | cons a left ih =>
      by_cases ha : s3Phase a = 1 <;>
        simp [phaseOneSubword, ha, ih]

/-- A neutral word has empty phase-one subword. -/
theorem phaseOneSubword_eq_nil_of_neutral (word : Word S3Alphabet)
    (hword : IsNeutralWord word) : phaseOneSubword word = [] := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      have ha : s3Phase a = 0 := hword a (by simp)
      have htail : IsNeutralWord word := by
        intro b hb
        exact hword b (by simp [hb])
      simp [phaseOneSubword, ha, ih htail]

/-- Every pair block filters to exactly its two ordered phase-one labels. -/
theorem phaseOneSubword_pairBlock (piece : Word S3Alphabet)
    (hpiece : IsPairBlock piece) :
    ∃ x y : S3PhaseOne, phaseOneSubword piece = [x, y] := by
  rcases hpiece with ⟨leading, x, middle, y, hleading, hx,
    hmiddle, hy, rfl⟩
  refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ?_⟩
  simp [phaseOneSubword, hx, hy, phaseOneSubword_append,
    phaseOneSubword_eq_nil_of_neutral leading hleading,
    phaseOneSubword_eq_nil_of_neutral middle hmiddle]

/-- Number of blocks carrying a distinguished ordered pair. -/
def pairBlockCount (x y : S3PhaseOne) : List (Word S3Alphabet) → Nat
  | [] => 0
  | piece :: pieces =>
      (if phaseOneSubword piece = [x, y] then 1 else 0) +
        pairBlockCount x y pieces

private theorem pairBlockCount_eq_pairCountOf_flatten
    (x y : S3PhaseOne) (pieces : List (Word S3Alphabet))
    (hpieces : ∀ piece ∈ pieces, IsPairBlock piece) :
    pairBlockCount x y pieces =
      pairCountOf x y (phaseOneSubword pieces.flatten) := by
  induction pieces with
  | nil => simp [pairBlockCount, phaseOneSubword]
  | cons piece pieces ih =>
      have hpiece := hpieces piece (by simp)
      have hrest : ∀ p ∈ pieces, IsPairBlock p := by
        intro p hp
        exact hpieces p (by simp [hp])
      obtain ⟨a, b, hab⟩ := phaseOneSubword_pairBlock piece hpiece
      rw [List.flatten_cons, phaseOneSubword_append, hab]
      by_cases hax : a = x <;> by_cases hby : b = y <;>
        simp [pairBlockCount, hab, hax, hby, ih hrest]

/-- In any valid factorization, the number of distinguished `(x,y)` blocks
is the fixed pair count in the filtered phase-one word. -/
theorem pairBlockCount_eq_pairCountOf (x y : S3PhaseOne)
    (pieces : List (Word S3Alphabet)) (suffix word : Word S3Alphabet)
    (hfactor : IsPairFactorization pieces suffix word) :
    pairBlockCount x y pieces = pairCountOf x y (phaseOneSubword word) := by
  have hsuffix := phaseOneSubword_eq_nil_of_neutral suffix hfactor.2.1
  calc
    pairBlockCount x y pieces =
        pairCountOf x y (phaseOneSubword pieces.flatten) :=
      pairBlockCount_eq_pairCountOf_flatten x y pieces hfactor.1
    _ = pairCountOf x y (phaseOneSubword (pieces.flatten ++ suffix)) := by
      rw [phaseOneSubword_append, hsuffix]
      simp
    _ = pairCountOf x y (phaseOneSubword word) := by rw [hfactor.2.2]

private theorem map_neutral (word : Word S3Alphabet)
    (hword : IsNeutralWord word) :
    word.map s3Phase = List.replicate word.length 0 := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      have ha : s3Phase a = 0 := hword a (by simp)
      have htail : IsNeutralWord word := by
        intro b hb
        exact hword b (by simp [hb])
      simp [ha, ih htail, List.replicate_succ]

private theorem zeros_before_one_unique (m n : Nat)
    (leftTail rightTail : List (ZMod 2))
    (h : List.replicate m 0 ++ 1 :: leftTail =
      List.replicate n 0 ++ 1 :: rightTail) : m = n := by
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ n =>
          rw [List.replicate_succ] at h
          have hbad : (1 : ZMod 2) = 0 := by
            simpa using congrArg List.head? h
          exact False.elim (one_ne_zero hbad)
  | succ m ih =>
      cases n with
      | zero =>
          rw [List.replicate_succ] at h
          have hbad : (0 : ZMod 2) = 1 := by
            simpa using congrArg List.head? h
          exact False.elim (zero_ne_one hbad)
      | succ n =>
          simp only [List.replicate_succ, List.cons_append, List.cons.injEq,
            true_and] at h
          exact congrArg Nat.succ (ih n h)

/-- Pair blocks form a prefix code: two valid blocks cannot be proper prefixes
of one another. -/
theorem pairBlock_eq_of_prefix (left right suffix : Word S3Alphabet)
    (hleft : IsPairBlock left) (hright : IsPairBlock right)
    (hprefix : right = left ++ suffix) : left = right := by
  rcases hleft with ⟨leading₁, x₁, middle₁, y₁, hl₁, hx₁,
    hm₁, hy₁, rfl⟩
  rcases hright with ⟨leading₂, x₂, middle₂, y₂, hl₂, hx₂,
    hm₂, hy₂, rfl⟩
  have hphase := congrArg (List.map s3Phase) hprefix
  have hleadingLength : leading₂.length = leading₁.length := by
    apply zeros_before_one_unique leading₂.length leading₁.length
      (List.replicate middle₂.length 0 ++ [1])
      (List.replicate middle₁.length 0 ++ [1] ++ suffix.map s3Phase)
    simpa [map_neutral leading₁ hl₁, map_neutral leading₂ hl₂,
      map_neutral middle₁ hm₁, map_neutral middle₂ hm₂,
      hx₁, hx₂, hy₁, hy₂, List.append_assoc] using hphase
  have hphaseTail :
      List.replicate middle₂.length 0 ++ [1] =
        List.replicate middle₁.length 0 ++ [1] ++ suffix.map s3Phase := by
    simpa [map_neutral leading₁ hl₁, map_neutral leading₂ hl₂,
      map_neutral middle₁ hm₁, map_neutral middle₂ hm₂,
      hx₁, hx₂, hy₁, hy₂, hleadingLength, List.append_assoc] using hphase
  have hmiddleLength : middle₂.length = middle₁.length := by
    apply zeros_before_one_unique middle₂.length middle₁.length []
      (suffix.map s3Phase)
    simpa [List.append_assoc] using hphaseTail
  have hblockLength :
      (leading₁ ++ x₁ :: middle₁ ++ [y₁]).length =
        (leading₂ ++ x₂ :: middle₂ ++ [y₂]).length := by
    simp [hleadingLength, hmiddleLength]
  have hsLength := congrArg List.length hprefix
  have hs : suffix = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_append, List.length_cons] at hblockLength hsLength
    omega
  simpa [hs] using hprefix.symm

/-- Valid block/suffix factorizations of the same word are unique. -/
theorem pairFactorization_unique
    (leftPieces rightPieces : List (Word S3Alphabet))
    (leftSuffix rightSuffix word : Word S3Alphabet)
    (hleft : IsPairFactorization leftPieces leftSuffix word)
    (hright : IsPairFactorization rightPieces rightSuffix word) :
    leftPieces = rightPieces ∧ leftSuffix = rightSuffix := by
  induction leftPieces generalizing rightPieces word with
  | nil =>
      cases rightPieces with
      | nil =>
          have hleftSuffix : leftSuffix = word := by simpa using hleft.2.2
          have hrightSuffix : rightSuffix = word := by simpa using hright.2.2
          exact ⟨rfl, hleftSuffix.trans hrightSuffix.symm⟩
      | cons piece pieces =>
          have hp := hright.1 piece (by simp)
          rcases hp with ⟨leading, x, middle, y, -, hx, -, -, rfl⟩
          have hxmem : x ∈ word := by
            rw [← hright.2.2]
            simp
          have hleftSuffix : leftSuffix = word := by simpa using hleft.2.2
          have hx0 := hleft.2.1 x (by simpa [hleftSuffix] using hxmem)
          rw [hx0] at hx
          exact False.elim (zero_ne_one hx)
  | cons piece pieces ih =>
      cases rightPieces with
      | nil =>
          have hp := hleft.1 piece (by simp)
          rcases hp with ⟨leading, x, middle, y, -, hx, -, -, rfl⟩
          have hxmem : x ∈ word := by
            rw [← hleft.2.2]
            simp
          have hrightSuffix : rightSuffix = word := by simpa using hright.2.2
          have hx0 := hright.2.1 x (by simpa [hrightSuffix] using hxmem)
          rw [hx0] at hx
          exact False.elim (zero_ne_one hx)
      | cons piece' pieces' =>
          have hp := hleft.1 piece (by simp)
          have hp' := hright.1 piece' (by simp)
          have hflat : piece ++ (pieces.flatten ++ leftSuffix) =
              piece' ++ (pieces'.flatten ++ rightSuffix) := by
            simpa [List.append_assoc] using hleft.2.2.trans hright.2.2.symm
          have hpiece : piece = piece' := by
            rcases List.append_eq_append_iff.mp hflat with
                ⟨suffix, hprefix, -⟩ | ⟨suffix, hprefix, -⟩
            · exact pairBlock_eq_of_prefix piece piece' suffix hp hp' hprefix
            · exact (pairBlock_eq_of_prefix piece' piece suffix hp' hp hprefix).symm
          subst piece'
          have htailFlat : pieces.flatten ++ leftSuffix =
              pieces'.flatten ++ rightSuffix := by
            simpa using hflat
          have hleftTail :
              IsPairFactorization pieces leftSuffix
                (pieces.flatten ++ leftSuffix) :=
            ⟨(by intro p hpMem; exact hleft.1 p (by simp [hpMem])),
              hleft.2.1, rfl⟩
          have hrightTail :
              IsPairFactorization pieces' rightSuffix
                (pieces.flatten ++ leftSuffix) :=
            ⟨(by intro p hpMem; exact hright.1 p (by simp [hpMem])),
              hright.2.1, htailFlat.symm⟩
          obtain ⟨hpieces, hsuffix⟩ :=
            ih pieces' (pieces.flatten ++ leftSuffix) hleftTail hrightTail
          exact ⟨congrArg (List.cons piece) hpieces, hsuffix⟩

end S3FlipPairCode

end GSH
