import GSH.Height.D5FlipPairHeight
import GSH.Height.TransferModulusSemantics

/-!
# The zero-residue transfer for canonical `D₅` reflection pairs

The final neutral suffix is retained explicitly.  Thus the language below
includes the phase-zero/even condition rather than silently discarding it.
-/

set_option autoImplicit false

namespace GSH

namespace D5FlipPairTransfer

open ArrowCounting
open S3ArrowArithmetic
open D5FlipPairHeight
open TransferSemantics

/-- Delete phase-zero letters and retain phase-one `D₅` letters. -/
def d5PhaseOneSubword : Word D5Alphabet → Word D5PhaseOne
  | [] => []
  | p :: word =>
      if hp : d5Phase p = 1 then
        ⟨p, hp⟩ :: d5PhaseOneSubword word
      else d5PhaseOneSubword word

private theorem d5Phase_eq_zero_of_ne_one (p : D5Alphabet)
    (hp : d5Phase p ≠ 1) : d5Phase p = 0 := by
  rcases p with i | i <;> simp [d5Phase] at hp ⊢

theorem d5PhaseOneSubword_length_cast (word : Word D5Alphabet) :
    ((d5PhaseOneSubword word).length : ZMod 2) =
      (word.map d5Phase).sum := by
  induction word with
  | nil => simp [d5PhaseOneSubword]
  | cons p word ih =>
      by_cases hp : d5Phase p = 1
      · simp [d5PhaseOneSubword, hp, ih, add_comm]
      · have hp0 := d5Phase_eq_zero_of_ne_one p hp
        simp [d5PhaseOneSubword, hp0, ih]

theorem d5PhaseOneSubword_even_iff_phase_sum_zero
    (word : Word D5Alphabet) :
    (d5PhaseOneSubword word).length % 2 = 0 ↔
      (word.map d5Phase).sum = 0 := by
  rw [← d5PhaseOneSubword_length_cast]
  simpa [Nat.dvd_iff_mod_eq_zero] using
    (ZMod.natCast_eq_zero_iff (d5PhaseOneSubword word).length 2).symm

abbrev IsNeutralWord (word : Word D5Alphabet) : Prop :=
  ∀ a ∈ word, d5Phase a = 0

def IsPairBlock (word : Word D5Alphabet) : Prop :=
  ∃ leading x middle y,
    IsNeutralWord leading ∧ d5Phase x = 1 ∧
      IsNeutralWord middle ∧ d5Phase y = 1 ∧
        word = leading ++ x :: middle ++ [y]

def IsPairFactorization (pieces : List (Word D5Alphabet))
    (suffix word : Word D5Alphabet) : Prop :=
  (∀ piece ∈ pieces, IsPairBlock piece) ∧ IsNeutralWord suffix ∧
    pieces.flatten ++ suffix = word

private theorem phase_eq_zero_or_one (p : D5Alphabet) :
    d5Phase p = 0 ∨ d5Phase p = 1 := by
  rcases p with i | i <;> simp [d5Phase]

private theorem run_neutral (start : ZMod 2) (word : Word D5Alphabet)
    (hword : IsNeutralWord word) :
    runFrom (c2Step d5Phase) start word = start := by
  induction word generalizing start with
  | nil => rfl
  | cons a word ih =>
      have ha : d5Phase a = 0 := hword a (by simp)
      have hw : IsNeutralWord word := by
        intro b hb
        exact hword b (by simp [hb])
      simp [runFrom_cons, c2Step, ha, ih start hw]

private theorem exists_first_flip (word : Word D5Alphabet)
    (h : ∃ a ∈ word, d5Phase a = 1) :
    ∃ leading x tail, word = leading ++ x :: tail ∧
      IsNeutralWord leading ∧ d5Phase x = 1 := by
  induction word with
  | nil => simp at h
  | cons a word ih =>
      by_cases ha : d5Phase a = 1
      · exact ⟨[], a, word, rfl, (by intro b hb; simp at hb), ha⟩
      · have ha0 : d5Phase a = 0 :=
          (phase_eq_zero_or_one a).resolve_right ha
        have htail : ∃ b ∈ word, d5Phase b = 1 := by
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
    ∀ n : Nat, ∀ word : Word D5Alphabet, word.length = n →
      runFrom (c2Step d5Phase) 0 word = 0 →
      ∃ pieces suffix, IsPairFactorization pieces suffix word := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih word hlength hrun
  by_cases hcontains : ∃ a ∈ word, d5Phase a = 1
  · obtain ⟨leading, x, rest, rfl, hleading, hx⟩ :=
      exists_first_flip word hcontains
    have hrunRest : runFrom (c2Step d5Phase) 1 rest = 0 := by
      rw [runFrom_append] at hrun
      simp [run_neutral 0 leading hleading, runFrom_cons, c2Step, hx] at hrun
      exact hrun
    have hcontainsRest : ∃ a ∈ rest, d5Phase a = 1 := by
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
    have hrunTail : runFrom (c2Step d5Phase) 0 tail = 0 := by
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

theorem exists_pairFactorization (word : Word D5Alphabet)
    (hphase : (word.map d5Phase).sum = 0) :
    ∃ pieces suffix, IsPairFactorization pieces suffix word := by
  have hrun : runFrom (c2Step d5Phase) 0 word = 0 := by
    simpa [c2RunFrom, c2Step] using
      (c2RunFrom_eq d5Phase 0 word).trans (by simp [hphase])
  exact exists_pairFactorization_of_length word.length word rfl hrun

local instance : BEq D5PhaseOne := instBEqOfDecidableEq

theorem phaseOneSubword_append (left right : Word D5Alphabet) :
    d5PhaseOneSubword (left ++ right) =
      d5PhaseOneSubword left ++ d5PhaseOneSubword right := by
  induction left with
  | nil => rfl
  | cons a left ih =>
      by_cases ha : d5Phase a = 1 <;>
        simp [d5PhaseOneSubword, ha, ih]

theorem phaseOneSubword_eq_nil_of_neutral (word : Word D5Alphabet)
    (hword : IsNeutralWord word) : d5PhaseOneSubword word = [] := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      have ha : d5Phase a = 0 := hword a (by simp)
      have htail : IsNeutralWord word := by
        intro b hb
        exact hword b (by simp [hb])
      simp [d5PhaseOneSubword, ha, ih htail]

theorem phaseOneSubword_pairBlock (piece : Word D5Alphabet)
    (hpiece : IsPairBlock piece) :
    ∃ x y : D5PhaseOne, d5PhaseOneSubword piece = [x, y] := by
  rcases hpiece with ⟨leading, x, middle, y, hleading, hx,
    hmiddle, hy, rfl⟩
  refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ?_⟩
  simp [d5PhaseOneSubword, hx, hy, phaseOneSubword_append,
    phaseOneSubword_eq_nil_of_neutral leading hleading,
    phaseOneSubword_eq_nil_of_neutral middle hmiddle]

def pairBlockCount (x y : D5PhaseOne) : List (Word D5Alphabet) → Nat
  | [] => 0
  | piece :: pieces =>
      (if d5PhaseOneSubword piece = [x, y] then 1 else 0) +
        pairBlockCount x y pieces

private theorem pairBlockCount_eq_pairCountOf_flatten
    (x y : D5PhaseOne) (pieces : List (Word D5Alphabet))
    (hpieces : ∀ piece ∈ pieces, IsPairBlock piece) :
    pairBlockCount x y pieces =
      pairCountOf x y (d5PhaseOneSubword pieces.flatten) := by
  induction pieces with
  | nil => simp [pairBlockCount, d5PhaseOneSubword]
  | cons piece pieces ih =>
      have hpiece := hpieces piece (by simp)
      have hrest : ∀ p ∈ pieces, IsPairBlock p := by
        intro p hp
        exact hpieces p (by simp [hp])
      obtain ⟨a, b, hab⟩ := phaseOneSubword_pairBlock piece hpiece
      rw [List.flatten_cons, phaseOneSubword_append, hab]
      by_cases hax : a = x <;> by_cases hby : b = y <;>
        simp [pairBlockCount, hab, hax, hby, ih hrest]

theorem pairBlockCount_eq_pairCountOf (x y : D5PhaseOne)
    (pieces : List (Word D5Alphabet)) (suffix word : Word D5Alphabet)
    (hfactor : IsPairFactorization pieces suffix word) :
    pairBlockCount x y pieces =
      pairCountOf x y (d5PhaseOneSubword word) := by
  have hsuffix := phaseOneSubword_eq_nil_of_neutral suffix hfactor.2.1
  calc
    pairBlockCount x y pieces =
        pairCountOf x y (d5PhaseOneSubword pieces.flatten) :=
      pairBlockCount_eq_pairCountOf_flatten x y pieces hfactor.1
    _ = pairCountOf x y
        (d5PhaseOneSubword (pieces.flatten ++ suffix)) := by
      rw [phaseOneSubword_append, hsuffix]
      simp
    _ = pairCountOf x y (d5PhaseOneSubword word) := by rw [hfactor.2.2]

private theorem map_neutral (word : Word D5Alphabet)
    (hword : IsNeutralWord word) :
    word.map d5Phase = List.replicate word.length 0 := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      have ha : d5Phase a = 0 := hword a (by simp)
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

theorem pairBlock_eq_of_prefix (left right suffix : Word D5Alphabet)
    (hleft : IsPairBlock left) (hright : IsPairBlock right)
    (hprefix : right = left ++ suffix) : left = right := by
  rcases hleft with ⟨leading₁, x₁, middle₁, y₁, hl₁, hx₁,
    hm₁, hy₁, rfl⟩
  rcases hright with ⟨leading₂, x₂, middle₂, y₂, hl₂, hx₂,
    hm₂, hy₂, rfl⟩
  have hphase := congrArg (List.map d5Phase) hprefix
  have hleadingLength : leading₂.length = leading₁.length := by
    apply zeros_before_one_unique leading₂.length leading₁.length
      (List.replicate middle₂.length 0 ++ [1])
      (List.replicate middle₁.length 0 ++ [1] ++ suffix.map d5Phase)
    simpa [map_neutral leading₁ hl₁, map_neutral leading₂ hl₂,
      map_neutral middle₁ hm₁, map_neutral middle₂ hm₂,
      hx₁, hx₂, hy₁, hy₂, List.append_assoc] using hphase
  have hphaseTail :
      List.replicate middle₂.length 0 ++ [1] =
        List.replicate middle₁.length 0 ++ [1] ++ suffix.map d5Phase := by
    simpa [map_neutral leading₁ hl₁, map_neutral leading₂ hl₂,
      map_neutral middle₁ hm₁, map_neutral middle₂ hm₂,
      hx₁, hx₂, hy₁, hy₂, hleadingLength,
      List.append_assoc] using hphase
  have hmiddleLength : middle₂.length = middle₁.length := by
    apply zeros_before_one_unique middle₂.length middle₁.length []
      (suffix.map d5Phase)
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

theorem pairFactorization_unique
    (leftPieces rightPieces : List (Word D5Alphabet))
    (leftSuffix rightSuffix word : Word D5Alphabet)
    (hleft : IsPairFactorization leftPieces leftSuffix word)
    (hright : IsPairFactorization rightPieces rightSuffix word) :
    leftPieces = rightPieces ∧ leftSuffix = rightSuffix := by
  induction leftPieces generalizing rightPieces word with
  | nil =>
      cases rightPieces with
      | nil =>
          have hl : leftSuffix = word := by simpa using hleft.2.2
          have hr : rightSuffix = word := by simpa using hright.2.2
          exact ⟨rfl, hl.trans hr.symm⟩
      | cons piece pieces =>
          have hp := hright.1 piece (by simp)
          rcases hp with ⟨leading, x, middle, y, -, hx, -, -, rfl⟩
          have hxmem : x ∈ word := by rw [← hright.2.2]; simp
          have hl : leftSuffix = word := by simpa using hleft.2.2
          have hx0 := hleft.2.1 x (by simpa [hl] using hxmem)
          rw [hx0] at hx
          exact False.elim (zero_ne_one hx)
  | cons piece pieces ih =>
      cases rightPieces with
      | nil =>
          have hp := hleft.1 piece (by simp)
          rcases hp with ⟨leading, x, middle, y, -, hx, -, -, rfl⟩
          have hxmem : x ∈ word := by rw [← hleft.2.2]; simp
          have hr : rightSuffix = word := by simpa using hright.2.2
          have hx0 := hright.2.1 x (by simpa [hr] using hxmem)
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
              pieces'.flatten ++ rightSuffix := by simpa using hflat
          have hleftTail : IsPairFactorization pieces leftSuffix
              (pieces.flatten ++ leftSuffix) :=
            ⟨(by intro p hm; exact hleft.1 p (by simp [hm])), hleft.2.1, rfl⟩
          have hrightTail : IsPairFactorization pieces' rightSuffix
              (pieces.flatten ++ leftSuffix) :=
            ⟨(by intro p hm; exact hright.1 p (by simp [hm])),
              hright.2.1, htailFlat.symm⟩
          obtain ⟨hpieces, hsuffix⟩ :=
            ih pieces' (pieces.flatten ++ leftSuffix) hleftTail hrightTail
          exact ⟨congrArg (List.cons piece) hpieces, hsuffix⟩

def d5PairResidueZero (x y : D5PhaseOne) : Language D5Alphabet :=
  {word | (word.map d5Phase).sum = 0 ∧
    pairCountOf x y (d5PhaseOneSubword word) % 5 = 0}

private theorem mem_pairBlock_iff (x y : D5PhaseOne)
    (word : Word D5Alphabet) :
    word ∈ d5PairBlock x.1 y.1 ↔
      IsPairBlock word ∧ d5PhaseOneSubword word = [x, y] := by
  classical
  constructor
  · intro hword
    rcases hword with ⟨leading, hleading, rest₁,
      ⟨xword, hxword, rest₂,
        ⟨middle, hmiddle, yword, hyword, rfl⟩, rfl⟩, rfl⟩
    have hxword' : xword = [x.1] := hxword
    have hyword' : yword = [y.1] := hyword
    subst xword
    subst yword
    constructor
    · exact ⟨leading, x.1, middle, y.1, hleading, x.2,
        hmiddle, y.2, by simp⟩
    · simp [d5PhaseOneSubword, x.2, y.2, phaseOneSubword_append,
        phaseOneSubword_eq_nil_of_neutral leading hleading,
        phaseOneSubword_eq_nil_of_neutral middle hmiddle]
  · rintro ⟨hblock, hsubword⟩
    rcases hblock with ⟨leading, a, middle, b, hleading, ha,
      hmiddle, hb, rfl⟩
    have hlabels : [⟨a, ha⟩, ⟨b, hb⟩] = [x, y] := by
      simpa [d5PhaseOneSubword, ha, hb, phaseOneSubword_append,
        phaseOneSubword_eq_nil_of_neutral leading hleading,
        phaseOneSubword_eq_nil_of_neutral middle hmiddle] using hsubword
    simp at hlabels
    have hax : a = x.1 := congrArg Subtype.val hlabels.1
    have hby : b = y.1 := congrArg Subtype.val hlabels.2
    subst a
    subst b
    refine ⟨leading, hleading, [x.1] ++ middle ++ [y.1], ?_, ?_⟩
    · refine ⟨[x.1], rfl, middle ++ [y.1], ?_, rfl⟩
      exact ⟨middle, hmiddle, [y.1], rfl, rfl⟩
    · simp [List.append_assoc]

private theorem mem_otherPairBlocks_iff (x y : D5PhaseOne)
    (word : Word D5Alphabet) :
    word ∈ d5OtherPairBlocks x y ↔
      IsPairBlock word ∧ d5PhaseOneSubword word ≠ [x, y] := by
  classical
  simp only [d5OtherPairBlocks, Set.mem_iUnion]
  constructor
  · rintro ⟨pair, hpair⟩
    by_cases hp : pair = (x, y)
    · rw [hp, if_pos rfl] at hpair
      simp at hpair
    · have hmem : word ∈ d5PairBlock pair.1.1 pair.2.1 := by
        simpa [hp] using hpair
      have hcode := (mem_pairBlock_iff pair.1 pair.2 word).mp hmem
      refine ⟨hcode.1, ?_⟩
      intro heq
      have hlabels : [pair.1, pair.2] = [x, y] := hcode.2.symm.trans heq
      simp at hlabels
      exact hp (Prod.ext hlabels.1 hlabels.2)
  · rintro ⟨hblock, hne⟩
    obtain ⟨a, b, hab⟩ := phaseOneSubword_pairBlock word hblock
    refine ⟨(a, b), ?_⟩
    have hp : (a, b) ≠ (x, y) := by
      intro hp
      cases hp
      exact hne hab
    have hmem : word ∈ d5PairBlock a.1 b.1 :=
      (mem_pairBlock_iff a b word).mpr ⟨hblock, hab⟩
    simpa [hp] using hmem

private theorem mem_pairCode_iff (x y : D5PhaseOne)
    (word : Word D5Alphabet) :
    word ∈ d5DistinguishedPairBlock x y ∪ d5OtherPairBlocks x y ↔
      IsPairBlock word := by
  classical
  rw [Set.mem_union]
  simp only [d5DistinguishedPairBlock, mem_pairBlock_iff,
    mem_otherPairBlocks_iff]
  constructor
  · rintro (⟨hblock, -⟩ | ⟨hblock, -⟩) <;> exact hblock
  · intro hblock
    by_cases hsub : d5PhaseOneSubword word = [x, y]
    · exact Or.inl ⟨hblock, hsub⟩
    · exact Or.inr ⟨hblock, hsub⟩

private theorem pairLanguages_disjoint (x y : D5PhaseOne) :
    Disjoint (d5DistinguishedPairBlock x y) (d5OtherPairBlocks x y) := by
  rw [Set.disjoint_left]
  intro word hdist hother
  exact (mem_otherPairBlocks_iff x y word).mp hother |>.2
    ((mem_pairBlock_iff x y word).mp hdist).2

private theorem pairCode_unique (x y : D5PhaseOne) :
    ∀ left right : List (Word D5Alphabet),
      Factorizes (d5DistinguishedPairBlock x y ∪ d5OtherPairBlocks x y)
          left left.flatten →
      Factorizes (d5DistinguishedPairBlock x y ∪ d5OtherPairBlocks x y)
          right right.flatten →
      left.flatten = right.flatten → left = right := by
  intro left right hleft hright hflat
  have hleftFactor : IsPairFactorization left [] left.flatten := by
    refine ⟨?_, (by intro a ha; simp at ha), by simp⟩
    intro piece hpiece
    exact (mem_pairCode_iff x y piece).mp (hleft.1 piece hpiece)
  have hrightFactor : IsPairFactorization right [] left.flatten := by
    refine ⟨?_, (by intro a ha; simp at ha), ?_⟩
    · intro piece hpiece
      exact (mem_pairCode_iff x y piece).mp (hright.1 piece hpiece)
    · simpa using hflat.symm
  exact (pairFactorization_unique left right [] [] left.flatten
    hleftFactor hrightFactor).1

private theorem countIn_distinguished_eq_pairBlockCount
    (x y : D5PhaseOne) (pieces : List (Word D5Alphabet))
    (hpieces : ∀ piece ∈ pieces, IsPairBlock piece) :
    countIn (d5DistinguishedPairBlock x y) pieces =
      pairBlockCount x y pieces := by
  classical
  induction pieces with
  | nil => simp [countIn, pairBlockCount]
  | cons piece pieces ih =>
      have hpiece := hpieces piece (by simp)
      have htail : ∀ other ∈ pieces, IsPairBlock other := by
        intro other hother
        exact hpieces other (by simp [hother])
      have hmem : piece ∈ d5DistinguishedPairBlock x y ↔
          d5PhaseOneSubword piece = [x, y] := by
        simpa [d5DistinguishedPairBlock, hpiece] using
          (mem_pairBlock_iff x y piece)
      have hcountCons :
          countIn (d5DistinguishedPairBlock x y) (piece :: pieces) =
            (if piece ∈ d5DistinguishedPairBlock x y then 1 else 0) +
              countIn (d5DistinguishedPairBlock x y) pieces := by
        unfold countIn
        rw [List.countP_cons]
        by_cases hm : piece ∈ d5DistinguishedPairBlock x y <;>
          simp [hm, Nat.add_comm]
      rw [hcountCons, ih htail]
      by_cases hm : piece ∈ d5DistinguishedPairBlock x y
      · have hs := hmem.mp hm
        simp [pairBlockCount, hm, hs]
      · have hs : d5PhaseOneSubword piece ≠ [x, y] :=
          fun hs => hm (hmem.mpr hs)
        simp [pairBlockCount, hm, hs]

private theorem phase_sum_zero_of_pairFactorization
    (pieces : List (Word D5Alphabet)) (suffix word : Word D5Alphabet)
    (hfactor : IsPairFactorization pieces suffix word) :
    (word.map d5Phase).sum = 0 := by
  apply (d5PhaseOneSubword_even_iff_phase_sum_zero word).mp
  rw [← hfactor.2.2, phaseOneSubword_append,
    phaseOneSubword_eq_nil_of_neutral suffix hfactor.2.1]
  simp only [List.append_nil]
  have heven : ∀ blocks : List (Word D5Alphabet),
      (∀ piece ∈ blocks, IsPairBlock piece) →
        (d5PhaseOneSubword blocks.flatten).length % 2 = 0 := by
    intro blocks hblocks
    induction blocks with
    | nil => simp [d5PhaseOneSubword]
    | cons piece blocks ih =>
        have hpiece := hblocks piece (by simp)
        have htail : ∀ other ∈ blocks, IsPairBlock other := by
          intro other hother
          exact hblocks other (by simp [hother])
        obtain ⟨a, b, hab⟩ := phaseOneSubword_pairBlock piece hpiece
        rw [List.flatten_cons, phaseOneSubword_append, hab]
        simp only [List.length_append, List.length_cons, List.length_nil]
        have iht := ih htail
        omega
  exact heven pieces hfactor.1

/-- Exact phase-zero, distinguished-pair residue-zero language. -/
theorem d5PairResidue_zero_eq_formula (x y : D5PhaseOne) :
    d5PairResidueZero x y =
      Language.concat
        (TransferCore.formula (d5DistinguishedPairBlock x y)
          (d5OtherPairBlocks x y) 5)
        d5Neutral := by
  classical
  ext word
  rw [Language.mem_concat_iff]
  change ((word.map d5Phase).sum = 0 ∧
      pairCountOf x y (d5PhaseOneSubword word) % 5 = 0) ↔ _
  constructor
  · rintro ⟨hphase, hcount⟩
    obtain ⟨pieces, suffix, hfactor⟩ := exists_pairFactorization word hphase
    refine ⟨pieces.flatten, ?_, suffix, hfactor.2.1, hfactor.2.2⟩
    rw [mem_formula_partition_iff
      (d5DistinguishedPairBlock x y) (d5OtherPairBlocks x y)
      5 (by omega) (pairLanguages_disjoint x y) (pairCode_unique x y)]
    refine ⟨pieces, ⟨?_, rfl⟩, ?_⟩
    · intro piece hpiece
      exact (mem_pairCode_iff x y piece).mpr (hfactor.1 piece hpiece)
    · rw [countIn_distinguished_eq_pairBlockCount x y pieces hfactor.1,
        pairBlockCount_eq_pairCountOf x y pieces suffix word hfactor]
      exact hcount
  · rintro ⟨pre, hpre, suffix, hsuffix, hword⟩
    rw [mem_formula_partition_iff
      (d5DistinguishedPairBlock x y) (d5OtherPairBlocks x y)
      5 (by omega) (pairLanguages_disjoint x y) (pairCode_unique x y)] at hpre
    obtain ⟨pieces, hpieces, hcount⟩ := hpre
    have hblocks : ∀ piece ∈ pieces, IsPairBlock piece := by
      intro piece hpiece
      exact (mem_pairCode_iff x y piece).mp (hpieces.1 piece hpiece)
    have hfactor : IsPairFactorization pieces suffix word := by
      refine ⟨hblocks, hsuffix, ?_⟩
      rw [hpieces.2]
      exact hword
    refine ⟨phase_sum_zero_of_pairFactorization pieces suffix word hfactor, ?_⟩
    rw [← pairBlockCount_eq_pairCountOf x y pieces suffix word hfactor,
      ← countIn_distinguished_eq_pairBlockCount x y pieces hblocks]
    exact hcount

theorem hasHeightAtMost_d5PairResidue_zero (x y : D5PhaseOne)
    (hne : x.1 ≠ y.1) :
    HasHeightAtMost (d5PairResidueZero x y) 1 := by
  have hformula := hasHeightAtMost_d5PairFormula x y hne
  exact (hformula.concat (d5Neutral_starFree.mono (by omega))).congr
    (d5PairResidue_zero_eq_formula x y).symm

end D5FlipPairTransfer

end GSH
