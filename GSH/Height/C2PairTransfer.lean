import GSH.Height.C2PairHeight
import GSH.Height.C2SelfLoop
import GSH.Height.TransferModulusSemantics

/-!
# Source-zero residues for canonical phase-one pairs

The final neutral suffix is retained explicitly.  Thus the language below
includes the phase-zero/even condition rather than silently discarding it.
-/

set_option autoImplicit false

namespace GSH

namespace C2PairTransfer

open ArrowCounting
open TransferSemantics

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]
variable (phase : α → ZMod 2)

/-- Phase-one letters for the chosen quotient map. -/
abbrev PhaseOne (phase : α → ZMod 2) := {a : α // phase a = 1}

/-- Fixed consecutive-pair count on the filtered phase-one word. -/
def pairCountOf {β : Type*} [DecidableEq β] (x y : β) : Word β → Nat
  | a :: b :: word =>
      (if a = x ∧ b = y then 1 else 0) + pairCountOf x y word
  | _ => 0

/-- Words containing only phase-zero letters. -/
def neutral : Language α := {word | ∀ a ∈ word, phase a = 0}

/-- The distinguished canonical pair block. -/
def distinguishedPairBlock (x y : PhaseOne phase) : Language α :=
  C2PairHeight.pairBlock phase x.1 y.1

/-- All canonical pair blocks except the distinguished one. -/
def otherPairBlocks (x y : PhaseOne phase) : Language α :=
  ⋃ pair : PhaseOne phase × PhaseOne phase,
    if pair = (x, y) then ∅
    else C2PairHeight.pairBlock phase pair.1.1 pair.2.1

private theorem otherPairBlocks_starFree (x y : PhaseOne phase) :
    IsStarFree (otherPairBlocks phase x y) := by
  classical
  unfold otherPairBlocks
  apply HasHeightAtMost.iUnion
  intro pair
  by_cases hp : pair = (x, y)
  · simpa [hp] using (HasHeightAtMost.empty (α := α) (n := 0))
  · simp only [hp, if_false]
    exact C2PairHeight.isStarFree_pairBlock phase pair.1.1 pair.2.1

/-- The PST pair formula has height at most one. -/
theorem hasHeightAtMost_pairFormula (x y : PhaseOne phase)
    (hne : x.1 ≠ y.1) (modulus : Nat) :
    HasHeightAtMost
      (TransferCore.formula (distinguishedPairBlock phase x y)
        (otherPairBlocks phase x y) modulus) 1 := by
  apply TransferCore.hasHeightAtMost_formula
  · exact C2PairHeight.isStarFree_pairBlock phase x.1 y.1
  · exact otherPairBlocks_starFree phase x y
  · exact C2PairHeight.isStarFree_pairBlockStar phase x.1 y.1 x.2 y.2 hne

/-- Delete phase-zero letters and retain phase-one `C₂` letters. -/
def phaseOneSubword : Word α → Word (PhaseOne phase)
  | [] => []
  | p :: word =>
      if hp : phase p = 1 then
        ⟨p, hp⟩ :: phaseOneSubword word
      else phaseOneSubword word

private theorem phase_eq_zero_of_ne_one (p : α)
    (hp : phase p ≠ 1) : phase p = 0 := by
  have hval : (phase p).val = 0 ∨ (phase p).val = 1 := by
    have := ZMod.val_lt (phase p)
    omega
  rcases hval with hval | hval
  · apply ZMod.val_injective 2
    simpa [hval]
  · exfalso
    apply hp
    apply ZMod.val_injective 2
    simpa [hval, ZMod.val_one]

theorem phaseOneSubword_length_cast (word : Word α) :
    ((phaseOneSubword phase word).length : ZMod 2) =
      (word.map phase).sum := by
  induction word with
  | nil => simp [phaseOneSubword]
  | cons p word ih =>
      by_cases hp : phase p = 1
      · simp [phaseOneSubword, hp, ih, add_comm]
      · have hp0 := phase_eq_zero_of_ne_one phase p hp
        simp [phaseOneSubword, hp0, ih]

theorem phaseOneSubword_even_iff_phase_sum_zero
    (word : Word α) :
    (phaseOneSubword phase word).length % 2 = 0 ↔
      (word.map phase).sum = 0 := by
  rw [← phaseOneSubword_length_cast (phase := phase)]
  simpa [Nat.dvd_iff_mod_eq_zero] using
    (ZMod.natCast_eq_zero_iff (phaseOneSubword phase word).length 2).symm

abbrev IsNeutralWord (word : Word α) : Prop :=
  ∀ a ∈ word, phase a = 0

def IsPairBlock (word : Word α) : Prop :=
  ∃ leading x middle y,
    IsNeutralWord phase leading ∧ phase x = 1 ∧
      IsNeutralWord phase middle ∧ phase y = 1 ∧
        word = leading ++ x :: middle ++ [y]

def IsPairFactorization (pieces : List (Word α))
    (suffix word : Word α) : Prop :=
  (∀ piece ∈ pieces, IsPairBlock phase piece) ∧ IsNeutralWord phase suffix ∧
    pieces.flatten ++ suffix = word

private theorem phase_eq_zero_or_one (p : α) :
    phase p = 0 ∨ phase p = 1 := by
  by_cases hp : phase p = 1
  · exact Or.inr hp
  · exact Or.inl (phase_eq_zero_of_ne_one phase p hp)

private theorem run_neutral (start : ZMod 2) (word : Word α)
    (hword : IsNeutralWord phase word) :
    runFrom (c2Step phase) start word = start := by
  induction word generalizing start with
  | nil => rfl
  | cons a word ih =>
      have ha : phase a = 0 := hword a (by simp)
      have hw : IsNeutralWord phase word := by
        intro b hb
        exact hword b (by simp [hb])
      simp [runFrom_cons, c2Step, ha, ih start hw]

private theorem exists_first_flip (word : Word α)
    (h : ∃ a ∈ word, phase a = 1) :
    ∃ leading x tail, word = leading ++ x :: tail ∧
      IsNeutralWord phase leading ∧ phase x = 1 := by
  induction word with
  | nil => simp at h
  | cons a word ih =>
      by_cases ha : phase a = 1
      · exact ⟨[], a, word, rfl, (by intro b hb; simp at hb), ha⟩
      · have ha0 : phase a = 0 :=
          (phase_eq_zero_or_one phase a).resolve_right ha
        have htail : ∃ b ∈ word, phase b = 1 := by
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
    ∀ n : Nat, ∀ word : Word α, word.length = n →
      runFrom (c2Step phase) 0 word = 0 →
      ∃ pieces suffix, IsPairFactorization phase pieces suffix word := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih word hlength hrun
  by_cases hcontains : ∃ a ∈ word, phase a = 1
  · obtain ⟨leading, x, rest, rfl, hleading, hx⟩ :=
      exists_first_flip phase word hcontains
    have hrunRest : runFrom (c2Step phase) 1 rest = 0 := by
      rw [runFrom_append] at hrun
      simp [run_neutral phase 0 leading hleading, runFrom_cons, c2Step, hx] at hrun
      exact hrun
    have hcontainsRest : ∃ a ∈ rest, phase a = 1 := by
      by_contra hnone
      have hneutral : IsNeutralWord phase rest := by
        intro a ha
        rcases phase_eq_zero_or_one phase a with ha0 | ha1
        · exact ha0
        · exact False.elim (hnone ⟨a, ha, ha1⟩)
      have hone := run_neutral phase 1 rest hneutral
      rw [hrunRest] at hone
      exact zero_ne_one hone
    obtain ⟨middle, y, tail, rfl, hmiddle, hy⟩ :=
      exists_first_flip phase rest hcontainsRest
    have hrunTail : runFrom (c2Step phase) 0 tail = 0 := by
      rw [runFrom_append] at hrunRest
      simp [run_neutral phase 1 middle hmiddle, runFrom_cons, c2Step, hy] at hrunRest
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
  · have hneutral : IsNeutralWord phase word := by
      intro a ha
      rcases phase_eq_zero_or_one phase a with ha0 | ha1
      · exact ha0
      · exact False.elim (hcontains ⟨a, ha, ha1⟩)
    exact ⟨[], word, by simp, hneutral, rfl⟩

theorem exists_pairFactorization (word : Word α)
    (hphase : (word.map phase).sum = 0) :
    ∃ pieces suffix, IsPairFactorization phase pieces suffix word := by
  have hrun : runFrom (c2Step phase) 0 word = 0 := by
    simpa [c2RunFrom, c2Step] using
      (c2RunFrom_eq phase 0 word).trans (by simp [hphase])
  exact exists_pairFactorization_of_length phase word.length word rfl hrun

local instance : BEq (PhaseOne phase) := instBEqOfDecidableEq

theorem phaseOneSubword_append (left right : Word α) :
    phaseOneSubword phase (left ++ right) =
      phaseOneSubword phase left ++ phaseOneSubword phase right := by
  induction left with
  | nil => rfl
  | cons a left ih =>
      by_cases ha : phase a = 1 <;>
        simp [phaseOneSubword, ha, ih]

theorem phaseOneSubword_eq_nil_of_neutral (word : Word α)
    (hword : IsNeutralWord phase word) : phaseOneSubword phase word = [] := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      have ha : phase a = 0 := hword a (by simp)
      have htail : IsNeutralWord phase word := by
        intro b hb
        exact hword b (by simp [hb])
      simp [phaseOneSubword, ha, ih htail]

theorem phaseOneSubword_pairBlock (piece : Word α)
    (hpiece : IsPairBlock phase piece) :
    ∃ x y : PhaseOne phase, phaseOneSubword phase piece = [x, y] := by
  rcases hpiece with ⟨leading, x, middle, y, hleading, hx,
    hmiddle, hy, rfl⟩
  refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ?_⟩
  simp [phaseOneSubword, hx, hy, phaseOneSubword_append,
    phaseOneSubword_eq_nil_of_neutral (phase := phase) leading hleading,
    phaseOneSubword_eq_nil_of_neutral (phase := phase) middle hmiddle]

def pairBlockCount (x y : PhaseOne phase) : List (Word α) → Nat
  | [] => 0
  | piece :: pieces =>
      (if phaseOneSubword phase piece = [x, y] then 1 else 0) +
        pairBlockCount x y pieces

private theorem pairBlockCount_eq_pairCountOf_flatten
    (x y : PhaseOne phase) (pieces : List (Word α))
    (hpieces : ∀ piece ∈ pieces, IsPairBlock phase piece) :
    pairBlockCount phase x y pieces =
      pairCountOf x y (phaseOneSubword phase pieces.flatten) := by
  induction pieces with
  | nil => simp [pairBlockCount, pairCountOf, phaseOneSubword]
  | cons piece pieces ih =>
      have hpiece := hpieces piece (by simp)
      have hrest : ∀ p ∈ pieces, IsPairBlock phase p := by
        intro p hp
        exact hpieces p (by simp [hp])
      obtain ⟨a, b, hab⟩ :=
        phaseOneSubword_pairBlock (phase := phase) piece hpiece
      rw [List.flatten_cons, phaseOneSubword_append, hab]
      by_cases hax : a = x <;> by_cases hby : b = y <;>
        simp [pairBlockCount, pairCountOf, hab, hax, hby, ih hrest]

theorem pairBlockCount_eq_pairCountOf (x y : PhaseOne phase)
    (pieces : List (Word α)) (suffix word : Word α)
    (hfactor : IsPairFactorization phase pieces suffix word) :
    pairBlockCount phase x y pieces =
      pairCountOf x y (phaseOneSubword phase word) := by
  have hsuffix := phaseOneSubword_eq_nil_of_neutral
    (phase := phase) suffix hfactor.2.1
  calc
    pairBlockCount phase x y pieces =
        pairCountOf x y (phaseOneSubword phase pieces.flatten) :=
      pairBlockCount_eq_pairCountOf_flatten phase x y pieces hfactor.1
    _ = pairCountOf x y
        (phaseOneSubword phase (pieces.flatten ++ suffix)) := by
      rw [phaseOneSubword_append, hsuffix]
      simp
    _ = pairCountOf x y (phaseOneSubword phase word) := by rw [hfactor.2.2]

private theorem map_neutral (word : Word α)
    (hword : IsNeutralWord phase word) :
    word.map phase = List.replicate word.length 0 := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      have ha : phase a = 0 := hword a (by simp)
      have htail : IsNeutralWord phase word := by
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

theorem pairBlock_eq_of_prefix (left right suffix : Word α)
    (hleft : IsPairBlock phase left) (hright : IsPairBlock phase right)
    (hprefix : right = left ++ suffix) : left = right := by
  rcases hleft with ⟨leading₁, x₁, middle₁, y₁, hl₁, hx₁,
    hm₁, hy₁, rfl⟩
  rcases hright with ⟨leading₂, x₂, middle₂, y₂, hl₂, hx₂,
    hm₂, hy₂, rfl⟩
  have hphase := congrArg (List.map phase) hprefix
  have hleadingLength : leading₂.length = leading₁.length := by
    apply zeros_before_one_unique leading₂.length leading₁.length
      (List.replicate middle₂.length 0 ++ [1])
      (List.replicate middle₁.length 0 ++ [1] ++ suffix.map phase)
    simpa [map_neutral (phase := phase) leading₁ hl₁,
      map_neutral (phase := phase) leading₂ hl₂,
      map_neutral (phase := phase) middle₁ hm₁,
      map_neutral (phase := phase) middle₂ hm₂,
      hx₁, hx₂, hy₁, hy₂, List.append_assoc] using hphase
  have hphaseTail :
      List.replicate middle₂.length 0 ++ [1] =
        List.replicate middle₁.length 0 ++ [1] ++ suffix.map phase := by
    simpa [map_neutral (phase := phase) leading₁ hl₁,
      map_neutral (phase := phase) leading₂ hl₂,
      map_neutral (phase := phase) middle₁ hm₁,
      map_neutral (phase := phase) middle₂ hm₂,
      hx₁, hx₂, hy₁, hy₂, hleadingLength,
      List.append_assoc] using hphase
  have hmiddleLength : middle₂.length = middle₁.length := by
    apply zeros_before_one_unique middle₂.length middle₁.length []
      (suffix.map phase)
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
    (leftPieces rightPieces : List (Word α))
    (leftSuffix rightSuffix word : Word α)
    (hleft : IsPairFactorization phase leftPieces leftSuffix word)
    (hright : IsPairFactorization phase rightPieces rightSuffix word) :
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
            · exact pairBlock_eq_of_prefix phase piece piece' suffix hp hp' hprefix
            · exact (pairBlock_eq_of_prefix phase piece' piece suffix hp' hp hprefix).symm
          subst piece'
          have htailFlat : pieces.flatten ++ leftSuffix =
              pieces'.flatten ++ rightSuffix := by simpa using hflat
          have hleftTail : IsPairFactorization phase pieces leftSuffix
              (pieces.flatten ++ leftSuffix) :=
            ⟨(by intro p hm; exact hleft.1 p (by simp [hm])), hleft.2.1, rfl⟩
          have hrightTail : IsPairFactorization phase pieces' rightSuffix
              (pieces.flatten ++ leftSuffix) :=
            ⟨(by intro p hm; exact hright.1 p (by simp [hm])),
              hright.2.1, htailFlat.symm⟩
          obtain ⟨hpieces, hsuffix⟩ :=
            ih pieces' (pieces.flatten ++ leftSuffix) hleftTail hrightTail
          exact ⟨congrArg (List.cons piece) hpieces, hsuffix⟩

def pairResidueZero (x y : PhaseOne phase) (modulus : Nat) : Language α :=
  {word | (word.map phase).sum = 0 ∧
    pairCountOf x y (phaseOneSubword phase word) % modulus = 0}

private theorem mem_pairBlock_iff (x y : PhaseOne phase)
    (word : Word α) :
    word ∈ C2PairHeight.pairBlock phase x.1 y.1 ↔
      IsPairBlock phase word ∧ phaseOneSubword phase word = [x, y] := by
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
    · have hleading' : IsNeutralWord phase leading := by
        simpa [C2SelfLoopHeight.neutralWordsR] using hleading
      have hmiddle' : IsNeutralWord phase middle := by
        simpa [C2SelfLoopHeight.neutralWordsR] using hmiddle
      exact ⟨leading, x.1, middle, y.1, hleading', x.2,
        hmiddle', y.2, by simp⟩
    · have hleading' : IsNeutralWord phase leading := by
        simpa [C2SelfLoopHeight.neutralWordsR] using hleading
      have hmiddle' : IsNeutralWord phase middle := by
        simpa [C2SelfLoopHeight.neutralWordsR] using hmiddle
      simp [phaseOneSubword, x.2, y.2, phaseOneSubword_append,
        phaseOneSubword_eq_nil_of_neutral (phase := phase) leading hleading',
        phaseOneSubword_eq_nil_of_neutral (phase := phase) middle hmiddle']
  · rintro ⟨hblock, hsubword⟩
    rcases hblock with ⟨leading, a, middle, b, hleading, ha,
      hmiddle, hb, rfl⟩
    have hlabels : [⟨a, ha⟩, ⟨b, hb⟩] = [x, y] := by
      simpa [phaseOneSubword, ha, hb, phaseOneSubword_append,
        phaseOneSubword_eq_nil_of_neutral (phase := phase) leading hleading,
        phaseOneSubword_eq_nil_of_neutral (phase := phase) middle hmiddle] using hsubword
    simp at hlabels
    have hax : a = x.1 := congrArg Subtype.val hlabels.1
    have hby : b = y.1 := congrArg Subtype.val hlabels.2
    subst a
    subst b
    have hleading' : leading ∈
        GRegex.denote (C2SelfLoopHeight.neutralWordsR phase) := by
      simpa [C2SelfLoopHeight.neutralWordsR] using hleading
    have hmiddle' : middle ∈
        GRegex.denote (C2SelfLoopHeight.neutralWordsR phase) := by
      simpa [C2SelfLoopHeight.neutralWordsR] using hmiddle
    refine ⟨leading, hleading', [x.1] ++ middle ++ [y.1], ?_, ?_⟩
    · refine ⟨[x.1], rfl, middle ++ [y.1], ?_, rfl⟩
      exact ⟨middle, hmiddle', [y.1], rfl, rfl⟩
    · simp [List.append_assoc]

private theorem mem_otherPairBlocks_iff (x y : PhaseOne phase)
    (word : Word α) :
    word ∈ otherPairBlocks phase x y ↔
      IsPairBlock phase word ∧ phaseOneSubword phase word ≠ [x, y] := by
  classical
  simp only [otherPairBlocks, Set.mem_iUnion]
  constructor
  · rintro ⟨pair, hpair⟩
    by_cases hp : pair = (x, y)
    · rw [hp, if_pos rfl] at hpair
      simp at hpair
    · have hmem : word ∈ C2PairHeight.pairBlock phase pair.1.1 pair.2.1 := by
        simpa [hp] using hpair
      have hcode := (mem_pairBlock_iff phase pair.1 pair.2 word).mp hmem
      refine ⟨hcode.1, ?_⟩
      intro heq
      have hlabels : [pair.1, pair.2] = [x, y] := hcode.2.symm.trans heq
      simp at hlabels
      exact hp (Prod.ext hlabels.1 hlabels.2)
  · rintro ⟨hblock, hne⟩
    obtain ⟨a, b, hab⟩ :=
      phaseOneSubword_pairBlock (phase := phase) word hblock
    refine ⟨(a, b), ?_⟩
    have hp : (a, b) ≠ (x, y) := by
      intro hp
      cases hp
      exact hne hab
    have hmem : word ∈ C2PairHeight.pairBlock phase a.1 b.1 :=
      (mem_pairBlock_iff phase a b word).mpr ⟨hblock, hab⟩
    simpa [hp] using hmem

private theorem mem_pairCode_iff (x y : PhaseOne phase)
    (word : Word α) :
    word ∈ distinguishedPairBlock phase x y ∪ otherPairBlocks phase x y ↔
      IsPairBlock phase word := by
  classical
  rw [Set.mem_union]
  simp only [distinguishedPairBlock, mem_pairBlock_iff,
    mem_otherPairBlocks_iff]
  constructor
  · rintro (⟨hblock, -⟩ | ⟨hblock, -⟩) <;> exact hblock
  · intro hblock
    by_cases hsub : phaseOneSubword phase word = [x, y]
    · exact Or.inl ⟨hblock, hsub⟩
    · exact Or.inr ⟨hblock, hsub⟩

private theorem pairLanguages_disjoint (x y : PhaseOne phase) :
    Disjoint (distinguishedPairBlock phase x y) (otherPairBlocks phase x y) := by
  rw [Set.disjoint_left]
  intro word hdist hother
  exact (mem_otherPairBlocks_iff phase x y word).mp hother |>.2
    ((mem_pairBlock_iff phase x y word).mp hdist).2

private theorem pairCode_unique (x y : PhaseOne phase) :
    ∀ left right : List (Word α),
      Factorizes (distinguishedPairBlock phase x y ∪ otherPairBlocks phase x y)
          left left.flatten →
      Factorizes (distinguishedPairBlock phase x y ∪ otherPairBlocks phase x y)
          right right.flatten →
      left.flatten = right.flatten → left = right := by
  intro left right hleft hright hflat
  have hleftFactor : IsPairFactorization phase left [] left.flatten := by
    refine ⟨?_, (by intro a ha; simp at ha), by simp⟩
    intro piece hpiece
    exact (mem_pairCode_iff phase x y piece).mp (hleft.1 piece hpiece)
  have hrightFactor : IsPairFactorization phase right [] left.flatten := by
    refine ⟨?_, (by intro a ha; simp at ha), ?_⟩
    · intro piece hpiece
      exact (mem_pairCode_iff phase x y piece).mp (hright.1 piece hpiece)
    · simpa using hflat.symm
  exact (pairFactorization_unique phase left right [] [] left.flatten
    hleftFactor hrightFactor).1

private theorem countIn_distinguished_eq_pairBlockCount
    (x y : PhaseOne phase) (pieces : List (Word α))
    (hpieces : ∀ piece ∈ pieces, IsPairBlock phase piece) :
    countIn (distinguishedPairBlock phase x y) pieces =
      pairBlockCount phase x y pieces := by
  classical
  induction pieces with
  | nil => simp [countIn, pairBlockCount]
  | cons piece pieces ih =>
      have hpiece := hpieces piece (by simp)
      have htail : ∀ other ∈ pieces, IsPairBlock phase other := by
        intro other hother
        exact hpieces other (by simp [hother])
      have hmem : piece ∈ distinguishedPairBlock phase x y ↔
          phaseOneSubword phase piece = [x, y] := by
        simpa [distinguishedPairBlock, hpiece] using
          (mem_pairBlock_iff phase x y piece)
      have hcountCons :
          countIn (distinguishedPairBlock phase x y) (piece :: pieces) =
            (if piece ∈ distinguishedPairBlock phase x y then 1 else 0) +
              countIn (distinguishedPairBlock phase x y) pieces := by
        unfold countIn
        rw [List.countP_cons]
        by_cases hm : piece ∈ distinguishedPairBlock phase x y <;>
          simp [hm, Nat.add_comm]
      rw [hcountCons, ih htail]
      by_cases hm : piece ∈ distinguishedPairBlock phase x y
      · have hs := hmem.mp hm
        simp [pairBlockCount, hm, hs, ih htail]
      · have hs : phaseOneSubword phase piece ≠ [x, y] :=
          fun hs => hm (hmem.mpr hs)
        simp [pairBlockCount, hm, hs, ih htail]

private theorem phase_sum_zero_of_pairFactorization
    (pieces : List (Word α)) (suffix word : Word α)
    (hfactor : IsPairFactorization phase pieces suffix word) :
    (word.map phase).sum = 0 := by
  apply (phaseOneSubword_even_iff_phase_sum_zero (phase := phase) word).mp
  rw [← hfactor.2.2, phaseOneSubword_append,
    phaseOneSubword_eq_nil_of_neutral (phase := phase) suffix hfactor.2.1]
  simp only [List.append_nil]
  have heven : ∀ blocks : List (Word α),
      (∀ piece ∈ blocks, IsPairBlock phase piece) →
        (phaseOneSubword phase blocks.flatten).length % 2 = 0 := by
    intro blocks hblocks
    induction blocks with
    | nil => simp [phaseOneSubword]
    | cons piece blocks ih =>
        have hpiece := hblocks piece (by simp)
        have htail : ∀ other ∈ blocks, IsPairBlock phase other := by
          intro other hother
          exact hblocks other (by simp [hother])
        obtain ⟨a, b, hab⟩ :=
          phaseOneSubword_pairBlock (phase := phase) piece hpiece
        rw [List.flatten_cons, phaseOneSubword_append, hab]
        simp only [List.length_append, List.length_cons, List.length_nil]
        have iht := ih htail
        omega
  exact heven pieces hfactor.1

/-- Exact phase-zero, distinguished-pair residue-zero language. -/
theorem pairResidue_zero_eq_formula (x y : PhaseOne phase)
    (modulus : Nat) (hmodulus : 0 < modulus) :
    pairResidueZero phase x y modulus =
      Language.concat
        (TransferCore.formula (distinguishedPairBlock phase x y)
          (otherPairBlocks phase x y) modulus)
        (neutral phase) := by
  classical
  ext word
  rw [Language.mem_concat_iff]
  change ((word.map phase).sum = 0 ∧
      pairCountOf x y (phaseOneSubword phase word) % modulus = 0) ↔ _
  constructor
  · rintro ⟨hphase, hcount⟩
    obtain ⟨pieces, suffix, hfactor⟩ := exists_pairFactorization phase word hphase
    refine ⟨pieces.flatten, ?_, suffix, hfactor.2.1, hfactor.2.2⟩
    rw [mem_formula_partition_iff
      (distinguishedPairBlock phase x y) (otherPairBlocks phase x y)
      modulus hmodulus (pairLanguages_disjoint phase x y) (pairCode_unique phase x y)]
    refine ⟨pieces, ⟨?_, rfl⟩, ?_⟩
    · intro piece hpiece
      exact (mem_pairCode_iff phase x y piece).mpr (hfactor.1 piece hpiece)
    · rw [countIn_distinguished_eq_pairBlockCount phase x y pieces hfactor.1,
        pairBlockCount_eq_pairCountOf phase x y pieces suffix word hfactor]
      exact hcount
  · rintro ⟨pre, hpre, suffix, hsuffix, hword⟩
    rw [mem_formula_partition_iff
      (distinguishedPairBlock phase x y) (otherPairBlocks phase x y)
      modulus hmodulus (pairLanguages_disjoint phase x y) (pairCode_unique phase x y)] at hpre
    obtain ⟨pieces, hpieces, hcount⟩ := hpre
    have hblocks : ∀ piece ∈ pieces, IsPairBlock phase piece := by
      intro piece hpiece
      exact (mem_pairCode_iff phase x y piece).mp (hpieces.1 piece hpiece)
    have hfactor : IsPairFactorization phase pieces suffix word := by
      refine ⟨hblocks, hsuffix, ?_⟩
      rw [hpieces.2]
      exact hword
    refine ⟨phase_sum_zero_of_pairFactorization phase pieces suffix word hfactor, ?_⟩
    rw [← pairBlockCount_eq_pairCountOf phase x y pieces suffix word hfactor,
      ← countIn_distinguished_eq_pairBlockCount phase x y pieces hblocks]
    exact hcount

theorem hasHeightAtMost_pairResidue_zero (x y : PhaseOne phase)
    (hne : x.1 ≠ y.1) (modulus : Nat) (hmodulus : 0 < modulus) :
    HasHeightAtMost (pairResidueZero phase x y modulus) 1 := by
  have hformula := hasHeightAtMost_pairFormula phase x y hne modulus
  have hneutral : IsStarFree (neutral phase) := by
    refine ⟨C2SelfLoopHeight.neutralWordsR phase, ?_, ?_⟩
    · ext word
      simp [neutral, C2SelfLoopHeight.neutralWordsR]
    · simp [C2SelfLoopHeight.neutralWordsR]
  exact (hformula.concat (hneutral.mono (by omega))).congr
    (pairResidue_zero_eq_formula phase x y modulus hmodulus).symm

/-! ## All residues by prefix shifts -/

/-- Even-phase words with a prescribed fixed-pair residue. -/
def pairResidue (x y : PhaseOne phase) (modulus residue : Nat) : Language α :=
  {word | (word.map phase).sum = 0 ∧
    pairCountOf x y (phaseOneSubword phase word) % modulus = residue}

/-- A prefix consisting of `amount` copies of the distinguished pair. -/
def pairPrefix (x y : PhaseOne phase) (amount : Nat) : Word α :=
  (List.replicate amount [x.1, y.1]).flatten

private theorem phaseOneSubword_pairPrefix (x y : PhaseOne phase)
    (amount : Nat) :
    phaseOneSubword phase (pairPrefix phase x y amount) =
      (List.replicate amount [x, y]).flatten := by
  induction amount with
  | zero => rfl
  | succ amount ih =>
      have hprefix : pairPrefix phase x y (amount + 1) =
          [x.1, y.1] ++ pairPrefix phase x y amount := by
        simp [pairPrefix, List.replicate_succ]
      rw [hprefix, phaseOneSubword_append, ih]
      simp [phaseOneSubword, x.2, y.2, List.replicate_succ]

private theorem phase_sum_pairPrefix (x y : PhaseOne phase)
    (amount : Nat) :
    ((pairPrefix phase x y amount).map phase).sum = 0 := by
  induction amount with
  | zero => rfl
  | succ amount ih =>
      have hprefix : pairPrefix phase x y (amount + 1) =
          [x.1, y.1] ++ pairPrefix phase x y amount := by
        simp [pairPrefix, List.replicate_succ]
      rw [hprefix, List.map_append, List.sum_append, ih]
      simpa [x.2, y.2] using (CharTwo.add_self_eq_zero (1 : ZMod 2))

private theorem pairCountOf_replicate_pairs_append
    (x y : PhaseOne phase) (amount : Nat) (tail : Word (PhaseOne phase)) :
    pairCountOf x y
        ((List.replicate amount [x, y]).flatten ++ tail) =
      amount + pairCountOf x y tail := by
  induction amount with
  | zero => simp
  | succ amount ih =>
      rw [List.replicate_succ, List.flatten_cons]
      simp [pairCountOf, ih]
      omega

private theorem pairCount_pairPrefix_append
    (x y : PhaseOne phase) (amount : Nat) (word : Word α) :
    pairCountOf x y
        (phaseOneSubword phase (pairPrefix phase x y amount ++ word)) =
      amount + pairCountOf x y (phaseOneSubword phase word) := by
  rw [phaseOneSubword_append,
    phaseOneSubword_pairPrefix phase x y amount,
    pairCountOf_replicate_pairs_append phase x y amount]

/-- Every distinct phase-one pair residue has height at most one. -/
theorem hasHeightAtMost_pairResidue (x y : PhaseOne phase)
    (hne : x.1 ≠ y.1) (modulus : Nat) (hmodulus : 0 < modulus)
    (residue : Fin modulus) :
    HasHeightAtMost (pairResidue phase x y modulus residue.1) 1 := by
  let amount := modulus - residue.1
  let pre := pairPrefix phase x y amount
  have hzero := hasHeightAtMost_pairResidue_zero
    phase x y hne modulus hmodulus
  have hquot := C2SelfLoop.HasHeightAtMost.leftQuotientWord hzero pre
  exact hquot.congr (by
    ext word
    simp only [C2SelfLoop.mem_leftQuotientWord, pairResidueZero,
      pairResidue, Set.mem_setOf_eq]
    rw [List.map_append, List.sum_append,
      phase_sum_pairPrefix phase x y amount, zero_add,
      pairCount_pairPrefix_append phase x y amount word]
    exact and_congr_right (fun _ =>
      C2SelfLoop.shifted_zero_iff modulus residue.1 amount
        (pairCountOf x y (phaseOneSubword phase word))
        hmodulus residue.2 rfl))

end C2PairTransfer

end GSH
