import GSH.Height.A4NonmoverCut
import GSH.Height.TransferSemantics

/-!
# Base-cut parity for `A₄`

For a fixed target phase, words are cut whenever the phase arrives at that
target.  The resulting unique first-return decomposition gives
`O (X X)* V` for odd cut count and `V₀ ∪ O X (X X)* V` for even cut count.
-/

set_option autoImplicit false

namespace GSH

/-- Phase reached after reading a word. -/
def a4PhaseRunFrom : ZMod 3 → Word A4 → ZMod 3
  | phase, [] => phase
  | phase, g :: word => a4PhaseRunFrom (phase + a4PhaseValue g) word

@[simp] theorem a4PhaseRunFrom_append (start : ZMod 3) (u v : Word A4) :
    a4PhaseRunFrom start (u ++ v) = a4PhaseRunFrom (a4PhaseRunFrom start u) v := by
  induction u generalizing start with
  | nil => simp [a4PhaseRunFrom]
  | cons g u ih => simpa [a4PhaseRunFrom] using ih (start + a4PhaseValue g)

theorem a4BaseCutCountFrom_append (start target : ZMod 3) (u v : Word A4) :
    a4BaseCutCountFrom start target (u ++ v) =
      a4BaseCutCountFrom start target u +
        a4BaseCutCountFrom (a4PhaseRunFrom start u) target v := by
  induction u generalizing start with
  | nil => simp [a4BaseCutCountFrom, a4PhaseRunFrom]
  | cons g u ih =>
      simp only [List.cons_append, a4BaseCutCountFrom, a4PhaseRunFrom]
      rw [ih]
      omega

/-- Initial block ending at the first cut. -/
def a4BaseCutInitialBlock (target : ZMod 3) : Language A4 :=
  {word | a4BaseCutCountFrom 0 target word = 1 ∧
    a4PhaseRunFrom 0 word = target}

/-- Return block from the target to its next cut. -/
def a4BaseCutReturnBlock (target : ZMod 3) : Language A4 :=
  {word | a4BaseCutCountFrom target target word = 1 ∧
    a4PhaseRunFrom target word = target}

/-- Tail after the final cut. -/
def a4BaseCutTail (target : ZMod 3) : Language A4 :=
  {word | a4BaseCutCountFrom target target word = 0}

/-- A whole word with no cut. -/
def a4BaseCutInitialTail (target : ZMod 3) : Language A4 :=
  {word | a4BaseCutCountFrom 0 target word = 0}

def a4BaseCutOdd (target : ZMod 3) : Language A4 :=
  {word | a4BaseCutCountFrom 0 target word % 2 = 1}

def a4BaseCutEven (target : ZMod 3) : Language A4 :=
  {word | a4BaseCutCountFrom 0 target word % 2 = 0}

def a4BaseCutOddFormula (target : ZMod 3) : Language A4 :=
  Language.concat (a4BaseCutInitialBlock target)
    (Language.concat
      (Language.star (Language.concat (a4BaseCutReturnBlock target)
        (a4BaseCutReturnBlock target)))
      (a4BaseCutTail target))

def a4BaseCutEvenFormula (target : ZMod 3) : Language A4 :=
  a4BaseCutInitialTail target ∪
    Language.concat (a4BaseCutInitialBlock target)
      (Language.concat (a4BaseCutReturnBlock target)
        (Language.concat
          (Language.star (Language.concat (a4BaseCutReturnBlock target)
            (a4BaseCutReturnBlock target)))
          (a4BaseCutTail target)))

/-- Either no cut occurs, or a nonempty first-cut block can be split off. -/
private theorem a4_noCut_or_firstCut (start target : ZMod 3) (word : Word A4) :
    a4BaseCutCountFrom start target word = 0 ∨
      ∃ first rest,
        a4BaseCutCountFrom start target first = 1 ∧
        a4PhaseRunFrom start first = target ∧ first ++ rest = word := by
  induction word generalizing start with
  | nil => exact Or.inl rfl
  | cons g word ih =>
      let next := start + a4PhaseValue g
      by_cases hnext : next = target
      · exact Or.inr ⟨[g], word, by simp [a4BaseCutCountFrom,
          next, hnext], by simp [a4PhaseRunFrom, next, hnext], rfl⟩
      · rcases ih next with hzero | ⟨first, rest, hcount, hrun, hsplit⟩
        · left
          simp [a4BaseCutCountFrom, next, hnext, hzero]
        · right
          refine ⟨g :: first, rest, ?_, ?_, ?_⟩
          · simpa [a4BaseCutCountFrom, next, hnext] using hcount
          · simpa [a4PhaseRunFrom, next] using hrun
          · simp [hsplit]

private theorem a4_firstCut_nonempty {start target : ZMod 3} {word : Word A4}
    (h : a4BaseCutCountFrom start target word = 1) : word ≠ [] := by
  intro hw
  subst word
  simp [a4BaseCutCountFrom] at h

private theorem a4_returnPair_count_run (target : ZMod 3) {word : Word A4}
    (hword : word ∈ Language.concat (a4BaseCutReturnBlock target)
      (a4BaseCutReturnBlock target)) :
    a4BaseCutCountFrom target target word = 2 ∧
      a4PhaseRunFrom target word = target := by
  rcases hword with ⟨u, hu, v, hv, rfl⟩
  simp only [a4BaseCutReturnBlock, Set.mem_setOf_eq] at hu hv
  rw [a4BaseCutCountFrom_append, a4PhaseRunFrom_append, hu.2]
  exact ⟨by omega, hv.2⟩

private theorem a4_starPairs_count_run (target : ZMod 3) {word : Word A4}
    (hword : word ∈ Language.star (Language.concat
      (a4BaseCutReturnBlock target) (a4BaseCutReturnBlock target))) :
    a4BaseCutCountFrom target target word % 2 = 0 ∧
      a4PhaseRunFrom target word = target := by
  obtain ⟨pieces, hpieces⟩ :=
    (TransferSemantics.mem_star_iff_factorizes _ word).mp hword
  rcases hpieces with ⟨hall, rfl⟩
  induction pieces with
  | nil => simp [a4BaseCutCountFrom, a4PhaseRunFrom]
  | cons piece pieces ih =>
      have hp := a4_returnPair_count_run target (hall piece (by simp))
      have htail : ∀ other ∈ pieces,
          other ∈ Language.concat (a4BaseCutReturnBlock target)
            (a4BaseCutReturnBlock target) := by
        intro other hother
        exact hall other (by simp [hother])
      have hstarTail : pieces.flatten ∈ Language.star
          (Language.concat (a4BaseCutReturnBlock target)
            (a4BaseCutReturnBlock target)) :=
        (TransferSemantics.mem_star_iff_factorizes _ _).mpr
          ⟨pieces, ⟨htail, rfl⟩⟩
      have hi := ih htail hstarTail
      rw [List.flatten_cons, a4BaseCutCountFrom_append,
        a4PhaseRunFrom_append, hp.2]
      constructor
      · have hpcount := hp.1
        have hicount := hi.1
        omega
      · exact hi.2

private theorem a4_returnEven_formula (target : ZMod 3) (word : Word A4) :
    a4BaseCutCountFrom target target word % 2 = 0 ↔
      word ∈ Language.concat
        (Language.star (Language.concat (a4BaseCutReturnBlock target)
          (a4BaseCutReturnBlock target))) (a4BaseCutTail target) := by
  constructor
  · intro heven
    rcases a4_noCut_or_firstCut target target word with hzero |
          ⟨first, rest, hfirstCount, hfirstRun, hsplit⟩
    · exact ⟨[], ⟨0, by simp [Language.power, Language.epsilon]⟩,
        word, hzero, by simp⟩
    · have hrestOdd : a4BaseCutCountFrom target target rest % 2 = 1 := by
        rw [← hsplit, a4BaseCutCountFrom_append, hfirstRun] at heven
        omega
      rcases a4_noCut_or_firstCut target target rest with hrestZero |
            ⟨second, rest2, hsecondCount, hsecondRun, hsplit2⟩
      · omega
      · have hrest2Even : a4BaseCutCountFrom target target rest2 % 2 = 0 := by
          rw [← hsplit2, a4BaseCutCountFrom_append, hsecondRun] at hrestOdd
          omega
        have hfirstNe := a4_firstCut_nonempty hfirstCount
        have hsecondNe := a4_firstCut_nonempty hsecondCount
        have hlen : rest2.length < word.length := by
          rw [← hsplit, ← hsplit2, List.length_append, List.length_append]
          have hpos1 := List.length_pos_of_ne_nil hfirstNe
          have hpos2 := List.length_pos_of_ne_nil hsecondNe
          omega
        obtain ⟨starWord, hstar, tail, htail, hrest2⟩ :=
          (a4_returnEven_formula target rest2).mp hrest2Even
        have hpair : first ++ second ∈ Language.concat
              (a4BaseCutReturnBlock target) (a4BaseCutReturnBlock target) :=
          ⟨first, ⟨hfirstCount, hfirstRun⟩, second,
            ⟨hsecondCount, hsecondRun⟩, rfl⟩
        obtain ⟨pieces, hpieces⟩ :=
          (TransferSemantics.mem_star_iff_factorizes _ starWord).mp hstar
        have hstar' : (first ++ second) ++ starWord ∈ Language.star
              (Language.concat (a4BaseCutReturnBlock target)
                (a4BaseCutReturnBlock target)) :=
          (TransferSemantics.mem_star_iff_factorizes _ _).mpr
            ⟨(first ++ second) :: pieces,
              TransferSemantics.factorizes_cons hpair hpieces⟩
        exact ⟨(first ++ second) ++ starWord, hstar', tail, htail, by
          rw [← hsplit, ← hsplit2, ← hrest2]
          simp [List.append_assoc]⟩
  · rintro ⟨pairs, hpairs, tail, htail, rfl⟩
    have hp := a4_starPairs_count_run target hpairs
    simp only [a4BaseCutTail, Set.mem_setOf_eq] at htail
    rw [a4BaseCutCountFrom_append, hp.2]
    omega
termination_by word.length

theorem a4BaseCutOdd_eq_formula (target : ZMod 3) :
    a4BaseCutOdd target = a4BaseCutOddFormula target := by
  ext word
  simp only [a4BaseCutOdd, a4BaseCutOddFormula, Set.mem_setOf_eq]
  constructor
  · intro hodd
    rcases a4_noCut_or_firstCut 0 target word with hzero |
        ⟨first, rest, hcount, hrun, hsplit⟩
    · omega
    · have heven : a4BaseCutCountFrom target target rest % 2 = 0 := by
        rw [← hsplit, a4BaseCutCountFrom_append, hrun] at hodd
        omega
      exact ⟨first, ⟨hcount, hrun⟩, rest,
        (a4_returnEven_formula target rest).mp heven, hsplit⟩
  · rintro ⟨first, hfirst, rest, hrest, rfl⟩
    simp only [a4BaseCutInitialBlock, Set.mem_setOf_eq] at hfirst
    have heven := (a4_returnEven_formula target rest).mpr hrest
    rw [a4BaseCutCountFrom_append, hfirst.2]
    omega

theorem a4BaseCutEven_eq_formula (target : ZMod 3) :
    a4BaseCutEven target = a4BaseCutEvenFormula target := by
  ext word
  simp only [a4BaseCutEven, a4BaseCutEvenFormula, Set.mem_setOf_eq,
    Set.mem_union]
  constructor
  · intro heven
    rcases a4_noCut_or_firstCut 0 target word with hzero |
        ⟨first, rest, hcount, hrun, hsplit⟩
    · exact Or.inl hzero
    · right
      have hrestOdd : a4BaseCutCountFrom target target rest % 2 = 1 := by
        rw [← hsplit, a4BaseCutCountFrom_append, hrun] at heven
        omega
      rcases a4_noCut_or_firstCut target target rest with hzeroRest |
          ⟨second, rest2, hcount2, hrun2, hsplit2⟩
      · omega
      · have heven2 : a4BaseCutCountFrom target target rest2 % 2 = 0 := by
          rw [← hsplit2, a4BaseCutCountFrom_append, hrun2] at hrestOdd
          omega
        exact ⟨first, ⟨hcount, hrun⟩, rest, ⟨second,
          ⟨hcount2, hrun2⟩, rest2,
          (a4_returnEven_formula target rest2).mp heven2, hsplit2⟩, hsplit⟩
  · rintro (hzero | ⟨first, hfirst, rest,
        ⟨second, hsecond, rest2, hrest2, rfl⟩, rfl⟩)
    · change a4BaseCutCountFrom 0 target word = 0 at hzero
      omega
    · simp only [a4BaseCutInitialBlock, a4BaseCutReturnBlock,
        Set.mem_setOf_eq] at hfirst hsecond
      have heven2 := (a4_returnEven_formula target rest2).mpr hrest2
      rw [a4BaseCutCountFrom_append, hfirst.2,
        a4BaseCutCountFrom_append, hsecond.2]
      omega

theorem hasHeightAtMost_a4BaseCutParity (target : ZMod 3)
    (hO : IsStarFree (a4BaseCutInitialBlock target))
    (hX : IsStarFree (a4BaseCutReturnBlock target))
    (hV : IsStarFree (a4BaseCutTail target))
    (hV0 : IsStarFree (a4BaseCutInitialTail target)) :
    HasHeightAtMost (a4BaseCutOdd target) 1 ∧
      HasHeightAtMost (a4BaseCutEven target) 1 := by
  have hpairs : HasHeightAtMost
      (Language.star (Language.concat (a4BaseCutReturnBlock target)
        (a4BaseCutReturnBlock target))) 1 :=
    (hX.concat hX).star
  constructor
  · rw [a4BaseCutOdd_eq_formula]
    exact hO.mono (by omega) |>.concat (hpairs.concat (hV.mono (by omega)))
  · rw [a4BaseCutEven_eq_formula]
    exact (hV0.mono (by omega)).union
      ((hO.mono (by omega)).concat
        ((hX.mono (by omega)).concat (hpairs.concat (hV.mono (by omega)))))

end GSH
