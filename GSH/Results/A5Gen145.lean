import GSH.Regex.Sugar
import GSH.Groups
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic.FinCases

/-!
# Generator-dependent height ≤ 1 for `A₅`

Stepwise proof for `π(a)=(123)`, `π(b)=(145)` following
`notes/A5_generator_dependent_star_height_1.md`.

Left-to-right evaluation: `phi (l :: w) = phi w * letterToA5 l`.
-/

set_option autoImplicit false

open Equiv Equiv.Perm List

namespace GSH
namespace A5Gen145

/-! ## Step 1: alphabet, action, evaluation -/

inductive Letter
  | a
  | b
  deriving DecidableEq, Repr

def letterPerm : Letter → Perm (Fin 5)
  | .a => c[0, 1, 2]
  | .b => c[0, 3, 4]

def letterToA5 : Letter → A5
  | .a => ⟨c[0, 1, 2], mem_alternatingGroup.2 (by decide)⟩
  | .b => ⟨c[0, 3, 4], mem_alternatingGroup.2 (by decide)⟩

@[simp] theorem coe_letterToA5 (x : Letter) :
    (letterToA5 x : Perm (Fin 5)) = letterPerm x := by
  cases x <;> rfl

def applyWord : Word Letter → Fin 5 → Fin 5
  | [], p => p
  | l :: w, p => applyWord w (letterPerm l p)

def phi : Word Letter → A5
  | [] => 1
  | l :: w => phi w * letterToA5 l

@[simp] theorem applyWord_nil (p : Fin 5) : applyWord [] p = p := rfl
@[simp] theorem phi_nil : phi ([] : Word Letter) = 1 := rfl

theorem applyWord_append (u v : Word Letter) (p : Fin 5) :
    applyWord (u ++ v) p = applyWord v (applyWord u p) := by
  induction u generalizing p with
  | nil => rfl
  | cons _ _ ih => exact ih _

theorem phi_append (u v : Word Letter) : phi (u ++ v) = phi v * phi u := by
  induction u with
  | nil => simp
  | cons _ _ ih => simp [phi, ih, mul_assoc]

theorem coe_phi (w : Word Letter) (p : Fin 5) :
    (phi w : Perm (Fin 5)) p = applyWord w p := by
  induction w generalizing p with
  | nil => simp
  | cons l w ih =>
    simp [phi, applyWord, coe_letterToA5, Subgroup.coe_mul, mul_apply, ih]

def wordProblem : Language Letter := {w | phi w = 1}
def stab (p : Fin 5) : Language Letter := {w | applyWord w p = p}

@[simp] theorem mem_wordProblem_iff (w : Word Letter) :
    w ∈ wordProblem ↔ phi w = 1 := Iff.rfl
@[simp] theorem mem_stab_iff (p : Fin 5) (w : Word Letter) :
    w ∈ stab p ↔ applyWord w p = p := Iff.rfl

/-! ## Step 2: fixing points `0,1,2` ⇒ identity -/

theorem eq_one_of_fixes_012 (g : A5)
    (h0 : (g : Perm (Fin 5)) 0 = 0)
    (h1 : (g : Perm (Fin 5)) 1 = 1)
    (h2 : (g : Perm (Fin 5)) 2 = 2) :
    g = 1 := by
  let σ : Perm (Fin 5) := g
  change σ 0 = 0 at h0
  change σ 1 = 1 at h1
  change σ 2 = 2 at h2
  have ne012 (i : Fin 5) (hi : i = 3 ∨ i = 4) :
      σ i ≠ 0 ∧ σ i ≠ 1 ∧ σ i ≠ 2 := by
    refine ⟨?_, ?_, ?_⟩
    · intro e
      cases hi with
      | inl hi =>
        subst i
        exact (show (3 : Fin 5) ≠ 0 by decide) (σ.injective (e.trans h0.symm))
      | inr hi =>
        subst i
        exact (show (4 : Fin 5) ≠ 0 by decide) (σ.injective (e.trans h0.symm))
    · intro e
      cases hi with
      | inl hi =>
        subst i
        exact (show (3 : Fin 5) ≠ 1 by decide) (σ.injective (e.trans h1.symm))
      | inr hi =>
        subst i
        exact (show (4 : Fin 5) ≠ 1 by decide) (σ.injective (e.trans h1.symm))
    · intro e
      cases hi with
      | inl hi =>
        subst i
        exact (show (3 : Fin 5) ≠ 2 by decide) (σ.injective (e.trans h2.symm))
      | inr hi =>
        subst i
        exact (show (4 : Fin 5) ≠ 2 by decide) (σ.injective (e.trans h2.symm))
  have h3cases : σ 3 = 3 ∨ σ 3 = 4 := by
    have h := ne012 3 (.inl rfl)
    generalize hy : σ 3 = y at h ⊢
    fin_cases y <;> simp_all
  have h4cases : σ 4 = 3 ∨ σ 4 = 4 := by
    have h := ne012 4 (.inr rfl)
    generalize hy : σ 4 = y at h ⊢
    fin_cases y <;> simp_all
  have h34 : σ 3 = 3 ∧ σ 4 = 4 := by
    cases h3cases with
    | inl h33 =>
      cases h4cases with
      | inr h44 => exact ⟨h33, h44⟩
      | inl h43 =>
        exact absurd (σ.injective (h33.trans h43.symm)) (by decide)
    | inr h34 =>
      cases h4cases with
      | inl h43 =>
        have eqv : σ = Equiv.swap (3 : Fin 5) 4 := by
          ext y
          fin_cases y <;> simp [h0, h1, h2, h34, h43, Equiv.swap_apply_of_ne_of_ne]
        have : sign σ = -1 := by
          rw [eqv]
          exact sign_swap (by decide : (3 : Fin 5) ≠ 4)
        have : sign σ = 1 := mem_alternatingGroup.1 g.property
        simp_all
      | inr h44 =>
        exact absurd (σ.injective (h34.trans h44.symm)) (by decide)
  apply Subtype.ext
  apply Equiv.ext
  intro x
  fin_cases x <;> simp [σ, h0, h1, h2, h34]

theorem wordProblem_eq_stab012 :
    wordProblem = stab 0 ∩ stab 1 ∩ stab 2 := by
  ext w
  simp only [mem_wordProblem_iff, Set.mem_inter_iff, mem_stab_iff]
  constructor
  · intro h; simp [← coe_phi, h]
  · rintro ⟨⟨h0, h1⟩, h2⟩
    exact eq_one_of_fixes_012 (phi w)
      (by simpa [coe_phi] using h0)
      (by simpa [coe_phi] using h1)
      (by simpa [coe_phi] using h2)

/-! ## Step 3: `A₀ = {a}*`, `B₀ = {b}*` -/

open GRegex

def U : GRegex Letter := univ
def A0 : GRegex Letter := compl (concat U (concat (atom .b) U))
def B0 : GRegex Letter := compl (concat U (concat (atom .a) U))

theorem denote_A0 :
    denote A0 = {w : Word Letter | ∀ x ∈ w, x = Letter.a} := by
  ext w
  have contains_b :
      w ∈ denote (concat U (concat (atom .b) U)) ↔ Letter.b ∈ w := by
    simp only [U, denote_univ, denote, Language.concat, Language.letter]
    change (∃ u ∈ (Set.univ : Language Letter),
      ∃ v ∈ Language.concat (Language.letter Letter.b) Set.univ, u ++ v = w) ↔
      Letter.b ∈ w
    constructor
    · rintro ⟨u, -, v, ⟨x, hx, y, -, hxy⟩, huv⟩
      have hx' : x = [Letter.b] := hx
      subst x
      rw [← huv, ← hxy]
      simp
    · intro hw
      obtain ⟨u, v, rfl⟩ := List.mem_iff_append.1 hw
      refine ⟨u, Set.mem_univ _, [Letter.b] ++ v, ?_, rfl⟩
      exact ⟨[Letter.b], rfl, v, Set.mem_univ _, rfl⟩
  change w ∉ denote (concat U (concat (atom .b) U)) ↔ _
  rw [contains_b]
  constructor
  · intro h x hx
    cases x with
    | a => rfl
    | b => exact False.elim (h hx)
  · intro h hw
    exact (by decide : Letter.b ≠ Letter.a) (h Letter.b hw)

theorem denote_B0 :
    denote B0 = {w : Word Letter | ∀ x ∈ w, x = Letter.b} := by
  ext w
  have contains_a :
      w ∈ denote (concat U (concat (atom .a) U)) ↔ Letter.a ∈ w := by
    simp only [U, denote_univ, denote, Language.concat, Language.letter]
    change (∃ u ∈ (Set.univ : Language Letter),
      ∃ v ∈ Language.concat (Language.letter Letter.a) Set.univ, u ++ v = w) ↔
      Letter.a ∈ w
    constructor
    · rintro ⟨u, -, v, ⟨x, hx, y, -, hxy⟩, huv⟩
      have hx' : x = [Letter.a] := hx
      subst x
      rw [← huv, ← hxy]
      simp
    · intro hw
      obtain ⟨u, v, rfl⟩ := List.mem_iff_append.1 hw
      refine ⟨u, Set.mem_univ _, [Letter.a] ++ v, ?_, rfl⟩
      exact ⟨[Letter.a], rfl, v, Set.mem_univ _, rfl⟩
  change w ∉ denote (concat U (concat (atom .a) U)) ↔ _
  rw [contains_a]
  constructor
  · intro h x hx
    cases x with
    | a => exact False.elim (h hx)
    | b => rfl
  · intro h hw
    exact (by decide : Letter.a ≠ Letter.b) (h Letter.a hw)

/-! ## Step 4: transition table -/

@[simp] theorem a_apply : letterPerm .a 0 = 1 ∧ letterPerm .a 1 = 2 ∧
    letterPerm .a 2 = 0 ∧ letterPerm .a 3 = 3 ∧ letterPerm .a 4 = 4 := by
  decide

@[simp] theorem b_apply : letterPerm .b 0 = 3 ∧ letterPerm .b 1 = 1 ∧
    letterPerm .b 2 = 2 ∧ letterPerm .b 3 = 4 ∧ letterPerm .b 4 = 0 := by
  decide

theorem apply_replicate_b_at_1 (k : Nat) :
    applyWord (replicate k .b) 1 = 1 := by
  induction k with
  | zero => simp
  | succ k ih => simp [replicate_succ, applyWord, ih, b_apply]

theorem apply_replicate_b_at_2 (k : Nat) :
    applyWord (replicate k .b) 2 = 2 := by
  induction k with
  | zero => simp
  | succ k ih => simp [replicate_succ, applyWord, ih, b_apply]

theorem apply_replicate_a_at_3 (k : Nat) :
    applyWord (replicate k .a) 3 = 3 := by
  induction k with
  | zero => simp
  | succ k ih => simp [replicate_succ, applyWord, ih, a_apply]

theorem apply_replicate_a_at_4 (k : Nat) :
    applyWord (replicate k .a) 4 = 4 := by
  induction k with
  | zero => simp
  | succ k ih => simp [replicate_succ, applyWord, ih, a_apply]

theorem exists_replicate_of_forall (x : Letter) (w : Word Letter)
    (h : ∀ y ∈ w, y = x) :
    ∃ k, w = replicate k x := by
  induction w with
  | nil => exact ⟨0, rfl⟩
  | cons y w ih =>
    have hy : y = x := h y (by simp)
    obtain ⟨k, hk⟩ := ih (by
      intro z hz
      exact h z (by simp [hz]))
    subst y
    subst w
    exact ⟨k + 1, by simp [replicate_succ]⟩

theorem apply_a_bstar_a_bstar_a (u v : Word Letter)
    (hu : ∀ x ∈ u, x = Letter.b) (hv : ∀ x ∈ v, x = Letter.b) :
    applyWord ([.a] ++ u ++ [.a] ++ v ++ [.a]) 0 = 0 := by
  obtain ⟨m, hm⟩ := exists_replicate_of_forall .b u hu
  obtain ⟨n, hn⟩ := exists_replicate_of_forall .b v hv
  subst u
  subst v
  simp only [List.append_assoc]
  change applyWord (.a :: (replicate m .b ++ .a :: (replicate n .b ++ [.a]))) 0 = 0
  simp only [applyWord, a_apply]
  rw [applyWord_append, apply_replicate_b_at_1]
  simp only [applyWord, a_apply]
  rw [applyWord_append, apply_replicate_b_at_2]
  simp [applyWord, a_apply]

theorem apply_b_astar_b_astar_b (u v : Word Letter)
    (hu : ∀ x ∈ u, x = Letter.a) (hv : ∀ x ∈ v, x = Letter.a) :
    applyWord ([.b] ++ u ++ [.b] ++ v ++ [.b]) 0 = 0 := by
  obtain ⟨m, hm⟩ := exists_replicate_of_forall .a u hu
  obtain ⟨n, hn⟩ := exists_replicate_of_forall .a v hv
  subst u
  subst v
  simp only [List.append_assoc]
  change applyWord (.b :: (replicate m .a ++ .b :: (replicate n .a ++ [.b]))) 0 = 0
  simp only [applyWord, b_apply]
  rw [applyWord_append, apply_replicate_a_at_3]
  simp only [applyWord, b_apply]
  rw [applyWord_append, apply_replicate_a_at_4]
  simp [applyWord, b_apply]

/-! ## Step 5: first-return code `C` and `K₁, K₂, K₃` -/

def C : GRegex Letter :=
  union
    (concat5 (atom .a) B0 (atom .a) B0 (atom .a))
    (concat5 (atom .b) A0 (atom .b) A0 (atom .b))

def K1 : GRegex Letter := star C

def K2visit : GRegex Letter :=
  concat B0 <|
    concat (atom .a) <|
      concat B0 <|
        concat (atom .a) <|
          concat K1 <|
            concat (atom .a) B0

def K2 : GRegex Letter := union B0 K2visit

def K3visit : GRegex Letter :=
  concat B0 <|
    concat (atom .a) <|
      concat K1 <|
        concat (atom .a) <|
          concat B0 <|
            concat (atom .a) B0

def K3 : GRegex Letter := union B0 K3visit

def certificate : GRegex Letter := inter K1 (inter K2 K3)

/-! ### Syntactic height ≤ 1 -/

theorem starHeight_A0 : starHeight A0 = 0 := by simp [A0, U, starHeight, univ]
theorem starHeight_B0 : starHeight B0 = 0 := by simp [B0, U, starHeight, univ]
theorem starHeight_C : starHeight C = 0 := by
  simp [C, starHeight_A0, starHeight_B0, starHeight, concat5]
theorem starHeight_K1 : starHeight K1 = 1 := by simp [K1, starHeight_C]
theorem starHeight_K2 : starHeight K2 = 1 := by
  simp [K2, K2visit, K1, starHeight_B0, starHeight_C, starHeight]
theorem starHeight_K3 : starHeight K3 = 1 := by
  simp [K3, K3visit, K1, starHeight_B0, starHeight_C, starHeight]
theorem starHeight_certificate_eq : starHeight certificate = 1 := by
  simp [certificate, starHeight_inter, starHeight_K1, starHeight_K2, starHeight_K3]
theorem starHeight_certificate : starHeight certificate ≤ 1 :=
  Nat.le_of_eq starHeight_certificate_eq

/-! ### Semantic equalities (core) -/

/-- Words in `denote C` return to point `0`. -/
-- BLUEPRINT: N-A5-GEN145-001
theorem denote_C_subset_stab0_firstReturn :
    denote C ⊆ stab 0 := by
  intro w hw
  simp only [C, denote, concat5, Language.concat, Set.mem_union] at hw
  rcases hw with h | h
  · rcases h with ⟨u, hu, v, ⟨r, hr, s, ⟨t, ht, z, ⟨q, hq, x, hx, hqx⟩, htz⟩, hrs⟩, huv⟩
    have hu' : u = [.a] := hu
    have ht' : t = [.a] := ht
    have hx' : x = [.a] := hx
    rw [denote_B0] at hr hq
    subst u
    subst t
    subst x
    rw [← huv, ← hrs, ← htz, ← hqx]
    change applyWord ([.a] ++ (r ++ ([.a] ++ (q ++ [.a])))) 0 = 0
    simpa only [List.append_assoc] using apply_a_bstar_a_bstar_a r q hr hq
  · rcases h with ⟨u, hu, v, ⟨r, hr, s, ⟨t, ht, z, ⟨q, hq, x, hx, hqx⟩, htz⟩, hrs⟩, huv⟩
    have hu' : u = [.b] := hu
    have ht' : t = [.b] := ht
    have hx' : x = [.b] := hx
    rw [denote_A0] at hr hq
    subst u
    subst t
    subst x
    rw [← huv, ← hrs, ← htz, ← hqx]
    change applyWord ([.b] ++ (r ++ ([.b] ++ (q ++ [.b])))) 0 = 0
    simpa only [List.append_assoc] using apply_b_astar_b_astar_b r q hr hq

theorem mem_B0_replicate (k : Nat) : replicate k Letter.b ∈ denote B0 := by
  rw [denote_B0]
  intro x hx
  exact (List.mem_replicate.mp hx).2

theorem mem_A0_replicate (k : Nat) : replicate k Letter.a ∈ denote A0 := by
  rw [denote_A0]
  intro x hx
  exact (List.mem_replicate.mp hx).2

theorem mem_denote_C_of_a_form (k m : Nat) :
    [.a] ++ replicate k .b ++ [.a] ++ replicate m .b ++ [.a] ∈ denote C := by
  simp only [C, denote, concat5]
  refine Or.inl ?_
  refine ⟨[.a], by simp [Language.letter],
    replicate k .b ++ ([.a] ++ (replicate m .b ++ [.a])), ?_, by simp⟩
  refine ⟨replicate k .b, mem_B0_replicate k,
    [.a] ++ (replicate m .b ++ [.a]), ?_, by simp⟩
  refine ⟨[.a], by simp [Language.letter],
    replicate m .b ++ [.a], ?_, by simp⟩
  exact ⟨replicate m .b, mem_B0_replicate m, [.a], by simp [Language.letter], by simp⟩

theorem mem_denote_C_of_b_form (k m : Nat) :
    [.b] ++ replicate k .a ++ [.b] ++ replicate m .a ++ [.b] ∈ denote C := by
  simp only [C, denote, concat5]
  refine Or.inr ?_
  refine ⟨[.b], by simp [Language.letter],
    replicate k .a ++ ([.b] ++ (replicate m .a ++ [.b])), ?_, by simp⟩
  refine ⟨replicate k .a, mem_A0_replicate k,
    [.b] ++ (replicate m .a ++ [.b]), ?_, by simp⟩
  refine ⟨[.b], by simp [Language.letter],
    replicate m .a ++ [.b], ?_, by simp⟩
  exact ⟨replicate m .a, mem_A0_replicate m, [.b], by simp [Language.letter], by simp⟩

/-- Longest `b`-prefix split. -/
theorem split_b_prefix (w : Word Letter) :
    ∃ k rest, w = replicate k .b ++ rest ∧
      (rest = [] ∨ ∃ x xs, rest = x :: xs ∧ x ≠ .b) := by
  induction w with
  | nil => exact ⟨0, [], by simp, Or.inl rfl⟩
  | cons x xs ih =>
    cases x with
    | a => exact ⟨0, .a :: xs, by simp, Or.inr ⟨.a, xs, rfl, by decide⟩⟩
    | b =>
      obtain ⟨k, rest, hsplit, hrest⟩ := ih
      exact ⟨k + 1, rest, by simp [replicate_succ, hsplit], hrest⟩

theorem split_a_prefix (w : Word Letter) :
    ∃ k rest, w = replicate k .a ++ rest ∧
      (rest = [] ∨ ∃ x xs, rest = x :: xs ∧ x ≠ .a) := by
  induction w with
  | nil => exact ⟨0, [], by simp, Or.inl rfl⟩
  | cons x xs ih =>
    cases x with
    | b => exact ⟨0, .b :: xs, by simp, Or.inr ⟨.b, xs, rfl, by decide⟩⟩
    | a =>
      obtain ⟨k, rest, hsplit, hrest⟩ := ih
      exact ⟨k + 1, rest, by simp [replicate_succ, hsplit], hrest⟩

theorem classify_return_from_1 (rest : Word Letter)
    (hend : applyWord rest 1 = 0)
    (hfirst : ∀ u v, u ≠ [] → v ≠ [] → u ++ v = Letter.a :: rest → applyWord u 0 ≠ 0) :
    ∃ k m, rest = replicate k .b ++ [.a] ++ replicate m .b ++ [.a] := by
  obtain ⟨k, rest1, hsplit, hrest1⟩ := split_b_prefix rest
  have rest1_ne : rest1 ≠ [] := by
    intro h
    subst h
    have : applyWord rest 1 = 1 := by simpa [hsplit] using apply_replicate_b_at_1 k
    simp_all
  obtain ⟨x, rest2, hx⟩ : ∃ x rest2, rest1 = x :: rest2 ∧ x ≠ .b := by
    cases hrest1 with
    | inl h => exact (rest1_ne h).elim
    | inr h => exact h
  have hx' : x = .a := by
    cases x with
    | a => rfl
    | b => exact (hx.2 rfl).elim
  subst x
  have hend2 : applyWord rest2 2 = 0 := by
    have := hend
    rw [hsplit, hx.1] at this
    simpa [applyWord_append, apply_replicate_b_at_1, applyWord, a_apply] using this
  obtain ⟨m, rest3, hsplit2, hrest3⟩ := split_b_prefix rest2
  have rest3_ne : rest3 ≠ [] := by
    intro h
    subst h
    have : applyWord rest2 2 = 2 := by simpa [hsplit2] using apply_replicate_b_at_2 m
    simp_all
  obtain ⟨y, rest4, hy⟩ : ∃ y rest4, rest3 = y :: rest4 ∧ y ≠ .b := by
    cases hrest3 with
    | inl h => exact (rest3_ne h).elim
    | inr h => exact h
  have hy' : y = .a := by
    cases y with
    | a => rfl
    | b => exact (hy.2 rfl).elim
  subst y
  have rest4_nil : rest4 = [] := by
    by_contra hne
    have hu :
        applyWord ([.a] ++ replicate k .b ++ [.a] ++ replicate m .b ++ [.a]) 0 = 0 :=
      apply_a_bstar_a_bstar_a _ _
        (by intro z hz; exact (List.mem_replicate.mp hz).2)
        (by intro z hz; exact (List.mem_replicate.mp hz).2)
    have hsplitw :
        ([.a] ++ replicate k .b ++ [.a] ++ replicate m .b ++ [.a]) ++ rest4 =
          .a :: rest := by
      simp [hsplit, hx.1, hsplit2, hy.1]
    exact hfirst _ rest4 (by simp) hne hsplitw hu
  subst rest4
  exact ⟨k, m, by simp [hsplit, hx.1, hsplit2, hy.1]⟩

theorem classify_return_from_3 (rest : Word Letter)
    (hend : applyWord rest 3 = 0)
    (hfirst : ∀ u v, u ≠ [] → v ≠ [] → u ++ v = Letter.b :: rest → applyWord u 0 ≠ 0) :
    ∃ k m, rest = replicate k .a ++ [.b] ++ replicate m .a ++ [.b] := by
  obtain ⟨k, rest1, hsplit, hrest1⟩ := split_a_prefix rest
  have rest1_ne : rest1 ≠ [] := by
    intro h
    subst h
    have : applyWord rest 3 = 3 := by simpa [hsplit] using apply_replicate_a_at_3 k
    simp_all
  obtain ⟨x, rest2, hx⟩ : ∃ x rest2, rest1 = x :: rest2 ∧ x ≠ .a := by
    cases hrest1 with
    | inl h => exact (rest1_ne h).elim
    | inr h => exact h
  have hx' : x = .b := by
    cases x with
    | b => rfl
    | a => exact (hx.2 rfl).elim
  subst x
  have hend2 : applyWord rest2 4 = 0 := by
    have := hend
    rw [hsplit, hx.1] at this
    simpa [applyWord_append, apply_replicate_a_at_3, applyWord, b_apply] using this
  obtain ⟨m, rest3, hsplit2, hrest3⟩ := split_a_prefix rest2
  have rest3_ne : rest3 ≠ [] := by
    intro h
    subst h
    have : applyWord rest2 4 = 4 := by simpa [hsplit2] using apply_replicate_a_at_4 m
    simp_all
  obtain ⟨y, rest4, hy⟩ : ∃ y rest4, rest3 = y :: rest4 ∧ y ≠ .a := by
    cases hrest3 with
    | inl h => exact (rest3_ne h).elim
    | inr h => exact h
  have hy' : y = .b := by
    cases y with
    | b => rfl
    | a => exact (hy.2 rfl).elim
  subst y
  have rest4_nil : rest4 = [] := by
    by_contra hne
    have hu :
        applyWord ([.b] ++ replicate k .a ++ [.b] ++ replicate m .a ++ [.b]) 0 = 0 :=
      apply_b_astar_b_astar_b _ _
        (by intro z hz; exact (List.mem_replicate.mp hz).2)
        (by intro z hz; exact (List.mem_replicate.mp hz).2)
    have hsplitw :
        ([.b] ++ replicate k .a ++ [.b] ++ replicate m .a ++ [.b]) ++ rest4 =
          .b :: rest := by
      simp [hsplit, hx.1, hsplit2, hy.1]
    exact hfirst _ rest4 (by simp) hne hsplitw hu
  subst rest4
  exact ⟨k, m, by simp [hsplit, hx.1, hsplit2, hy.1]⟩

/-- Every nonempty first return from `0` lies in `denote C`. -/
-- BLUEPRINT: N-A5-GEN145-002
theorem firstReturn_mem_denote_C (w : Word Letter) (hw : w ≠ [])
    (hfix : applyWord w 0 = 0)
    (hfirst : ∀ u v, u ≠ [] → v ≠ [] → u ++ v = w → applyWord u 0 ≠ 0) :
    w ∈ denote C := by
  obtain ⟨l, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
  cases l with
  | a =>
    have hend : applyWord rest 1 = 0 := by simpa [applyWord, a_apply] using hfix
    obtain ⟨k, m, hk⟩ := classify_return_from_1 rest hend (by
      intro u v hu hv huv; exact hfirst u v hu hv (by simpa using huv))
    subst rest
    simpa using mem_denote_C_of_a_form k m
  | b =>
    have hend : applyWord rest 3 = 0 := by simpa [applyWord, b_apply] using hfix
    obtain ⟨k, m, hk⟩ := classify_return_from_3 rest hend (by
      intro u v hu hv huv; exact hfirst u v hu hv (by simpa using huv))
    subst rest
    simpa using mem_denote_C_of_b_form k m

/-- If `u ∈ L` and `v ∈ L*`, then `u ++ v ∈ L*`. -/
theorem concat_left_mem_star {α : Type*} (L : Language α) {u v : Word α}
    (hu : u ∈ L) (hv : v ∈ Language.star L) : u ++ v ∈ Language.star L := by
  obtain ⟨m, hm⟩ := hv
  induction m generalizing v with
  | zero =>
    simp [Language.power, Language.epsilon] at hm
    subst v
    exact ⟨1, by simpa [Language.power, Language.concat] using hu⟩
  | succ m ih =>
    simp [Language.power, Language.concat] at hm
    obtain ⟨p, hp, c, hc, rfl⟩ := hm
    have hup : u ++ p ∈ Language.star L := ih hp
    obtain ⟨k, hk⟩ := hup
    refine ⟨k + 1, ?_⟩
    simp [Language.power, Language.concat]
    exact ⟨u ++ p, hk, c, hc, by simp⟩

/-- Minimal nonempty return prefix to point `0`. -/
theorem exists_first_return_prefix (w : Word Letter) (hw : w ≠ [])
    (hfix : applyWord w 0 = 0) :
    ∃ u v, u ≠ [] ∧ u ++ v = w ∧ applyWord u 0 = 0 ∧
      (∀ u' v', u' ≠ [] → v' ≠ [] → u' ++ v' = u → applyWord u' 0 ≠ 0) := by
  let P (k : Nat) : Prop :=
    0 < k ∧ k ≤ w.length ∧ applyWord (w.take k) 0 = 0
  have hP : ∃ k, P k :=
    ⟨w.length, List.length_pos_of_ne_nil hw, le_rfl,
      by simpa [List.take_length] using hfix⟩
  classical
  let k := Nat.find hP
  have hk : P k := Nat.find_spec hP
  have hmin : ∀ j, j < k → ¬ P j := fun j hj => Nat.find_min hP hj
  refine ⟨w.take k, w.drop k, ?_, List.take_append_drop k w, hk.2.2, ?_⟩
  · intro hnil
    have hlen := congrArg List.length hnil
    simp [List.length_take, Nat.min_eq_left hk.2.1] at hlen
    exact (Nat.ne_of_gt hk.1) hlen
  · intro u' v' hu' hv' huv' hret
    have hlen_uv : u'.length + v'.length = k := by
      have := congrArg List.length huv'
      simp [List.length_take, Nat.min_eq_left hk.2.1] at this
      exact this
    have hulen : u'.length < k := by
      have : 0 < v'.length := List.length_pos_of_ne_nil hv'
      omega
    have hu'_prefix : u' <+: w := by
      refine ⟨v' ++ w.drop k, ?_⟩
      calc
        u' ++ (v' ++ w.drop k) = (u' ++ v') ++ w.drop k := by rw [List.append_assoc]
        _ = w.take k ++ w.drop k := by rw [huv']
        _ = w := List.take_append_drop k w
    have htake : w.take u'.length = u' := (List.prefix_iff_eq_take.mp hu'_prefix).symm
    have hPlen : P u'.length := by
      refine ⟨List.length_pos_of_ne_nil hu', Nat.le_trans (Nat.le_of_lt hulen) hk.2.1, ?_⟩
      simpa [htake] using hret
    exact hmin u'.length hulen hPlen

/-- `K₁` denotes the stabilizer of point `0`. -/
-- BLUEPRINT: N-A5-GEN145-003
theorem denote_K1 : denote K1 = stab 0 := by
  ext w
  constructor
  · intro hw
    simp only [K1, denote, Language.mem_star_iff] at hw
    obtain ⟨n, hn⟩ := hw
    induction n generalizing w with
    | zero =>
      simp [Language.power, Language.epsilon] at hn
      simp [hn]
    | succ n ih =>
      simp [Language.power, Language.concat] at hn
      obtain ⟨p, hp, c, hc, rfl⟩ := hn
      have hp0 : applyWord p 0 = 0 := ih p hp
      have hc0 : applyWord c 0 = 0 := denote_C_subset_stab0_firstReturn hc
      simp [stab, applyWord_append, hp0, hc0]
  · intro hfix
    refine Nat.strong_induction_on (p := fun n => ∀ w : Word Letter,
        w.length = n → applyWord w 0 = 0 → w ∈ denote K1) w.length ?_ w rfl hfix
    intro n ih w hlen hfix
    cases w with
    | nil =>
      simp [K1, denote]
      exact ⟨0, by simp [Language.power]⟩
    | cons l rest =>
      have hwne : l :: rest ≠ [] := List.cons_ne_nil _ _
      obtain ⟨u, v, hu_ne, huv, hu_ret, hu_first⟩ :=
        exists_first_return_prefix (l :: rest) hwne hfix
      have huC : u ∈ denote C := firstReturn_mem_denote_C u hu_ne hu_ret hu_first
      have hv0 : applyWord v 0 = 0 := by
        have := hfix
        rw [← huv, applyWord_append, hu_ret] at this
        exact this
      have hvlen : v.length < n := by
        have : u.length + v.length = n := by
          rw [← List.length_append, huv, hlen]
        have : 0 < u.length := List.length_pos_of_ne_nil hu_ne
        omega
      have hvK : v ∈ denote K1 := ih v.length hvlen v rfl hv0
      simpa [K1, denote, ← huv] using concat_left_mem_star (denote C) huC (by simpa [K1, denote] using hvK)


/-! ### K2 / K3 stabilizer characterizations -/

theorem mem_B0_apply_at_1 (w : Word Letter) (hw : w ∈ denote B0) :
    applyWord w 1 = 1 := by
  rw [denote_B0] at hw
  obtain ⟨k, rfl⟩ := exists_replicate_of_forall .b w hw
  exact apply_replicate_b_at_1 k

theorem mem_B0_apply_at_2 (w : Word Letter) (hw : w ∈ denote B0) :
    applyWord w 2 = 2 := by
  rw [denote_B0] at hw
  obtain ⟨k, rfl⟩ := exists_replicate_of_forall .b w hw
  exact apply_replicate_b_at_2 k

theorem apply_baba_from_1 (k m : Nat) :
    applyWord (replicate k .b ++ [.a] ++ replicate m .b ++ [.a]) 1 = 0 := by
  simp only [List.append_assoc]
  change applyWord (replicate k .b ++ ([.a] ++ (replicate m .b ++ [.a]))) 1 = 0
  rw [applyWord_append, apply_replicate_b_at_1]
  have h12 : letterPerm .a 1 = 2 := by decide
  change applyWord ([.a] ++ (replicate m .b ++ [.a])) 1 = 0
  simp [applyWord, h12, applyWord_append, apply_replicate_b_at_2]

theorem apply_ba_from_2 (k : Nat) :
    applyWord (replicate k .b ++ [.a]) 2 = 0 := by
  rw [applyWord_append, apply_replicate_b_at_2]
  decide

theorem apply_ab_from_0 (k : Nat) :
    applyWord ([.a] ++ replicate k .b) 0 = 1 := by
  have : letterPerm .a 0 = 1 := by decide
  change applyWord (replicate k .b) (letterPerm .a 0) = 1
  rw [this]
  exact apply_replicate_b_at_1 k

theorem apply_aba_b_from_0 (k m : Nat) :
    applyWord ([.a] ++ replicate k .b ++ [.a] ++ replicate m .b) 0 = 2 := by
  simp only [List.append_assoc]
  change applyWord ([.a] ++ (replicate k .b ++ ([.a] ++ replicate m .b))) 0 = 2
  have h01 : letterPerm .a 0 = 1 := by decide
  simp [applyWord, h01, applyWord_append, apply_replicate_b_at_1,
    apply_replicate_b_at_2]

theorem walk_from_2_avoid_0_all_b (w : Word Letter)
    (hnever : ∀ k, 0 < k → k ≤ w.length → applyWord (w.take k) 2 ≠ 0) :
    ∀ x ∈ w, x = Letter.b := by
  induction w with
  | nil => intro _ h; cases h
  | cons l rest ih =>
    have hl : l = Letter.b := by
      cases l with
      | b => rfl
      | a =>
        have hit :
            applyWord ((Letter.a :: rest).take 1) 2 = 0 := by
          simp [applyWord]
        exact (hnever 1 (by decide) (by simp) hit).elim
    subst l
    have hnever' : ∀ k, 0 < k → k ≤ rest.length → applyWord (rest.take k) 2 ≠ 0 := by
      intro k hkpos hkle
      have h := hnever (k + 1) (Nat.succ_pos _) (by simpa using Nat.succ_le_succ hkle)
      simpa [List.take_succ_cons, applyWord, b_apply] using h
    intro x hx
    cases hx with
    | head => rfl
    | tail _ hx => exact ih hnever' x hx

theorem apply_avoid_0_from_3_mem_34 (w : Word Letter)
    (hnever : ∀ k, 0 < k → k ≤ w.length → applyWord (w.take k) 3 ≠ 0) :
    applyWord w 3 = 3 ∨ applyWord w 3 = 4 := by
  induction w with
  | nil => exact Or.inl rfl
  | cons l rest ih =>
    cases l with
    | a =>
      have hnever' : ∀ k, 0 < k → k ≤ rest.length → applyWord (rest.take k) 3 ≠ 0 := by
        intro k hkpos hkle
        have h := hnever (k + 1) (Nat.succ_pos _) (by simpa using Nat.succ_le_succ hkle)
        have : letterPerm .a 3 = 3 := by decide
        simpa [List.take_succ_cons, applyWord, this] using h
      have hrest := ih hnever'
      have ha3 : letterPerm .a 3 = 3 := by decide
      simpa [applyWord, ha3] using hrest
    | b =>
      have hnever4 : ∀ k, 0 < k → k ≤ rest.length → applyWord (rest.take k) 4 ≠ 0 := by
        intro k hkpos hkle
        have h := hnever (k + 1) (Nat.succ_pos _) (by simpa using Nat.succ_le_succ hkle)
        have : letterPerm .b 3 = 4 := by decide
        simpa [List.take_succ_cons, applyWord, this] using h
      have rest_a : ∀ x ∈ rest, x = Letter.a := by
        clear ih hnever
        induction rest with
        | nil => intro _ h; cases h
        | cons x xs ihx =>
          have hx : x = Letter.a := by
            cases x with
            | a => rfl
            | b =>
              have hit : applyWord ((Letter.b :: xs).take 1) 4 = 0 := by
                simp [applyWord]
              exact (hnever4 1 (by decide) (by simp) hit).elim
          subst x
          intro y hy
          cases hy with
          | head => rfl
          | tail _ hy =>
            exact ihx (by
              intro t htpos htle
              have h := hnever4 (t + 1) (Nat.succ_pos _) (by simpa using Nat.succ_le_succ htle)
              have : letterPerm .a 4 = 4 := by decide
              simpa [List.take_succ_cons, applyWord, this] using h) y hy
      obtain ⟨n, rn⟩ := exists_replicate_of_forall .a rest rest_a
      subst rest
      have : letterPerm .b 3 = 4 := by decide
      simp [applyWord, this, apply_replicate_a_at_4]

theorem stab1_never_hit_0_mem_B0 (w : Word Letter)
    (hend : applyWord w 1 = 1)
    (hnever : ∀ k, 0 < k → k ≤ w.length → applyWord (w.take k) 1 ≠ 0) :
    w ∈ denote B0 := by
  rw [denote_B0]
  induction w with
  | nil => intro _ h; cases h
  | cons l rest ih =>
    have hl : l = Letter.b := by
      cases l with
      | b => rfl
      | a =>
        have hend2 : applyWord rest 2 = 1 := by
          have : letterPerm .a 1 = 2 := by decide
          simpa [applyWord, this] using hend
        have never2 : ∀ k, 0 < k → k ≤ rest.length → applyWord (rest.take k) 2 ≠ 0 := by
          intro k hkpos hkle
          have h := hnever (k + 1) (Nat.succ_pos _) (by simpa using Nat.succ_le_succ hkle)
          have : letterPerm .a 1 = 2 := by decide
          simpa [List.take_succ_cons, applyWord, this] using h
        have rest_b := walk_from_2_avoid_0_all_b rest never2
        obtain ⟨k, rk⟩ := exists_replicate_of_forall .b rest rest_b
        subst rest
        have : applyWord (replicate k Letter.b) 2 = 2 := apply_replicate_b_at_2 k
        exact absurd (hend2.symm.trans this) (by decide)
    subst l
    have hend' : applyWord rest 1 = 1 := by simpa [applyWord, b_apply] using hend
    have hnever' : ∀ k, 0 < k → k ≤ rest.length → applyWord (rest.take k) 1 ≠ 0 := by
      intro k hkpos hkle
      have h := hnever (k + 1) (Nat.succ_pos _) (by simpa using Nat.succ_le_succ hkle)
      simpa [List.take_succ_cons, applyWord, b_apply] using h
    intro x hx
    cases hx with
    | head => rfl
    | tail _ hx => exact ih hend' hnever' x hx

theorem stab2_never_hit_0_mem_B0 (w : Word Letter)
    (_hend : applyWord w 2 = 2)
    (hnever : ∀ k, 0 < k → k ≤ w.length → applyWord (w.take k) 2 ≠ 0) :
    w ∈ denote B0 := by
  rw [denote_B0]
  exact walk_from_2_avoid_0_all_b w hnever

/-- Minimal nonempty prefix from `p` that first hits `0`. -/
theorem exists_first_hit_0_prefix (p : Fin 5) (w : Word Letter)
    (hhit : ∃ k, 0 < k ∧ k ≤ w.length ∧ applyWord (w.take k) p = 0) :
    ∃ u v, u ≠ [] ∧ u ++ v = w ∧ applyWord u p = 0 ∧
      (∀ u' v', u' ≠ [] → v' ≠ [] → u' ++ v' = u → applyWord u' p ≠ 0) := by
  let P (k : Nat) : Prop :=
    0 < k ∧ k ≤ w.length ∧ applyWord (w.take k) p = 0
  have hP : ∃ k, P k := hhit
  classical
  let k := Nat.find hP
  have hk : P k := Nat.find_spec hP
  have hmin : ∀ j, j < k → ¬ P j := fun j hj => Nat.find_min hP hj
  refine ⟨w.take k, w.drop k, ?_, List.take_append_drop k w, hk.2.2, ?_⟩
  · intro hnil
    have hlen := congrArg List.length hnil
    simp [List.length_take, Nat.min_eq_left hk.2.1] at hlen
    exact (Nat.ne_of_gt hk.1) hlen
  · intro u' v' hu' hv' huv' hret
    have hulen : u'.length < k := by
      have := congrArg List.length huv'
      simp [List.length_take, Nat.min_eq_left hk.2.1] at this
      have : 0 < v'.length := List.length_pos_of_ne_nil hv'
      omega
    have hu'_prefix : u' <+: w := by
      refine ⟨v' ++ w.drop k, ?_⟩
      calc
        u' ++ (v' ++ w.drop k) = (u' ++ v') ++ w.drop k := by rw [List.append_assoc]
        _ = w.take k ++ w.drop k := by rw [huv']
        _ = w := List.take_append_drop k w
    have htake : w.take u'.length = u' := (List.prefix_iff_eq_take.mp hu'_prefix).symm
    have hPlen : P u'.length := by
      refine ⟨List.length_pos_of_ne_nil hu', Nat.le_trans (Nat.le_of_lt hulen) hk.2.1, ?_⟩
      simpa [htake] using hret
    exact hmin u'.length hulen hPlen

/-- Maximal prefix ending at `0` among indices `≥ i`. -/
theorem exists_last_hit_0_after (p : Fin 5) (w : Word Letter) (i : Nat)
    (hi : i ≤ w.length) (hi0 : applyWord (w.take i) p = 0) :
    ∃ j, i ≤ j ∧ j ≤ w.length ∧ applyWord (w.take j) p = 0 ∧
      (∀ t, j < t → t ≤ w.length → applyWord (w.take t) p ≠ 0) := by
  classical
  let P (k : Nat) : Prop :=
    i ≤ k ∧ k ≤ w.length ∧ applyWord (w.take k) p = 0
  have hPi : P i := ⟨le_rfl, hi, hi0⟩
  let j := Nat.findGreatest P w.length
  have hjP : P j :=
    Nat.findGreatest_spec (P := P) hi hPi
  refine ⟨j, hjP.1, hjP.2.1, hjP.2.2, ?_⟩
  intro t hjt htle hret
  exact (Nat.findGreatest_eq_iff.1 rfl).2.2 hjt htle
    ⟨le_trans hjP.1 (Nat.le_of_lt hjt), htle, hret⟩

theorem classify_first_hit_from_1 (w : Word Letter)
    (hend : applyWord w 1 = 0)
    (hfirst : ∀ u v, u ≠ [] → v ≠ [] → u ++ v = w → applyWord u 1 ≠ 0) :
    ∃ k m, w = replicate k .b ++ [.a] ++ replicate m .b ++ [.a] := by
  obtain ⟨k, rest1, hsplit, hrest1⟩ := split_b_prefix w
  have rest1_ne : rest1 ≠ [] := by
    intro h; subst h
    have : applyWord w 1 = 1 := by simpa [hsplit] using apply_replicate_b_at_1 k
    simp_all
  obtain ⟨x, rest2, hx⟩ : ∃ x rest2, rest1 = x :: rest2 ∧ x ≠ .b := by
    cases hrest1 with
    | inl h => exact (rest1_ne h).elim
    | inr h => exact h
  have : x = .a := by
    cases x with | a => rfl | b => exact (hx.2 rfl).elim
  subst x
  have hend2 : applyWord rest2 2 = 0 := by
    have := hend
    rw [hsplit, hx.1] at this
    have h12 : letterPerm .a 1 = 2 := by decide
    simpa [applyWord_append, apply_replicate_b_at_1, applyWord, h12] using this
  obtain ⟨m, rest3, hsplit2, hrest3⟩ := split_b_prefix rest2
  have rest3_ne : rest3 ≠ [] := by
    intro h; subst h
    have : applyWord rest2 2 = 2 := by simpa [hsplit2] using apply_replicate_b_at_2 m
    simp_all
  obtain ⟨y, rest4, hy⟩ : ∃ y rest4, rest3 = y :: rest4 ∧ y ≠ .b := by
    cases hrest3 with
    | inl h => exact (rest3_ne h).elim
    | inr h => exact h
  have : y = .a := by
    cases y with | a => rfl | b => exact (hy.2 rfl).elim
  subst y
  have rest4_nil : rest4 = [] := by
    by_contra hne
    have hu : applyWord (replicate k .b ++ [.a] ++ replicate m .b ++ [.a]) 1 = 0 :=
      apply_baba_from_1 k m
    have hsplitw :
        (replicate k .b ++ [.a] ++ replicate m .b ++ [.a]) ++ rest4 = w := by
      simp [hsplit, hx.1, hsplit2, hy.1, List.append_assoc]
    exact hfirst _ rest4 (by simp) hne hsplitw hu
  subst rest4
  exact ⟨k, m, by simp [hsplit, hx.1, hsplit2, hy.1, List.append_assoc]⟩

theorem classify_first_hit_from_2 (w : Word Letter)
    (hend : applyWord w 2 = 0)
    (hfirst : ∀ u v, u ≠ [] → v ≠ [] → u ++ v = w → applyWord u 2 ≠ 0) :
    ∃ k, w = replicate k .b ++ [.a] := by
  obtain ⟨k, rest1, hsplit, hrest1⟩ := split_b_prefix w
  have rest1_ne : rest1 ≠ [] := by
    intro h; subst h
    have : applyWord w 2 = 2 := by simpa [hsplit] using apply_replicate_b_at_2 k
    simp_all
  obtain ⟨x, rest2, hx⟩ : ∃ x rest2, rest1 = x :: rest2 ∧ x ≠ .b := by
    cases hrest1 with
    | inl h => exact (rest1_ne h).elim
    | inr h => exact h
  have : x = .a := by
    cases x with | a => rfl | b => exact (hx.2 rfl).elim
  subst x
  have rest2_nil : rest2 = [] := by
    by_contra hne
    have hu : applyWord (replicate k .b ++ [.a]) 2 = 0 := apply_ba_from_2 k
    have hsplitw : (replicate k .b ++ [.a]) ++ rest2 = w := by simp [hsplit, hx.1]
    exact hfirst _ rest2 (by simp) hne hsplitw hu
  subst rest2
  exact ⟨k, by simp [hsplit, hx.1]⟩

theorem classify_exit_0_to_1 (v : Word Letter)
    (hend : applyWord v 0 = 1)
    (hnever : ∀ t, 0 < t → t ≤ v.length → applyWord (v.take t) 0 ≠ 0) :
    ∃ k, v = [.a] ++ replicate k .b := by
  have vne : v ≠ [] := by intro h; subst h; simp at hend
  obtain ⟨l, rest, rfl⟩ := List.exists_cons_of_ne_nil vne
  have hl : l = .a := by
    cases l with
    | a => rfl
    | b =>
      have hnever3 : ∀ t, 0 < t → t ≤ rest.length → applyWord (rest.take t) 3 ≠ 0 := by
        intro t htpos htle
        have h := hnever (t + 1) (Nat.succ_pos _) (by simpa using Nat.succ_le_succ htle)
        simpa [List.take_succ_cons, applyWord, b_apply] using h
      have stay := apply_avoid_0_from_3_mem_34 rest hnever3
      have hend3 : applyWord rest 3 = 1 := by simpa [applyWord, b_apply] using hend
      cases stay <;> simp_all
  subst l
  have hend1 : applyWord rest 1 = 1 := by
    have : letterPerm .a 0 = 1 := by decide
    simpa [applyWord, this] using hend
  have hnever1 : ∀ t, 0 < t → t ≤ rest.length → applyWord (rest.take t) 1 ≠ 0 := by
    intro t htpos htle
    have h := hnever (t + 1) (Nat.succ_pos _) (by simpa using Nat.succ_le_succ htle)
    have : letterPerm .a 0 = 1 := by decide
    simpa [List.take_succ_cons, applyWord, this] using h
  have hb : rest ∈ denote B0 := stab1_never_hit_0_mem_B0 rest hend1 hnever1
  rw [denote_B0] at hb
  obtain ⟨k, rk⟩ := exists_replicate_of_forall .b rest hb
  exact ⟨k, by simp [rk]⟩

theorem take_a_bk_a_suffix (k t : Nat) (rest2 : Word Letter) (_ht : t ≤ rest2.length) :
    ([Letter.a] ++ replicate k Letter.b ++ [Letter.a] ++ rest2).take (2 + k + t) =
      [Letter.a] ++ replicate k Letter.b ++ [Letter.a] ++ rest2.take t := by
  have assoc :
      [Letter.a] ++ replicate k Letter.b ++ [Letter.a] ++ rest2 =
        ([Letter.a] ++ replicate k Letter.b ++ [Letter.a]) ++ rest2 := by
    simp [List.append_assoc]
  have hlen :
      ([Letter.a] ++ replicate k Letter.b ++ [Letter.a]).length + t = 2 + k + t := by
    simp [List.length_append, List.length_replicate]; omega
  rw [assoc, ← hlen, List.take_length_add_append]

theorem classify_exit_0_to_2 (v : Word Letter)
    (hend : applyWord v 0 = 2)
    (hnever : ∀ t, 0 < t → t ≤ v.length → applyWord (v.take t) 0 ≠ 0) :
    ∃ k m, v = [Letter.a] ++ replicate k Letter.b ++ [Letter.a] ++ replicate m Letter.b := by
  have vne : v ≠ [] := by intro h; subst h; simp at hend
  obtain ⟨l, rest, rfl⟩ := List.exists_cons_of_ne_nil vne
  have hl : l = Letter.a := by
    cases l with
    | a => rfl
    | b =>
      have hnever3 : ∀ t, 0 < t → t ≤ rest.length → applyWord (rest.take t) 3 ≠ 0 := by
        intro t htpos htle
        have h := hnever (t + 1) (Nat.succ_pos _) (by simpa using Nat.succ_le_succ htle)
        simpa [List.take_succ_cons, applyWord, b_apply] using h
      have stay := apply_avoid_0_from_3_mem_34 rest hnever3
      have hend3 : applyWord rest 3 = 2 := by simpa [applyWord, b_apply] using hend
      cases stay <;> simp_all
  subst l
  have hend1 : applyWord rest 1 = 2 := by
    have : letterPerm Letter.a 0 = 1 := by decide
    simpa [applyWord, this] using hend
  obtain ⟨k, rest1, hsplit, hrest1⟩ := split_b_prefix rest
  have rest1_ne : rest1 ≠ [] := by
    intro h; subst h
    have : applyWord rest 1 = 1 := by simpa [hsplit] using apply_replicate_b_at_1 k
    simp_all
  obtain ⟨x, rest2, hx⟩ : ∃ x rest2, rest1 = x :: rest2 ∧ x ≠ Letter.b := by
    cases hrest1 with
    | inl h => exact (rest1_ne h).elim
    | inr h => exact h
  have : x = Letter.a := by
    cases x with | a => rfl | b => exact (hx.2 rfl).elim
  subst x
  have hnever2 : ∀ t, 0 < t → t ≤ rest2.length → applyWord (rest2.take t) 2 ≠ 0 := by
    intro t htpos htle
    have htake :
        (Letter.a :: rest).take (2 + k + t) =
          [Letter.a] ++ replicate k Letter.b ++ [Letter.a] ++ rest2.take t := by
      simpa [hsplit, hx.1, List.append_assoc] using
        take_a_bk_a_suffix k t rest2 htle
    have happly :
        applyWord ([Letter.a] ++ replicate k Letter.b ++ [Letter.a] ++ rest2.take t) 0 =
          applyWord (rest2.take t) 2 := by
      have hw :
          [Letter.a] ++ replicate k Letter.b ++ [Letter.a] ++ rest2.take t =
            ([Letter.a] ++ replicate k Letter.b) ++ ([Letter.a] ++ rest2.take t) := by
        simp [List.append_assoc]
      rw [hw, applyWord_append, apply_ab_from_0]
      change applyWord (Letter.a :: rest2.take t) 1 = applyWord (rest2.take t) 2
      have h12 : letterPerm Letter.a 1 = 2 := by decide
      simp only [applyWord, h12]
    have hlen : 2 + k + t ≤ (Letter.a :: rest).length := by
      simp [hsplit, hx.1, List.length_append, List.length_replicate]
      omega
    have h := hnever (2 + k + t) (by omega) hlen
    rw [htake, happly] at h
    exact h
  have rest2_b := walk_from_2_avoid_0_all_b rest2 hnever2
  obtain ⟨m, rm⟩ := exists_replicate_of_forall Letter.b rest2 rest2_b
  refine ⟨k, m, ?_⟩
  simp [hsplit, hx.1, rm, List.append_assoc]

theorem mem_K2visit_of_parts (k₁ m₁ : Nat) (mid : Word Letter) (k₂ : Nat)
    (hmid : mid ∈ denote K1) :
    replicate k₁ .b ++ [.a] ++ replicate m₁ .b ++ [.a] ++ mid ++
      [.a] ++ replicate k₂ .b ∈ denote K2visit := by
  simp only [K2visit, denote, Language.concat, Language.letter]
  refine ⟨replicate k₁ .b, mem_B0_replicate k₁,
    [.a] ++ (replicate m₁ .b ++ ([.a] ++ (mid ++ ([.a] ++ replicate k₂ .b)))), ?_, by simp⟩
  refine ⟨[.a], rfl,
    replicate m₁ .b ++ ([.a] ++ (mid ++ ([.a] ++ replicate k₂ .b))), ?_, by simp⟩
  refine ⟨replicate m₁ .b, mem_B0_replicate m₁,
    [.a] ++ (mid ++ ([.a] ++ replicate k₂ .b)), ?_, by simp⟩
  refine ⟨[.a], rfl, mid ++ ([.a] ++ replicate k₂ .b), ?_, by simp⟩
  refine ⟨mid, hmid, [.a] ++ replicate k₂ .b, ?_, by simp⟩
  exact ⟨[.a], rfl, replicate k₂ .b, mem_B0_replicate k₂, rfl⟩

theorem mem_K3visit_of_parts (k₁ : Nat) (mid : Word Letter) (k₂ m₂ : Nat)
    (hmid : mid ∈ denote K1) :
    replicate k₁ .b ++ [.a] ++ mid ++ [.a] ++ replicate k₂ .b ++ [.a] ++
      replicate m₂ .b ∈ denote K3visit := by
  simp only [K3visit, denote, Language.concat, Language.letter]
  refine ⟨replicate k₁ .b, mem_B0_replicate k₁,
    [.a] ++ (mid ++ ([.a] ++ (replicate k₂ .b ++ ([.a] ++ replicate m₂ .b)))), ?_, by simp⟩
  refine ⟨[.a], rfl,
    mid ++ ([.a] ++ (replicate k₂ .b ++ ([.a] ++ replicate m₂ .b))), ?_, by simp⟩
  refine ⟨mid, hmid,
    [.a] ++ (replicate k₂ .b ++ ([.a] ++ replicate m₂ .b)), ?_, by simp⟩
  refine ⟨[.a], rfl, replicate k₂ .b ++ ([.a] ++ replicate m₂ .b), ?_, by simp⟩
  refine ⟨replicate k₂ .b, mem_B0_replicate k₂, [.a] ++ replicate m₂ .b, ?_, by simp⟩
  exact ⟨[.a], rfl, replicate m₂ .b, mem_B0_replicate m₂, rfl⟩

/-- Split `w` into prefix before `i`, middle `[i,j)`, and suffix from `j`. -/
theorem take_drop_split_between (w : Word Letter) (i j : Nat)
    (hij : i ≤ j) (_hj : j ≤ w.length) :
    w = w.take i ++ (w.take j).drop i ++ w.drop j := by
  have htake : (w.take j).take i = w.take i := by
    simp [List.take_take, Nat.min_eq_left hij]
  calc
    w = w.take j ++ w.drop j := (List.take_append_drop j w).symm
    _ = w.take i ++ (w.take j).drop i ++ w.drop j := by
      congr 1
      calc
        w.take j = (w.take j).take i ++ (w.take j).drop i :=
          (List.take_append_drop i (w.take j)).symm
        _ = w.take i ++ (w.take j).drop i := by rw [htake]

theorem applyWord_take_add (w : Word Letter) (j t : Nat) (p : Fin 5) :
    applyWord (w.take (j + t)) p =
      applyWord ((w.drop j).take t) (applyWord (w.take j) p) := by
  rw [List.take_add, applyWord_append]

theorem denote_K2visit_subset_stab1 : denote K2visit ⊆ stab 1 := by
  intro w hw
  simp only [K2visit, denote, Language.concat, Language.letter] at hw
  rcases hw with
    ⟨u, hu, v, ⟨x, hx, y, ⟨r, hr, s, ⟨t, ht, z, ⟨q, hq, e, ⟨p, hp, f, hf, hpf⟩,
      hqe⟩, htz⟩, hrs⟩, hxy⟩, huv⟩
  have hx' : x = [Letter.a] := hx
  have ht' : t = [Letter.a] := ht
  have hp' : p = [Letter.a] := hp
  subst x; subst t; subst p
  have hw' : w = u ++ [Letter.a] ++ r ++ [Letter.a] ++ q ++ [Letter.a] ++ f := by
    simp [← huv, ← hxy, ← hrs, ← htz, ← hqe, ← hpf, List.append_assoc]
  have hu1 : applyWord u 1 = 1 := mem_B0_apply_at_1 u hu
  have hr2 : applyWord r 2 = 2 := mem_B0_apply_at_2 r hr
  have hq0 : applyWord q 0 = 0 := by
    have : q ∈ stab 0 := by simpa [denote_K1] using hq
    simpa [stab] using this
  have hf1 : applyWord f 1 = 1 := mem_B0_apply_at_1 f hf
  change applyWord w 1 = 1
  rw [hw']
  -- Path: 1 -u→ 1 -a→ 2 -r→ 2 -a→ 0 -q→ 0 -a→ 1 -f→ 1
  simp only [List.append_assoc]
  -- w-form becomes u ++ (a :: (r ++ (a :: (q ++ (a :: f)))))
  rw [applyWord_append, hu1]
  change applyWord (Letter.a :: (r ++ (Letter.a :: (q ++ (Letter.a :: f))))) 1 = 1
  have h12 : letterPerm Letter.a 1 = 2 := by decide
  simp only [applyWord, h12]
  rw [applyWord_append, hr2]
  change applyWord (Letter.a :: (q ++ (Letter.a :: f))) 2 = 1
  have h20 : letterPerm Letter.a 2 = 0 := by decide
  simp only [applyWord, h20]
  rw [applyWord_append, hq0]
  change applyWord (Letter.a :: f) 0 = 1
  have h01 : letterPerm Letter.a 0 = 1 := by decide
  simp only [applyWord, h01, hf1]

theorem denote_K3visit_subset_stab2 : denote K3visit ⊆ stab 2 := by
  intro w hw
  simp only [K3visit, denote, Language.concat, Language.letter] at hw
  rcases hw with
    ⟨u, hu, v, ⟨x, hx, y, ⟨q, hq, s, ⟨t, ht, z, ⟨r, hr, e, ⟨p, hp, f, hf, hpf⟩,
      hre⟩, htz⟩, hqs⟩, hxy⟩, huv⟩
  have hx' : x = [Letter.a] := hx
  have ht' : t = [Letter.a] := ht
  have hp' : p = [Letter.a] := hp
  subst x; subst t; subst p
  have hw' : w = u ++ [Letter.a] ++ q ++ [Letter.a] ++ r ++ [Letter.a] ++ f := by
    simp [← huv, ← hxy, ← hqs, ← htz, ← hre, ← hpf, List.append_assoc]
  have hu2 : applyWord u 2 = 2 := mem_B0_apply_at_2 u hu
  have hq0 : applyWord q 0 = 0 := by
    have : q ∈ stab 0 := by simpa [denote_K1] using hq
    simpa [stab] using this
  have hr1 : applyWord r 1 = 1 := mem_B0_apply_at_1 r hr
  have hf2 : applyWord f 2 = 2 := mem_B0_apply_at_2 f hf
  change applyWord w 2 = 2
  rw [hw']
  simp only [List.append_assoc]
  rw [applyWord_append, hu2]
  change applyWord (Letter.a :: (q ++ (Letter.a :: (r ++ (Letter.a :: f))))) 2 = 2
  have h20 : letterPerm Letter.a 2 = 0 := by decide
  simp only [applyWord, h20]
  rw [applyWord_append, hq0]
  change applyWord (Letter.a :: (r ++ (Letter.a :: f))) 0 = 2
  have h01 : letterPerm Letter.a 0 = 1 := by decide
  simp only [applyWord, h01]
  rw [applyWord_append, hr1]
  change applyWord (Letter.a :: f) 1 = 2
  have h12 : letterPerm Letter.a 1 = 2 := by decide
  simp only [applyWord, h12, hf2]

-- BLUEPRINT: N-A5-GEN145-004
theorem denote_K2 : denote K2 = stab 1 := by
  ext w
  constructor
  · intro hw
    simp only [K2, denote, Set.mem_union] at hw
    rcases hw with h | h
    · exact mem_B0_apply_at_1 w h
    · exact denote_K2visit_subset_stab1 h
  · intro hw
    change applyWord w 1 = 1 at hw
    by_cases hhit : ∃ k, 0 < k ∧ k ≤ w.length ∧ applyWord (w.take k) 1 = 0
    · obtain ⟨u, rest, une, huv, uret, ufirst⟩ := exists_first_hit_0_prefix 1 w hhit
      obtain ⟨k₁, m₁, huform⟩ := classify_first_hit_from_1 u uret ufirst
      have hi : u.length ≤ w.length := by
        have := congrArg List.length huv
        simp at this; omega
      have htake_u : w.take u.length = u := by
        simpa [← huv] using (List.take_left (l₁ := u) (l₂ := rest))
      have ui0 : applyWord (w.take u.length) 1 = 0 := by simpa [htake_u] using uret
      obtain ⟨j, hij, hjle, hj0, hjmax⟩ :=
        exists_last_hit_0_after 1 w u.length hi ui0
      have hw_split := take_drop_split_between w u.length j hij hjle
      set mid : Word Letter := (w.take j).drop u.length
      set suf : Word Letter := w.drop j
      have hw_parts : w = u ++ mid ++ suf := by
        simpa [htake_u, mid, suf] using hw_split
      have hmid0 : applyWord mid 0 = 0 := by
        have htj : w.take j = u ++ mid := by
          have hsplitj := List.take_append_drop u.length (w.take j)
          have hiu : (w.take j).take u.length = u := by
            simp [List.take_take, Nat.min_eq_left hij, htake_u]
          calc
            w.take j = (w.take j).take u.length ++ (w.take j).drop u.length :=
              hsplitj.symm
            _ = u ++ mid := by rw [hiu]
        have huj : applyWord (u ++ mid) 1 = 0 := by simpa [htj] using hj0
        simpa [applyWord_append, uret] using huj
      have hmidK : mid ∈ denote K1 := by
        simpa [denote_K1, stab] using hmid0
      have hsuf1 : applyWord suf 0 = 1 := by
        have : applyWord (w.take j ++ suf) 1 = 1 := by
          simpa [List.take_append_drop, suf] using hw
        simpa [applyWord_append, hj0] using this
      have hsuf_never :
          ∀ t, 0 < t → t ≤ suf.length → applyWord (suf.take t) 0 ≠ 0 := by
        intro t htpos htle hret
        have hlen : j + t ≤ w.length := by
          simp only [suf, List.length_drop] at htle
          omega
        have h := hjmax (j + t) (by omega) hlen
        have happly :
            applyWord (w.take (j + t)) 1 =
              applyWord ((w.drop j).take t) 0 := by
          rw [applyWord_take_add, hj0]
        exact h (by simpa [suf] using happly.trans hret)
      obtain ⟨k₂, hsuf⟩ := classify_exit_0_to_1 suf hsuf1 hsuf_never
      have hw_form :
          w =
            replicate k₁ Letter.b ++ [Letter.a] ++ replicate m₁ Letter.b ++
              [Letter.a] ++ mid ++ [Letter.a] ++ replicate k₂ Letter.b := by
        simp [hw_parts, huform, hsuf, List.append_assoc]
      refine Or.inr ?_
      simpa [hw_form] using mem_K2visit_of_parts k₁ m₁ mid k₂ hmidK
    · refine Or.inl ?_
      exact stab1_never_hit_0_mem_B0 w hw fun k hkpos hkle h =>
        hhit ⟨k, hkpos, hkle, h⟩

-- BLUEPRINT: N-A5-GEN145-005
theorem denote_K3 : denote K3 = stab 2 := by
  ext w
  constructor
  · intro hw
    simp only [K3, denote, Set.mem_union] at hw
    rcases hw with h | h
    · exact mem_B0_apply_at_2 w h
    · exact denote_K3visit_subset_stab2 h
  · intro hw
    change applyWord w 2 = 2 at hw
    by_cases hhit : ∃ k, 0 < k ∧ k ≤ w.length ∧ applyWord (w.take k) 2 = 0
    · obtain ⟨u, rest, une, huv, uret, ufirst⟩ := exists_first_hit_0_prefix 2 w hhit
      obtain ⟨k₁, huform⟩ := classify_first_hit_from_2 u uret ufirst
      have hi : u.length ≤ w.length := by
        have := congrArg List.length huv
        simp at this; omega
      have htake_u : w.take u.length = u := by
        simpa [← huv] using (List.take_left (l₁ := u) (l₂ := rest))
      have ui0 : applyWord (w.take u.length) 2 = 0 := by simpa [htake_u] using uret
      obtain ⟨j, hij, hjle, hj0, hjmax⟩ :=
        exists_last_hit_0_after 2 w u.length hi ui0
      have hw_split := take_drop_split_between w u.length j hij hjle
      set mid : Word Letter := (w.take j).drop u.length
      set suf : Word Letter := w.drop j
      have hw_parts : w = u ++ mid ++ suf := by
        simpa [htake_u, mid, suf] using hw_split
      have hmid0 : applyWord mid 0 = 0 := by
        have htj : w.take j = u ++ mid := by
          have hsplitj := List.take_append_drop u.length (w.take j)
          have hiu : (w.take j).take u.length = u := by
            simp [List.take_take, Nat.min_eq_left hij, htake_u]
          calc
            w.take j = (w.take j).take u.length ++ (w.take j).drop u.length :=
              hsplitj.symm
            _ = u ++ mid := by rw [hiu]
        have huj : applyWord (u ++ mid) 2 = 0 := by simpa [htj] using hj0
        simpa [applyWord_append, uret] using huj
      have hmidK : mid ∈ denote K1 := by
        simpa [denote_K1, stab] using hmid0
      have hsuf2 : applyWord suf 0 = 2 := by
        have : applyWord (w.take j ++ suf) 2 = 2 := by
          simpa [List.take_append_drop, suf] using hw
        simpa [applyWord_append, hj0] using this
      have hsuf_never :
          ∀ t, 0 < t → t ≤ suf.length → applyWord (suf.take t) 0 ≠ 0 := by
        intro t htpos htle hret
        have hlen : j + t ≤ w.length := by
          simp only [suf, List.length_drop] at htle
          omega
        have h := hjmax (j + t) (by omega) hlen
        have happly :
            applyWord (w.take (j + t)) 2 =
              applyWord ((w.drop j).take t) 0 := by
          rw [applyWord_take_add, hj0]
        exact h (by simpa [suf] using happly.trans hret)
      obtain ⟨k₂, m₂, hsuf⟩ := classify_exit_0_to_2 suf hsuf2 hsuf_never
      have hw_form :
          w =
            replicate k₁ Letter.b ++ [Letter.a] ++ mid ++ [Letter.a] ++
              replicate k₂ Letter.b ++ [Letter.a] ++ replicate m₂ Letter.b := by
        simp [hw_parts, huform, hsuf, List.append_assoc]
      refine Or.inr ?_
      simpa [hw_form] using mem_K3visit_of_parts k₁ mid k₂ m₂ hmidK
    · refine Or.inl ?_
      exact stab2_never_hit_0_mem_B0 w hw fun k hkpos hkle h =>
        hhit ⟨k, hkpos, hkle, h⟩


theorem denote_certificate :
    denote certificate = stab 0 ∩ stab 1 ∩ stab 2 := by
  simp only [certificate, denote_inter, denote_K1, denote_K2, denote_K3]
  rw [Set.inter_assoc]

theorem certificate_denotes_wordProblem :
    denote certificate = wordProblem := by
  rw [denote_certificate, wordProblem_eq_stab012]

theorem wordProblem_hasHeightAtMost_one :
    HasHeightAtMost wordProblem 1 :=
  ⟨certificate, certificate_denotes_wordProblem, starHeight_certificate⟩

end A5Gen145
end GSH
