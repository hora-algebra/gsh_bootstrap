import GSH.Regex.HeightClosure
import GSH.Regex.Sugar

/-!
# Height ≤ 1 for modular letter-set counts

For a finite list `S`, `{ w | countSet S w ≡ r (mod 3) }` has generalized
star height ≤ 1.
-/

set_option autoImplicit false

namespace GSH
namespace CountHeight

open GRegex Language List

variable {α : Type*} [DecidableEq α]

/-! ## Letter-set avoiders and atoms -/

def atomsOf : List α → GRegex α
  | [] => zero
  | a :: S => union (atom a) (atomsOf S)

theorem starHeight_atomsOf : ∀ S : List α, starHeight (atomsOf S) = 0
  | [] => rfl
  | a :: S => by
    change max (starHeight (atom a)) (starHeight (atomsOf S)) = 0
    rw [starHeight_atom, starHeight_atomsOf S]; rfl

theorem denote_atomsOf :
    ∀ S : List α, denote (atomsOf S) = {w : Word α | ∃ a ∈ S, w = [a]}
  | [] => by
    ext w; simp [atomsOf, denote, Language.empty]
  | a :: S => by
    ext w
    constructor
    · intro hw
      simp only [atomsOf, denote, Set.mem_union, mem_letter_iff] at hw
      rcases hw with hw | hw
      · exact ⟨a, by simp, hw⟩
      · rw [denote_atomsOf S] at hw
        obtain ⟨b, hb, rfl⟩ := hw
        exact ⟨b, by simp [hb], rfl⟩
    · intro hw
      simp only [atomsOf, denote, Set.mem_union, mem_letter_iff]
      obtain ⟨b, hb, rfl⟩ := hw
      simp only [mem_cons] at hb
      rcases hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr ((denote_atomsOf S) ▸ ⟨b, hb, rfl⟩)

def hitsSet (S : List α) : GRegex α :=
  concat univ (concat (atomsOf S) univ)

theorem starHeight_hitsSet (S : List α) : starHeight (hitsSet S) = 0 := by
  change max (starHeight (univ : GRegex α))
      (max (starHeight (atomsOf S)) (starHeight (univ : GRegex α))) = 0
  rw [starHeight_univ, starHeight_atomsOf]; rfl

def avoidSet (S : List α) : GRegex α :=
  compl (hitsSet S)

theorem starHeight_avoidSet (S : List α) : starHeight (avoidSet S) = 0 := by
  simpa [avoidSet] using starHeight_hitsSet S

theorem denote_hitsSet (S : List α) :
    denote (hitsSet S) = {w : Word α | ∃ a ∈ S, a ∈ w} := by
  ext w
  constructor
  · intro hw
    simp only [hitsSet, denote, denote_univ, mem_concat_iff, Set.mem_univ, true_and] at hw
    obtain ⟨_u, rest, hrest, rfl⟩ := hw
    obtain ⟨mid, hmid, _v, _, rfl⟩ := hrest
    rw [denote_atomsOf] at hmid
    obtain ⟨a, ha, rfl⟩ := hmid
    exact ⟨a, ha, by simp⟩
  · intro hw
    obtain ⟨a, ha, hin⟩ := hw
    obtain ⟨u, v, rfl⟩ := List.mem_iff_append.1 hin
    refine (mem_concat_iff _ _ _).2 ⟨u, (by simp [denote_univ] : u ∈ denote univ), [a] ++ v, ?_, rfl⟩
    refine (mem_concat_iff _ _ _).2 ⟨[a], ?_, v, (by simp [denote_univ] : v ∈ denote univ), rfl⟩
    exact (denote_atomsOf S) ▸ ⟨a, ha, rfl⟩

theorem denote_avoidSet (S : List α) :
    denote (avoidSet S) = {w : Word α | ∀ a ∈ S, a ∉ w} := by
  ext w
  simp [avoidSet, denote, Language.compl, denote_hitsSet]

def countSet (S : List α) (w : Word α) : Nat :=
  (w.filter (· ∈ S)).length

theorem countSet_cons (S : List α) (x : α) (w : Word α) :
    countSet S (x :: w) = (if x ∈ S then 1 else 0) + countSet S w := by
  by_cases hx : x ∈ S <;> simp [countSet, hx, Nat.add_comm]

theorem countSet_append (S : List α) (u v : Word α) :
    countSet S (u ++ v) = countSet S u + countSet S v := by
  induction u with
  | nil => simp [countSet]
  | cons x xs ih => simp [countSet_cons, ih, Nat.add_assoc]

theorem countSet_eq_zero_iff (S : List α) (w : Word α) :
    countSet S w = 0 ↔ ∀ a ∈ S, a ∉ w := by
  induction w with
  | nil => simp [countSet]
  | cons x xs ih =>
    constructor
    · intro h a ha hxw
      have hxfalse : x ∉ S := by
        intro hx; simp [countSet_cons, hx] at h
      simp only [mem_cons] at hxw
      rcases hxw with rfl | hxw
      · exact hxfalse ha
      · have hxs : countSet S xs = 0 := by
          by_cases hx : x ∈ S
          · exact (hxfalse hx).elim
          · simpa [countSet_cons, hx] using h
        exact (ih.mp hxs) a ha hxw
    · intro h
      by_cases hx : x ∈ S
      · exact absurd (show x ∈ x :: xs from by simp) (h x hx)
      · simp [countSet_cons, hx]
        exact ih.mpr fun a ha hx' => h a ha (List.mem_cons_of_mem x hx')

theorem mem_avoidSet_iff_countSet (S : List α) {w : Word α} :
    w ∈ denote (avoidSet S) ↔ countSet S w = 0 := by
  constructor
  · intro h
    rw [denote_avoidSet] at h
    exact (countSet_eq_zero_iff S w).2 h
  · intro h
    rw [denote_avoidSet]
    exact (countSet_eq_zero_iff S w).1 h

/-! ## One-hit token and left-associated powers -/

def oneHit (S : List α) : GRegex α :=
  concat3 (avoidSet S) (atomsOf S) (avoidSet S)

theorem starHeight_oneHit (S : List α) : starHeight (oneHit S) = 0 := by
  change max (starHeight (avoidSet S))
      (max (starHeight (atomsOf S)) (starHeight (avoidSet S))) = 0
  rw [starHeight_avoidSet, starHeight_atomsOf]; rfl

theorem denote_oneHit (S : List α) :
    denote (oneHit S) =
      {w | ∃ u v a, a ∈ S ∧ w = u ++ a :: v ∧ countSet S u = 0 ∧ countSet S v = 0} := by
  ext w
  constructor
  · intro hw
    simp only [oneHit, concat3, denote, mem_concat_iff] at hw
    obtain ⟨u, hu, rest, hrest, rfl⟩ := hw
    obtain ⟨mid, hmid, v, hv, rfl⟩ := hrest
    rw [denote_atomsOf] at hmid
    obtain ⟨a, ha, rfl⟩ := hmid
    exact ⟨u, v, a, ha, rfl,
      (mem_avoidSet_iff_countSet S).1 hu, (mem_avoidSet_iff_countSet S).1 hv⟩
  · rintro ⟨u, v, a, ha, rfl, hu, hv⟩
    refine (mem_concat_iff _ _ _).2
      ⟨u, (mem_avoidSet_iff_countSet S).2 hu, a :: v, ?_, rfl⟩
    refine (mem_concat_iff _ _ _).2
      ⟨[a], (denote_atomsOf S) ▸ ⟨a, ha, rfl⟩, v, (mem_avoidSet_iff_countSet S).2 hv, rfl⟩

theorem countSet_of_mem_oneHit (S : List α) {w : Word α}
    (hw : w ∈ denote (oneHit S)) : countSet S w = 1 := by
  rw [denote_oneHit] at hw
  obtain ⟨u, v, a, ha, rfl, hu, hv⟩ := hw
  simp [countSet_append, countSet_cons, ha, hu, hv]

def hitsPower (S : List α) : Nat → Language α
  | 0 => Language.epsilon
  | n + 1 => Language.concat (denote (oneHit S)) (hitsPower S n)

theorem hitsPower_one (S : List α) :
    hitsPower S 1 = denote (oneHit S) := by
  ext w
  simp only [hitsPower, mem_concat_iff, mem_epsilon_iff]
  constructor
  · rintro ⟨u, hu, v, rfl, rfl⟩; simpa using hu
  · intro hw; exact ⟨w, hw, [], rfl, by simp⟩

theorem countSet_of_mem_hitsPower (S : List α) :
    ∀ n w, w ∈ hitsPower S n → countSet S w = n
  | 0, w, hw => by
    simp only [hitsPower, mem_epsilon_iff] at hw; simp [hw, countSet]
  | n + 1, w, hw => by
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_concat_iff _ _ _).1 hw
    rw [countSet_append, countSet_of_mem_oneHit S hu, countSet_of_mem_hitsPower S n v hv,
      Nat.add_comm]

theorem exists_oneHit_prefix (S : List α) {w : Word α} (hpos : 0 < countSet S w) :
    ∃ u v, w = u ++ v ∧ u ∈ denote (oneHit S) ∧ countSet S v = countSet S w - 1 := by
  induction w with
  | nil => simp [countSet] at hpos
  | cons x xs ih =>
    by_cases hx : x ∈ S
    · refine ⟨[x], xs, rfl, ?_, ?_⟩
      · rw [denote_oneHit]; exact ⟨[], [], x, hx, rfl, rfl, rfl⟩
      · simp [countSet_cons, hx]
    · have hxs : 0 < countSet S xs := by simpa [countSet_cons, hx] using hpos
      obtain ⟨u, v, rfl, hu, hv⟩ := ih hxs
      refine ⟨x :: u, v, by simp, ?_, ?_⟩
      · rw [denote_oneHit] at hu ⊢
        obtain ⟨u₀, v₀, a, ha, huEq, hu0, hv0⟩ := hu
        refine ⟨x :: u₀, v₀, a, ha, by simp [huEq], ?_, hv0⟩
        simp [countSet_cons, hx, hu0]
      · simpa [countSet_cons, hx] using hv

theorem exists_hitsPower_factor (S : List α) :
    ∀ n w, countSet S w = n →
      ∃ u v, w = u ++ v ∧ u ∈ hitsPower S n ∧ v ∈ denote (avoidSet S)
  | 0, w, hw =>
    ⟨[], w, rfl, rfl, (mem_avoidSet_iff_countSet S).2 hw⟩
  | n + 1, w, hw => by
    have hpos : 0 < countSet S w := by omega
    obtain ⟨u, rest, rfl, hu, hrest⟩ := exists_oneHit_prefix S hpos
    have : countSet S rest = n := by omega
    obtain ⟨p, q, rfl, hp, hq⟩ := exists_hitsPower_factor S n rest this
    exact ⟨u ++ p, q, by simp, ⟨u, hu, p, hp, rfl⟩, hq⟩

theorem mem_concat_hitsPower (S : List α) :
    ∀ m k w,
      w ∈ Language.concat (hitsPower S m) (hitsPower S k) ↔ w ∈ hitsPower S (m + k)
  | 0, k, w => by
    simp only [hitsPower, mem_concat_iff, mem_epsilon_iff, Nat.zero_add]
    constructor
    · rintro ⟨_, rfl, v, hv, rfl⟩; exact hv
    · intro hw; exact ⟨[], rfl, w, hw, rfl⟩
  | m + 1, k, w => by
    simp only [hitsPower, mem_concat_iff, Nat.succ_add]
    constructor
    · rintro ⟨_uv, ⟨u, hu, v, hv, rfl⟩, x, hx, rfl⟩
      refine ⟨u, hu, v ++ x, ?_, by simp⟩
      exact (mem_concat_hitsPower S m k (v ++ x)).1 ⟨v, hv, x, hx, rfl⟩
    · rintro ⟨u, hu, rest, hrest, rfl⟩
      obtain ⟨v, hv, x, hx, rfl⟩ := (mem_concat_hitsPower S m k rest).2 hrest
      exact ⟨u ++ v, ⟨u, hu, v, hv, rfl⟩, x, hx, by simp⟩

theorem mem_power_hitsPower (S : List α) (m n : Nat) {w : Word α} :
    w ∈ Language.power (hitsPower S m) n ↔ w ∈ hitsPower S (m * n) := by
  induction n generalizing w with
  | zero => simp [hitsPower, power_zero]
  | succ n ih =>
    simp only [power_succ, Nat.mul_succ]
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      exact (mem_concat_hitsPower S (m * n) m _).1 ⟨u, ih.1 hu, v, hv, rfl⟩
    · intro hw
      obtain ⟨u, hu, v, hv, rfl⟩ := (mem_concat_hitsPower S (m * n) m w).2 hw
      exact ⟨u, ih.2 hu, v, hv, rfl⟩

/-! ## Mod-3 count expressions -/

def threeHits (S : List α) : GRegex α :=
  concat3 (oneHit S) (oneHit S) (oneHit S)

theorem starHeight_threeHits (S : List α) : starHeight (threeHits S) = 0 := by
  change max (starHeight (oneHit S))
      (max (starHeight (oneHit S)) (starHeight (oneHit S))) = 0
  rw [starHeight_oneHit]; rfl

theorem denote_threeHits (S : List α) :
    denote (threeHits S) = hitsPower S 3 := by
  ext w
  constructor
  · intro hw
    simp only [threeHits, concat3, denote, mem_concat_iff] at hw
    obtain ⟨u, hu, rest, ⟨v, hv, x, hx, rfl⟩, rfl⟩ := hw
    refine (mem_concat_iff _ _ _).2 ⟨u, hu, v ++ x, ?_, rfl⟩
    refine (mem_concat_iff _ _ _).2 ⟨v, hv, x, ?_, rfl⟩
    exact (hitsPower_one S).symm ▸ hx
  · intro hw
    -- `hitsPower 3 = oneHit · (oneHit · hitsPower 1)`
    obtain ⟨u, hu, rest, hrest, rfl⟩ := (mem_concat_iff _ _ _).1 (show w ∈
        Language.concat (denote (oneHit S)) (hitsPower S 2) from hw)
    obtain ⟨v, hv, x, hx, rfl⟩ := (mem_concat_iff _ _ _).1
      (show rest ∈ Language.concat (denote (oneHit S)) (hitsPower S 1) from hrest)
    have hx' : x ∈ denote (oneHit S) := (hitsPower_one S) ▸ hx
    refine (mem_concat_iff _ _ _).2 ⟨u, hu, v ++ x, ⟨v, hv, x, hx', rfl⟩, rfl⟩

def countMod3Eq0 (S : List α) : GRegex α :=
  concat (star (threeHits S)) (avoidSet S)

def countMod3Eq1 (S : List α) : GRegex α :=
  concat (oneHit S) (countMod3Eq0 S)

def countMod3Eq2 (S : List α) : GRegex α :=
  concat (oneHit S) (countMod3Eq1 S)

theorem starHeight_countMod3Eq0 (S : List α) : starHeight (countMod3Eq0 S) ≤ 1 := by
  change max (starHeight (threeHits S) + 1) (starHeight (avoidSet S)) ≤ 1
  rw [starHeight_threeHits, starHeight_avoidSet]
  decide

theorem starHeight_countMod3Eq1 (S : List α) : starHeight (countMod3Eq1 S) ≤ 1 := by
  change max (starHeight (oneHit S)) (starHeight (countMod3Eq0 S)) ≤ 1
  rw [starHeight_oneHit]
  exact max_le (by decide) (starHeight_countMod3Eq0 S)

theorem starHeight_countMod3Eq2 (S : List α) : starHeight (countMod3Eq2 S) ≤ 1 := by
  change max (starHeight (oneHit S)) (starHeight (countMod3Eq1 S)) ≤ 1
  rw [starHeight_oneHit]
  exact max_le (by decide) (starHeight_countMod3Eq1 S)

theorem denote_countMod3Eq0 (S : List α) :
    denote (countMod3Eq0 S) = {w : Word α | countSet S w % 3 = 0} := by
  ext w
  simp only [countMod3Eq0, denote, mem_concat_iff, mem_star_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, ⟨n, hu⟩, v, hv, rfl⟩
    have hu' : u ∈ hitsPower S (3 * n) := by
      have : u ∈ Language.power (denote (threeHits S)) n := hu
      rw [denote_threeHits] at this
      exact (mem_power_hitsPower S 3 n).1 this
    have hc := countSet_of_mem_hitsPower S (3 * n) u hu'
    have hv' := (mem_avoidSet_iff_countSet S).1 hv
    simp [countSet_append, hc, hv']
  · intro hw
    let n := countSet S w / 3
    have hn : countSet S w = 3 * n := by
      have : countSet S w % 3 = 0 := hw
      omega
    obtain ⟨u, v, rfl, hu, hv⟩ := exists_hitsPower_factor S (3 * n) w hn
    refine ⟨u, ⟨n, ?_⟩, v, hv, rfl⟩
    have : u ∈ Language.power (hitsPower S 3) n := (mem_power_hitsPower S 3 n).2 hu
    rwa [← denote_threeHits] at this

theorem denote_countMod3Eq1 (S : List α) :
    denote (countMod3Eq1 S) = {w : Word α | countSet S w % 3 = 1} := by
  ext w
  simp only [countMod3Eq1, denote, mem_concat_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    have hu' := countSet_of_mem_oneHit S hu
    have hv' : countSet S v % 3 = 0 := by
      have := (denote_countMod3Eq0 S).symm ▸ hv
      simpa using this
    simp [countSet_append, hu']; omega
  · intro hw
    have hpos : 0 < countSet S w := by have : countSet S w % 3 = 1 := hw; omega
    obtain ⟨u, v, rfl, hu, hv⟩ := exists_oneHit_prefix S hpos
    refine ⟨u, hu, v, ?_, rfl⟩
    have : countSet S v % 3 = 0 := by omega
    exact (denote_countMod3Eq0 S) ▸ this

theorem denote_countMod3Eq2 (S : List α) :
    denote (countMod3Eq2 S) = {w : Word α | countSet S w % 3 = 2} := by
  ext w
  simp only [countMod3Eq2, denote, mem_concat_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    have hu' := countSet_of_mem_oneHit S hu
    have hv' : countSet S v % 3 = 1 := by
      have := (denote_countMod3Eq1 S).symm ▸ hv
      simpa using this
    simp [countSet_append, hu']; omega
  · intro hw
    have hpos : 0 < countSet S w := by have : countSet S w % 3 = 2 := hw; omega
    obtain ⟨u, v, rfl, hu, hv⟩ := exists_oneHit_prefix S hpos
    refine ⟨u, hu, v, ?_, rfl⟩
    have : countSet S v % 3 = 1 := by omega
    exact (denote_countMod3Eq1 S) ▸ this

theorem countMod3_hasHeightAtMost_one (S : List α) (r : Fin 3) :
    HasHeightAtMost {w : Word α | countSet S w % 3 = r.val} 1 := by
  match r with
  | ⟨0, _⟩ => exact ⟨countMod3Eq0 S, denote_countMod3Eq0 S, starHeight_countMod3Eq0 S⟩
  | ⟨1, _⟩ => exact ⟨countMod3Eq1 S, denote_countMod3Eq1 S, starHeight_countMod3Eq1 S⟩
  | ⟨2, _⟩ => exact ⟨countMod3Eq2 S, denote_countMod3Eq2 S, starHeight_countMod3Eq2 S⟩

/-! ## Mod-2 count expressions -/

/-- Two successive hits. -/
def twoHits (S : List α) : GRegex α :=
  concat (oneHit S) (oneHit S)

theorem starHeight_twoHits (S : List α) : starHeight (twoHits S) = 0 := by
  change max (starHeight (oneHit S)) (starHeight (oneHit S)) = 0
  rw [starHeight_oneHit]; rfl

theorem denote_twoHits (S : List α) :
    denote (twoHits S) = hitsPower S 2 := by
  ext w
  constructor
  · intro hw
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_concat_iff _ _ _).1
      (show w ∈ Language.concat (denote (oneHit S)) (denote (oneHit S)) from hw)
    exact (mem_concat_iff _ _ _).2 ⟨u, hu, v, (hitsPower_one S).symm ▸ hv, rfl⟩
  · intro hw
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_concat_iff _ _ _).1
      (show w ∈ Language.concat (denote (oneHit S)) (hitsPower S 1) from hw)
    exact (mem_concat_iff _ _ _).2 ⟨u, hu, v, (hitsPower_one S) ▸ hv, rfl⟩

/-- `{ countSet S ≡ 0 (mod 2) }`. -/
def countMod2Eq0 (S : List α) : GRegex α :=
  concat (star (twoHits S)) (avoidSet S)

/-- `{ countSet S ≡ 1 (mod 2) }`. -/
def countMod2Eq1 (S : List α) : GRegex α :=
  concat (oneHit S) (countMod2Eq0 S)

theorem starHeight_countMod2Eq0 (S : List α) : starHeight (countMod2Eq0 S) ≤ 1 := by
  change max (starHeight (twoHits S) + 1) (starHeight (avoidSet S)) ≤ 1
  rw [starHeight_twoHits, starHeight_avoidSet]
  decide

theorem starHeight_countMod2Eq1 (S : List α) : starHeight (countMod2Eq1 S) ≤ 1 := by
  change max (starHeight (oneHit S)) (starHeight (countMod2Eq0 S)) ≤ 1
  rw [starHeight_oneHit]
  exact max_le (by decide) (starHeight_countMod2Eq0 S)

theorem denote_countMod2Eq0 (S : List α) :
    denote (countMod2Eq0 S) = {w : Word α | countSet S w % 2 = 0} := by
  ext w
  simp only [countMod2Eq0, denote, mem_concat_iff, mem_star_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, ⟨n, hu⟩, v, hv, rfl⟩
    have hu' : u ∈ hitsPower S (2 * n) := by
      have : u ∈ Language.power (denote (twoHits S)) n := hu
      rw [denote_twoHits] at this
      exact (mem_power_hitsPower S 2 n).1 this
    have hc := countSet_of_mem_hitsPower S (2 * n) u hu'
    have hv' := (mem_avoidSet_iff_countSet S).1 hv
    simp [countSet_append, hc, hv']
  · intro hw
    let n := countSet S w / 2
    have hn : countSet S w = 2 * n := by
      have : countSet S w % 2 = 0 := hw
      omega
    obtain ⟨u, v, rfl, hu, hv⟩ := exists_hitsPower_factor S (2 * n) w hn
    refine ⟨u, ⟨n, ?_⟩, v, hv, rfl⟩
    have : u ∈ Language.power (hitsPower S 2) n := (mem_power_hitsPower S 2 n).2 hu
    rwa [← denote_twoHits] at this

theorem denote_countMod2Eq1 (S : List α) :
    denote (countMod2Eq1 S) = {w : Word α | countSet S w % 2 = 1} := by
  ext w
  simp only [countMod2Eq1, denote, mem_concat_iff, denote_countMod2Eq0, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    have hu' := countSet_of_mem_oneHit S hu
    simp [countSet_append, hu']; omega
  · intro hw
    have hpos : 0 < countSet S w := by have : countSet S w % 2 = 1 := hw; omega
    obtain ⟨u, v, rfl, hu, hv⟩ := exists_oneHit_prefix S hpos
    refine ⟨u, hu, v, ?_, rfl⟩
    show countSet S v % 2 = 0
    omega

theorem countMod2_hasHeightAtMost_one (S : List α) (r : Fin 2) :
    HasHeightAtMost {w : Word α | countSet S w % 2 = r.val} 1 := by
  match r with
  | ⟨0, _⟩ => exact ⟨countMod2Eq0 S, denote_countMod2Eq0 S, starHeight_countMod2Eq0 S⟩
  | ⟨1, _⟩ => exact ⟨countMod2Eq1 S, denote_countMod2Eq1 S, starHeight_countMod2Eq1 S⟩

/-! ## Single-letter even count

`evenCount` is now derived from the letter-set machinery with `S = [a]`
(definition change from the earlier `oneA`-based star recorded in
`PROOF_OBLIGATIONS.md` under `N-A4-FULL-020`; the target language is
unchanged). -/

theorem count_eq_countSet_singleton (a : α) (w : Word α) :
    w.count a = countSet [a] w := by
  induction w with
  | nil => simp [countSet]
  | cons x xs ih =>
    by_cases hx : x = a
    · subst hx
      simp [List.count_cons, countSet_cons, ih, Nat.add_comm]
    · simp [List.count_cons, hx, countSet_cons, ih]

/-- Even count of a single letter. -/
def evenCount (a : α) : GRegex α := countMod2Eq0 [a]

theorem starHeight_evenCount (a : α) : starHeight (evenCount a) ≤ 1 :=
  starHeight_countMod2Eq0 [a]

-- N-A4-FULL-020 (closed)
theorem denote_evenCount (a : α) :
    denote (evenCount a) = {w : Word α | w.count a % 2 = 0} := by
  rw [evenCount, denote_countMod2Eq0]
  ext w
  simp [count_eq_countSet_singleton]

theorem evenCount_hasHeightAtMost_one (a : α) :
    HasHeightAtMost {w : Word α | w.count a % 2 = 0} 1 :=
  ⟨evenCount a, denote_evenCount a, starHeight_evenCount a⟩

end CountHeight
end GSH
