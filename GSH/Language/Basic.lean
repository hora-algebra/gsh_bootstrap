import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Basic

/-!
# Words and languages

The project uses `List α` as the free monoid of words and `Set (List α)` as
languages.  Complement is therefore always relative to the full `α*`.
-/

set_option autoImplicit false

namespace GSH

universe u

abbrev Word (α : Type u) := List α
abbrev Language (α : Type u) := Set (Word α)

namespace Language

variable {α : Type u}

/-- The empty language. -/
def empty : Language α := ∅

/-- The language containing only the empty word. -/
def epsilon : Language α := {[]}

/-- The singleton one-letter language. -/
def letter (a : α) : Language α := {[a]}

/-- Boolean complement inside the full free monoid `List α`. -/
def compl (L : Language α) : Language α := Lᶜ

/-- Language concatenation. -/
def concat (L K : Language α) : Language α :=
  {w | ∃ u ∈ L, ∃ v ∈ K, u ++ v = w}

/-- The `n`-fold concatenation power, with zeroth power `{ε}`. -/
def power (L : Language α) : Nat → Language α
  | 0 => epsilon
  | n + 1 => concat (power L n) L

/-- Kleene star as the union of all finite powers. -/
def star (L : Language α) : Language α :=
  {w | ∃ n : Nat, w ∈ power L n}

@[simp] theorem mem_empty (w : Word α) : w ∉ (empty : Language α) := by
  simp [empty]

@[simp] theorem mem_epsilon_iff (w : Word α) : w ∈ (epsilon : Language α) ↔ w = [] := by
  simp [epsilon]

@[simp] theorem mem_letter_iff (a : α) (w : Word α) : w ∈ letter a ↔ w = [a] := by
  simp [letter]

@[simp] theorem mem_compl_iff (L : Language α) (w : Word α) :
    w ∈ compl L ↔ w ∉ L := by
  rfl

@[simp] theorem mem_concat_iff (L K : Language α) (w : Word α) :
    w ∈ concat L K ↔ ∃ u ∈ L, ∃ v ∈ K, u ++ v = w := by
  rfl

@[simp] theorem power_zero (L : Language α) : power L 0 = epsilon := by
  rfl

@[simp] theorem power_succ (L : Language α) (n : Nat) :
    power L (n + 1) = concat (power L n) L := by
  rfl

@[simp] theorem mem_star_iff (L : Language α) (w : Word α) :
    w ∈ star L ↔ ∃ n : Nat, w ∈ power L n := by
  rfl

end Language
end GSH
