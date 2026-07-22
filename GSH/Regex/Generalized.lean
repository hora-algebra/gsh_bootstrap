import GSH.Language.Basic

/-!
# Generalized regular expressions

Complement is a primitive constructor.  `starHeight` measures syntax-tree
nesting.  `HasHeightAtMost L n` is semantic: it existentially quantifies over
all equivalent expressions.
-/

set_option autoImplicit false

namespace GSH

universe u

inductive GRegex (α : Type u) where
  | zero : GRegex α
  | epsilon : GRegex α
  | atom : α → GRegex α
  | union : GRegex α → GRegex α → GRegex α
  | concat : GRegex α → GRegex α → GRegex α
  | compl : GRegex α → GRegex α
  | star : GRegex α → GRegex α
  deriving Repr

namespace GRegex

variable {α : Type u}

/-- Denotational semantics over finite words. -/
def denote : GRegex α → Language α
  | zero => Language.empty
  | epsilon => Language.epsilon
  | atom a => Language.letter a
  | union r s => denote r ∪ denote s
  | concat r s => Language.concat (denote r) (denote s)
  | compl r => Language.compl (denote r)
  | star r => Language.star (denote r)

/-- Maximum nesting depth of the Kleene-star constructor. -/
def starHeight : GRegex α → Nat
  | zero | epsilon | atom _ => 0
  | union r s | concat r s => max (starHeight r) (starHeight s)
  | compl r => starHeight r
  | star r => starHeight r + 1

@[simp] theorem starHeight_zero : starHeight (zero : GRegex α) = 0 := rfl
@[simp] theorem starHeight_epsilon : starHeight (epsilon : GRegex α) = 0 := rfl
@[simp] theorem starHeight_atom (a : α) : starHeight (atom a) = 0 := rfl
@[simp] theorem starHeight_compl (r : GRegex α) :
    starHeight (compl r) = starHeight r := rfl
@[simp] theorem starHeight_star (r : GRegex α) :
    starHeight (star r) = starHeight r + 1 := rfl

end GRegex

/-- A semantic upper bound on generalized star height. -/
def HasHeightAtMost {α : Type u} (L : Language α) (n : Nat) : Prop :=
  ∃ r : GRegex α, GRegex.denote r = L ∧ GRegex.starHeight r ≤ n

/-- Regularity expressed through generalized regular expressions. -/
def IsRegular {α : Type u} (L : Language α) : Prop :=
  ∃ r : GRegex α, GRegex.denote r = L

/-- Star-free means generalized height at most zero. -/
def IsStarFree {α : Type u} (L : Language α) : Prop :=
  HasHeightAtMost L 0

/-- The height-one collapse statement for one alphabet. -/
def HeightOneCollapse (α : Type u) : Prop :=
  ∀ L : Language α, IsRegular L → HasHeightAtMost L 1

end GSH
