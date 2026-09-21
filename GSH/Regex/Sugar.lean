import GSH.Challenges.GeneralizedStarHeight

/-!
# Sugar constructors for generalized expressions

Boolean intersection and the universe language are derived from complement and
union, so they do not raise syntactic star height.  These are the De Morgan
forms used by the explicit height-one certificates in `RESULTS.md`.
-/

set_option autoImplicit false

namespace GSH
namespace GRegex

universe u

variable {α : Type u}

/-- The full free monoid `α*`, written without Kleene star as `compl ∅`. -/
def univ : GRegex α := compl zero

/-- Intersection via De Morgan: `compl (compl r ∪ compl s)`. -/
def inter (r s : GRegex α) : GRegex α :=
  compl (union (compl r) (compl s))

@[simp] theorem starHeight_univ : starHeight (univ : GRegex α) = 0 := rfl

@[simp] theorem starHeight_inter (r s : GRegex α) :
    starHeight (inter r s) = max (starHeight r) (starHeight s) := rfl

@[simp] theorem denote_univ : denote (univ : GRegex α) = Set.univ := by
  ext w
  simp [denote, univ, Language.compl, Language.empty]

theorem denote_inter (r s : GRegex α) :
    denote (inter r s) = denote r ∩ denote s := by
  ext w
  simp [denote, inter, Language.compl]

/-- Three-fold concatenation `r · s · t`. -/
def concat3 (r s t : GRegex α) : GRegex α :=
  concat r (concat s t)

/-- Five-fold concatenation. -/
def concat5 (r₁ r₂ r₃ r₄ r₅ : GRegex α) : GRegex α :=
  concat r₁ (concat r₂ (concat r₃ (concat r₄ r₅)))

@[simp] theorem starHeight_concat3 (r s t : GRegex α) :
    starHeight (concat3 r s t) =
      max (starHeight r) (max (starHeight s) (starHeight t)) := by
  simp [concat3, starHeight]

@[simp] theorem starHeight_concat5 (r₁ r₂ r₃ r₄ r₅ : GRegex α) :
    starHeight (concat5 r₁ r₂ r₃ r₄ r₅) =
      max (starHeight r₁)
        (max (starHeight r₂)
          (max (starHeight r₃) (max (starHeight r₄) (starHeight r₅)))) := by
  simp [concat5, starHeight]

end GRegex
end GSH
